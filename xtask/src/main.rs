#[macro_use]
extern crate lazy_static;

use clap::{ArgAction, Parser, Subcommand};
use cargo_metadata::{MetadataCommand};
use cargo_toml::{Manifest, Dependency};
use std::{
  collections::HashSet, env, fs::{self, File}, io::{Read, Write}, path::{self, Path, PathBuf}, process::{Command, Stdio}
};
use memoize::memoize;
use git2::Repository;

fn locate_from_path<P>(binary: &P) -> Option<PathBuf>
where
  P: AsRef<Path>,
{
  env::var_os("PATH").and_then(|paths| {
    env::split_paths(&paths)
      .filter_map(|dir| {
        let full_path = dir.join(&binary);
        if full_path.is_file() {
          Some(full_path)
        } else {
          None
        }
      })
      .next()
  })
}

fn locate_from_hints<PB, PH>(binary: &PB, hints: &[PH]) -> Option<PathBuf>
where
  PB: AsRef<Path>,
  PH: AsRef<Path>,
{
  hints.iter().filter_map(|hint| {
    let full_path = hint.as_ref().join(binary);
    if full_path.is_file() {
      Some(full_path)
    } else {
      None
    }
  }).next()
}


fn locate_from_env<P>(
  binary: &P,
  env_var: &str,
) -> Option<PathBuf>
where
  P: AsRef<Path>,
{
  env::var_os(env_var).and_then(|path| {
    let full_path = PathBuf::from(path);
    if full_path.is_file() {
      return Some(full_path);
    }
    let full_path = full_path.join(&binary);
    if full_path.is_file() {
      return Some(full_path);
    }
    None
  })
}

fn absolutize(path: &Path) -> PathBuf {
  if path.is_absolute() {
    return path.to_path_buf();
  }
  let mut abs = env::current_dir().unwrap();
  abs.push(path);
  abs
}

fn locate<PB, PH>(
  binary: PB,
  env_var: Option<&str>,
  hints: Vec<PH>,
) -> Option<PathBuf>
where
  PB: AsRef<Path>,
  PH: AsRef<Path>,
{
  let path = env_var.and_then(
    |env_var| locate_from_env(&binary, env_var)
  ).or_else(
    || locate_from_hints(&binary, &hints)
  ).or_else(
    || locate_from_path(&binary)
  );

  path.and_then(
    |path| {
      Some(absolutize(&path))
    }
  )
}

#[memoize]
fn get_verus() -> PathBuf {
  let hints = vec![PathBuf::from("tools/verus/source/target-verus/release")];
  #[cfg(target_os = "windows")]
  let verus = "verus.exe";
  #[cfg(not(target_os = "windows"))]
  let verus = "verus";
  
  locate(verus, Some("VERUS_PATH"), hints)
    .unwrap_or_else(|| {
      eprintln!("Cannot find the Verus binary, please set the VERUS_PATH environment variable or add it to your PATH");
      std::process::exit(1);
    })
}

fn get_z3() -> PathBuf {
  let hints = vec![PathBuf::from("tools/verus/source")];
  #[cfg(target_os = "windows")]
  let z3 = "z3.exe";
  #[cfg(not(target_os = "windows"))]
  let z3 = "z3";

  locate(z3, Some("VERUS_Z3_PATH"), hints)
    .unwrap_or_else(|| {
      eprintln!("Cannot find the Z3 binary, please set the VERUS_Z3_PATH environment variable or add it to your PATH");
      std::process::exit(1);
    })
}

fn cargo_install(name: &str) {
  Command::new("cargo")
    .arg("install")
    .arg(name)
    .status()
    .expect("Failed to install cargo package");
}

#[memoize]
fn get_rustfilt() -> PathBuf {
  #[cfg(target_os = "windows")]
  let rustfilt_name = "rustfilt.exe";
  #[cfg(not(target_os = "windows"))]
  let rustfilt_name = "rustfilt";
  
  let rustfilt = locate(rustfilt_name, None, Vec::<PathBuf>::new());
  if rustfilt.is_none() {
    cargo_install("rustfilt");
  }
  locate(rustfilt_name, None, Vec::<PathBuf>::new())
    .expect("Failed to find or install rustfilt")
}

#[memoize]
fn get_objdump() -> PathBuf {
  if std::env::var("LLVM_OBJDUMP").is_ok() {
    return PathBuf::from(std::env::var("LLVM_OBJDUMP").unwrap());
  }
  let objdump = locate("llvm-objdump", None, Vec::<PathBuf>::new());
  if objdump.is_none() {
    cargo_install("cargo-binutils");
  }
  locate("llvm-objdump", None, Vec::<PathBuf>::new())
    .expect("Failed to find or install llvm-objdump, please specify `LLVM_OBJDUMP` as the path to the executable")
}

#[memoize]
fn get_all_targets() -> HashSet<String> {
  let metadata = MetadataCommand::new()
    .no_deps()
    .exec()
    .expect("Failed to get cargo metadata");

  metadata.workspace_members
  .into_iter()
  .map(|id| {
    metadata.packages
    .iter()
    .find(|pkg| pkg.id == id)
    .expect("Failed to find package")
    .name
    .clone()
  })
  .collect()
}

#[derive(Parser, Debug)]
#[command(
  name = "cli",
  author = "Hao",
  version = "0.1.0",
  about = "A tool to manage the formal verification targets"
)]
struct Cli {
  #[command(subcommand)]
  command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
  Verify(VerifyArgs),
  Doc(DocArgs),
  Bootstrap(BootstrapArgs),
  Compile(CompileArgs),
}

#[derive(Parser, Debug)]
struct BootstrapArgs {
  #[arg(long = "no-vscode-extension", help = "Do not build verus vscode extension",
        default_value = "false", action = ArgAction::SetTrue)]
  no_vscode_extension: bool,

  #[arg(long = "restart", help = "Remove all toolchain and restart the bootstrap",
        default_value = "false", action = ArgAction::SetTrue)]
  restart: bool,
}


#[derive(Parser, Debug)]
struct VerifyArgs {
  #[arg(short = 't', long = "targets", value_parser = target_parser,
        help = "The targets to verify", num_args = 0..,
        action = ArgAction::Append)]
  targets: Vec<String>,

  #[arg(short = 'e', long = "max-errors",
    help = "The maximum number of errors to display",
    default_value = "5", action = ArgAction::Set)]
  max_errors: usize,

  #[arg(short = 'i', long = "import", value_parser = target_parser,
    help = "Import verified local crates (they need to be compiled first)",
    num_args = 0.., action = ArgAction::Append)]
  imports: Vec<String>,

  #[arg(short = 'l', long = "log",
    help = "Log the verification process",
    default_value = "false", action = ArgAction::SetTrue)]
  log: bool,

  #[arg(last = true, help = "Pass-through arguments to the Verus verifier",
    allow_hyphen_values = true)]
  pass_through: Vec<String>,
}

#[derive(Parser, Debug)]
struct DocArgs {
  #[arg(short = 't', long = "targets", value_parser = target_parser,
        help = "The targets to generate document", num_args = 0..,
        action = ArgAction::Append)]
  targets: Vec<String>,
}

#[derive(Parser, Debug)]
struct CompileArgs {
  #[arg(short = 't', long = "targets", value_parser = target_parser,
        help = "The targets to compile", num_args = 0..,
        action = ArgAction::Append)]
  targets: Vec<String>,

  #[arg(short = 'i', long = "import", value_parser = target_parser,
    help = "Import verified local crates (they need to be compiled first)",
    num_args = 0.., action = ArgAction::Append)]
  imports: Vec<String>,

  #[arg(short = 'l', long = "log",
    help = "Log the verification process",
    default_value = "false", action = ArgAction::SetTrue)]
  log: bool,

  #[arg(short = 'o', long = "release", default_value = "false",
        help = "Build artifacts in release mode",
        action = ArgAction::SetTrue)]
  release: bool,

  #[arg(short = 'd', long = "no-disasm", default_value = "false",
        help = "Do not disassemble the compiled binary",
        action = ArgAction::SetTrue)]
  no_disasm: bool,

  #[arg(last = true, help = "Pass-through arguments to the Verus verifier",
    allow_hyphen_values = true)]
  pass_through: Vec<String>,
}

fn target_parser(s: &str) -> Result<String, String> {
  let all_targets = get_all_targets();
  let s = s.trim_start_matches(".\\").trim_end_matches(path::MAIN_SEPARATOR);
  if all_targets.contains(s) {
    Ok(s.to_string())
  } else {
    Err(format!("Unknown target: {}", s))
  }
}

type DynError = Box<dyn std::error::Error>;

fn crate_type(target: &str) -> (PathBuf, &str) {
  let target_root = Path::new(&target).join("src");
  if target_root.join("lib.rs").is_file() {
    (target_root.join("lib.rs"), "lib")
  } else {
    (target_root.join("main.rs"), "bin")
  }
}

fn binary_suffix(crate_type: &str) -> &str {
  match crate_type {
    "lib" => "rlib",
    "bin" => "",
    _ => panic!("Unknown crate type: {}", crate_type),
  }
}

fn binary_prefix(crate_type: &str) -> &str {
  match crate_type {
    "lib" => "lib",
    "bin" => "",
    _ => panic!("Unknown crate type: {}", crate_type),
  }
}

fn verus_data(target: &str) -> PathBuf {
  let target_verus = Path::new("target").join(format!("{}.verusdata", target));
  if target_verus.is_file() {
    target_verus
  } else {
    panic!("Cannot find the verus data file for target: {}", target);
  }
}

fn verus_library(target: &str) -> PathBuf {
  let (_, crate_type) = crate_type(target);
  let output = format!("{}{}.{}", 
    binary_prefix(crate_type),
    target,
    binary_suffix(crate_type));
  let target_library = Path::new("target").join(output);
  if target_library.is_file() {
    target_library
  } else {
    panic!("Cannot find the library file for target: {}", target);
  }
}

fn push_imports(cmd: &mut Command, imports: Vec<&str>)
 {
  for import in imports {
    cmd.arg("--import").arg(format!("{}={}", import, verus_data(import).display()));
    cmd.arg("--extern").arg(format!("{}={}", import, verus_library(import).display()));
  }
}

lazy_static!{
  static ref SYSTEM_CRATES: HashSet<&'static str> = {
    let mut set = HashSet::new();
    set.insert("vstd");
    set.insert("builtin");
    set.insert("builtin_macros");
    set
  };
}

lazy_static!{
  static ref WORKSPACE_CRATES: HashSet<&'static str> = {
    let mut set = HashSet::new();
    set.insert("vstd_extra");
    set.insert("aster_common");
    set
  };
}

fn path_simplify(path: PathBuf) -> PathBuf {
  path
    .canonicalize()
    .unwrap_or_else(|_| PathBuf::from(path))
    .to_string_lossy()
    .to_string()
    .into()
}

fn get_dependency(target: &String) -> Vec<(String, PathBuf)>
{
  let toml = Path::new(&target).join("Cargo.toml");
  let content = fs::read_to_string(&toml)
    .expect(format!("Failed to read {}", &toml.display()).as_str());
  let manifest = Manifest::from_str(&content)
    .expect(format!("Failed to parse {}", &toml.display()).as_str());
  let deps = manifest.dependencies
    .iter()
    .filter_map(|(name, dep)| {
      if SYSTEM_CRATES.contains(name.as_str()) {
        return None;
      }
      let local: PathBuf = match dep {
        Dependency::Detailed(pkg) => {
          if pkg.path.is_some() {
            Path::new(target).join(pkg.path.as_ref().unwrap())
          } else {
            Path::new(name).to_path_buf()
          }
        },
        _ => Path::new(name).to_path_buf()
      };
      let local = path_simplify(local);
      if local.is_dir() {
        Some((name.clone(), local))
      } else {
        None
      }
    })
    .collect();
  deps
} 

fn exec_verify(args: &VerifyArgs) -> Result<(), DynError> {
  let targets = &args.targets;
  let verus = get_verus();
  let z3 = get_z3();
  let mut imports = HashSet::new();
  imports.extend(args.imports.iter().map(|s| s.as_str()));
  
  for target in targets {
    let (target_file, crate_type) = crate_type(target);
    let cmd = &mut Command::new(&verus);
    cmd
      .env("VERUS_PATH", &verus)
      .env("VERUS_Z3_PATH", &z3);

    let deps = get_dependency(target);
    let mut target_import = HashSet::new();
    target_import.extend(imports.clone());
    target_import.extend(deps.iter().map(|(name, _)| name.as_str()));
    push_imports(cmd, target_import.iter().cloned().collect());

    if args.log {
      cmd.arg("--log-all");
    }
    cmd
      .arg(target_file)
      .arg(format!("--crate-type={}", crate_type))
      .arg("--expand-errors")
      .arg(format!("--multiple-errors={}", args.max_errors))
      .args(&args.pass_through)
      .arg("--")
      .arg("-C").arg(format!("metadata={}", target))
      .stdout(Stdio::inherit());

    println!("Verifying target: {}\n{:?}", target, cmd);
    cmd.status()?;
  }

  Ok(())
}

fn exec_compile(args: &CompileArgs) -> Result<(), DynError> {
  let targets = &args.targets;
  let verus = get_verus();
  let z3 = get_z3();
  let out_dir = Path::new("target");
  let mut imports: HashSet<&str> = HashSet::new();
  imports.extend(args.imports.iter().map(|s| s.as_str()));

  if !out_dir.exists() {
    fs::create_dir(out_dir)?;
  }

  for target in targets {
    let (target_file, crate_type) = crate_type(target);
    let output = format!("target/{}{}.{}", 
      binary_prefix(crate_type),
      target,
      binary_suffix(crate_type));
    let cmd = &mut Command::new(&verus);
    cmd
      .env("VERUS_PATH", &verus)
      .env("VERUS_Z3_PATH", &z3)
      .arg("--compile")
      .arg("--export").arg(format!("target/{}.verusdata", target));

    let deps = get_dependency(target);
    let mut target_import = HashSet::new();
    target_import.extend(imports.clone());
    target_import.extend(deps.iter().map(|(name, _)| name.as_str()));
    push_imports(cmd, target_import.iter().cloned().collect());

    if args.log {
      cmd.arg("--log-all");
    }
    cmd
      .arg(target_file)
      .arg(format!("--crate-type={}", crate_type))
      .arg("-o").arg(&output)
      .arg("-C").arg("opt-level=2")
      .arg("-V").arg("use-crate-name")
      .args(&args.pass_through)
      .arg("--")
      .arg("-C").arg(format!("metadata={}", target))
      .stdout(Stdio::inherit());

    // if !args.release {
    //   cmd.arg("-V").arg("debug");
    // }

    println!("Compiling target: {}\n{:?}", target, cmd);
    cmd.status()?;

    if !args.no_disasm {
      let objdump_binary = get_objdump();
      let objdump = &mut Command::new(&objdump_binary);
      let mut status = objdump
        .arg("-d")
        .arg(&output)
        .stdout(Stdio::piped())
        .spawn()?;

      let out = status
        .stdout
        .take()
        .expect("Failed to get objdump stdout");

      let rustfilt_binary = get_rustfilt();
      let mut rustfilt = Command::new(&rustfilt_binary);
      let mut status = rustfilt
        .stdin(Stdio::from(out))
        .stdout(Stdio::piped())
        .spawn()?;

      let mut disasm = File::create(
        format!("target/{}{}.{}.S", 
          binary_prefix(crate_type), 
          target,
          binary_suffix(crate_type))
      )?;

      let mut out = status.stdout.take().expect("Failed to get rustfilt stdout");
      let mut content = Vec::new();
      out.read_to_end(&mut content)?;
      disasm.write_all(&content)?;
    }
  }

  Ok(())
}

fn get_verus_doc() -> PathBuf {
  let verus_doc = PathBuf::from("tools/verus/source/target/release/verusdoc");
  if !verus_doc.is_file() {
    println!("Build verusdoc ...");
    Command::new("bash")
      .current_dir(PathBuf::from("tools/verus/source"))
      .arg("-c")
      .arg("source ../tools/activate && vargo build --package verusdoc")
      .status()
      .expect("Failed to build verusdoc");

    Command::new("bash")
      .current_dir(PathBuf::from("tools/verus/source"))
      .arg("-c")
      .arg("source ../tools/activate && vargo build --vstd-no-verify")
      .status()
      .expect("Failed to build debug vstd");

    println!("Done! verusdoc at {:?}", verus_doc);
  }
  absolutize(&verus_doc)
}

fn get_verus_root() -> PathBuf {
  let verus_root = PathBuf::from("tools/verus/source");
  if !verus_root.is_dir() {
    eprintln!("Cannot find the Verus source code, please clone the Verus repository to tools/verus");
    std::process::exit(1);
  }
  absolutize(&verus_root)
}

fn exec_doc(args: &DocArgs) -> Result<(), DynError> {
  let targets = &args.targets;
  let verus = get_verus();
  let z3 = get_z3();
  let verus_doc = get_verus_doc();
  let verus_root = get_verus_root();
  let dll_ext = match env::consts::OS {
    "windows" => "dll",
    "macos" => "dylib",
    _ => "so",
  };

  for target in targets {
    let target_root = Path::new(&target).join("src");
    let (target_file, crate_type) = if target_root.join("lib.rs").is_file() {
      (target_root.join("lib.rs"), "lib")
    } else {
      (target_root.join("main.rs"), "bin")
    };

    let cmd = &mut Command::new("rustdoc");
    cmd
      .env("RUSTC_BOOTSTRAP", "1")
      .env("VERUSDOC", "1")
      .env("VERUS_Z3_PATH", &z3)
      .env("VERUS", &verus_root)
      .arg("--extern").arg(format!("vstd={}/target-verus/debug/libvstd.rlib", verus_root.display()))
      .arg("--extern").arg(format!("builtin={}/target-verus/debug/libbuiltin.rlib", verus_root.display()))
      .arg("--extern").arg(format!("builtin_macros={}/target-verus/debug/libbuiltin_macros.{}", verus_root.display(), dll_ext))
      .arg("--extern").arg(format!("state_machines_macros={}/target-verus/debug/libstate_machines_macros.{}", verus_root.display(), dll_ext))
      .arg("--library-path").arg(format!("{}/vstd", verus_root.display()))
      .arg("--edition=2018")
      .arg("--cfg").arg("verus_keep_ghost")
      .arg("--cfg").arg("verus_keep_ghost_body")
      .arg("--cfg").arg("feature=\"std\"")
      .arg("--cfg").arg("feature=\"alloc\"")
      .arg("-Zcrate-attr=feature(stmt_expr_attributes)")
      .arg("-Zcrate-attr=feature(negative_impls)")
      .arg("-Zcrate-attr=feature(rustc_attrs)")
      .arg("-Zcrate-attr=feature(unboxed_closures)")
      .arg("-Zcrate-attr=feature(register_tool)")
      .arg("-Zcrate-attr=register_tool(verus)")
      .arg("-Zcrate-attr=register_tool(verifier)")
      .arg("-Zcrate-attr=register_tool(verusfmt)")
      .arg("-Zcrate-attr=allow(internal_features)")
      .arg("-Zcrate-attr=allow(unused_braces)")
      .arg(format!("--crate-type={}", crate_type))
      .arg(target_file)
      .stdout(Stdio::inherit());
    println!("> {:?}", cmd);
    cmd.status()?;

    let cmd = &mut Command::new(&verus_doc);
    cmd
      .env("VERUS_PATH", &verus)
      .env("VERUS", &verus_root)
      .stdout(Stdio::inherit());
    println!("> {:?}", cmd);
    cmd.status()?;
 }

  Ok(())
}

fn is_patch_applied(dir: &Path, patch: &Path) -> bool {
  let status = Command::new("git")
    .current_dir(dir)
    .stdout(Stdio::null())
    .stderr(Stdio::null())
    .arg("apply")
    .arg("--reverse")
    .arg("--check")
    .arg(patch)
    .status()
    .expect("Failed to check patch");
  status.success()
}

fn apply_patch(dir: &Path, patch: &Path) -> bool {
  let status = Command::new("git")
    .current_dir(dir)
    .arg("apply")
    .arg(patch)
    .status()
    .expect("Failed to apply patch");
  status.success()
}

fn build_vscode_extension(args: &BootstrapArgs) -> Result<(), DynError> {
  let verus_analyzer_repo = "https://github.com/verus-lang/verus-analyzer.git";
  let verus_analyzer_dir = Path::new("tools").join("verus-analyzer");

    if args.restart && verus_analyzer_dir.exists() {
      std::fs::remove_dir_all(&verus_analyzer_dir)?;
  }

  if !verus_analyzer_dir.exists() {
    println!("Start to clone the Verus Analyzer repository to {}", verus_analyzer_dir.display());
    let res = Repository::clone(verus_analyzer_repo, &verus_analyzer_dir);
    if res.is_err() {
      eprintln!("Failed to clone the Verus Analyzer repository. Please try to manually clone it to {} and run
      `cargo xtask bootstrap` again", verus_analyzer_dir.display());
      std::process::exit(1);
    }
  }  

  let verus_analyzer_patch = Path::new("..").join("patches").join("verus-analyzer-fixes.patch");
  if !is_patch_applied(&verus_analyzer_dir, &verus_analyzer_patch) {
    println!("Apply the Verus Analyzer patch");
    apply_patch(&verus_analyzer_dir, &verus_analyzer_patch);
  }

  println!("Start to build the Verus Analyzer");
  #[cfg(target_os = "windows")]
  {
    let cmd = &mut Command::new("cmd");
    cmd
      .current_dir(&verus_analyzer_dir)
      .env_remove("RUSTUP_TOOLCHAIN")
      .arg("/c")
      .arg("cargo xtask dist");
    println!("{:?}", cmd);
    cmd.status()?;
  }
  #[cfg(not(target_os = "windows"))]
  {
    let cmd = &mut Command::new("bash");
    cmd
      .current_dir(&verus_analyzer_dir)
      .env_remove("RUSTUP_TOOLCHAIN")
      .arg("-c")
      .arg("cargo xtask dist");
    println!("{:?}", cmd);
    cmd.status()?;
  }

  println!("Prepare the Verus Analyzer binary");
  #[cfg(target_os = "windows")]
  {
    Command::new("powershell")
    .current_dir(&verus_analyzer_dir)
    .arg("-Command")
    .arg(format!(
        "Get-ChildItem -Path './dist' -Filter 'verus-analyzer*.zip' | Expand-Archive -DestinationPath './dist' -Force"
    ))
    .status()?;
  }
  #[cfg(not(target_os = "windows"))]
  {
    Command::new("bash")
    .current_dir(&verus_analyzer_dir)
    .arg("-c")
    .arg("gunzip ./dist/verus-analyzer-*.gz && chmod u+x ./dist/verus-analyzer-*")
    .status()?;
  }
  let server = fs::read_dir(verus_analyzer_dir.join("dist")).unwrap().next().unwrap().unwrap().path();

  println!("Done LSP server: {:?}", server);

  Ok(())
}

fn exec_bootstrap(args: &BootstrapArgs) -> Result<(), DynError> {
  let verus_repo = "https://github.com/verus-lang/verus.git";
  let verus_dir = Path::new("tools").join("verus");

  // Not needed because we have included the Verus source code
  /*if args.restart && verus_dir.exists() {
      std::fs::remove_dir_all(&verus_dir)?;
  }

  if !verus_dir.exists() {
    println!("Start to clone the Verus repository to {}", verus_dir.display());
    let res = Repository::clone(verus_repo, &verus_dir);
    if res.is_err() {
      eprintln!("Failed to clone the Verus repository. Please try to manually clone it to {}", verus_dir.display());
      std::process::exit(1);
    }
  }*/

  #[cfg(target_os = "windows")]
  {
    let z3_path = Path::new("tools").join("verus").join("source").join("z3.exe");
    if !z3_path.exists() {
      println!("Start to download the Z3 solver");
      Command::new("powershell")
        .current_dir(Path::new("tools").join("verus").join("source"))
        .arg("/c")
        .arg(".\\tools\\get-z3.ps1")
        .status()
        .expect("Failed to run get-z3.ps1");
    }
  }
  #[cfg(not(target_os = "windows"))]
  {
    let z3_path = Path::new("tools").join("verus").join("source").join("z3");
    if !z3_path.exists() {
      println!("Start to download the Z3 solver");
      Command::new("bash")
        .current_dir(Path::new("tools").join("verus").join("source"))
        .arg("-c")
        .arg("tools/get-z3.sh")
        .status()
        .expect("Failed to run get-z3.sh");}
  }

  let verus_path = Path::new("..").join("patches").join("verus-fixes.patch");
  // Not needed because we have manually modified the Verus source code
  /*if !is_patch_applied(&verus_dir, &verus_path) {
    println!("Apply the Verus patch");
    apply_patch(&verus_dir, &verus_path);
  }*/

  println!("Start to build the Verus compiler");
  #[cfg(target_os = "windows")]
  {
    let cmd = &mut Command::new("powershell");
    cmd.current_dir(Path::new("tools").join("verus").join("source"))
      .arg("/c")
      .arg("& '..\\tools\\activate.ps1' ; vargo build --release --features singular");
      println!("{:?}", cmd);
    cmd.status()?;
  } 
  #[cfg(not(target_os = "windows"))]
  {    
    let cmd = &mut Command::new("bash");
    cmd.current_dir(Path::new("tools").join("verus").join("source"))
      .arg("-c")
      .arg("source ../tools/activate && vargo build --release --features singular");
    println!("{:?}", cmd);
    cmd.status()?; 
  }

  if !args.no_vscode_extension {
    build_vscode_extension(args)?;
  }

  Ok(())
}

fn main() {

  let mut all_targets = get_all_targets();
  all_targets.remove("xtask");

  let cli = Cli::parse();
  if let Err(e) = match &cli.command {
    Commands::Verify(args) => { exec_verify(args) }
    Commands::Doc(args) => { exec_doc(args) }
    Commands::Bootstrap(args) => { exec_bootstrap(args) }
    Commands::Compile(args) => { exec_compile(args) }
  } {
    eprintln!("Error: {}", e);
    std::process::exit(1);
  }
}
