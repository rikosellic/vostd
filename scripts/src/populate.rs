use ignore::WalkBuilder;
use std::{env, fs, path::PathBuf};

type Error = Box<dyn std::error::Error>;
type Result<T> = std::result::Result<T, Error>;

pub struct CopyTask {
    pub src: PathBuf,
    pub dest: PathBuf,
}

impl CopyTask {
    pub fn get() -> Result<Self> {
        let src = project_root::get_project_root()?;
        let dest = env::args().nth(1).ok_or("Destination directory not provided")?;
        if src.to_string_lossy() == dest {
            return Err("Source and destination directories cannot be the same".into());
        }

        let task = CopyTask {
            src,
            dest: PathBuf::from(dest),
        };

        Ok(task)
    }

    pub fn copy(&self) -> Result<()> {
        let walker = WalkBuilder::new(&self.src)
            .git_ignore(true)
            .git_exclude(false)
            .git_global(false)
            .hidden(false)
            .filter_entry(|entry| {
                // Skip any .git directory, otherwise include all entries
                entry.file_name() != ".git"
            })
            .build();

        for entry in walker {
            let entry = entry?;
            let path = entry.path();
            if entry.file_type().map(|ft| ft.is_file()).unwrap_or(false) {
                let rel = path.strip_prefix(&self.src)?;
                let dest_file = self.dest.join(rel);

                if let Some(parent) = dest_file.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::copy(path, &dest_file)?;
                print!(".");
            }
        }
        println!("\ndone!");

        Ok(())
    }
}



fn main() {
    if let Err(e) = run() {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let task = CopyTask::get()?;
    task.copy()?;

    Ok(())
}