use std::process::{Command, Stdio};
use std::path::{Path, PathBuf};
use glob::glob;

use crate::error::*;
use crate::manifest::{Manifest, Subrepo};

const GITSLAVE_DIR: &str = ".git-slave";

pub fn ensure_gits(url: &str) -> Result<PathBuf> {
    let subrepo_dir = Path::new(GITSLAVE_DIR);
    if !subrepo_dir.exists() {
        let status = Command::new("git")
            .args(["clone", url, GITSLAVE_DIR])
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit())
            .status()?;
        if !status.success() {
            return Err(format!("Failed to clone subrepo: {}", url).into());
        }
    }

    let subrepo_pattern = subrepo_dir
        .join("tools")
        .join("gitslave-*")
        .join("gits");

    let subrepo = glob(subrepo_pattern.to_str().unwrap())?
        .filter_map(|entry| entry.ok())
        .find(|entry| entry.is_file())
        .ok_or_else(|| format!("Subrepo binary not found in: {}", subrepo_pattern.display()))?;

    if !subrepo.exists() {
        return Err(format!("Subrepo binary not found: {}", subrepo.display()).into());
    }

    Ok(subrepo)
}

pub fn gits_prepare(gits: &Path) -> Result<()> {
    let cmd = &mut Command::new("perl");
    cmd
        .arg(gits)
        .arg("--no-commit")
        .arg("prepare")
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());

    println!(">> {:?}", cmd);

    if !cmd.status()?.success() {
        return Err(format!("Failed to prepare gitslave: {}", gits.display()).into());
    }

    Ok(())
}

pub fn clone(repo: &Subrepo, gits: &Path) -> Result<()> {
    let repo_dir = Path::new(&repo.path);
    if repo_dir.exists() {
        return Err(format!("Subrepo directory already exists: {}", repo.path).into());
    }

    let cmd = &mut Command::new("perl");
    cmd
        .arg(gits)
        .arg("--no-commit")
        .arg("attach")
        .arg(repo.url.as_str())
        .arg(repo.path.as_str())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());

    println!(">> {:?}", cmd);

    if !cmd.status()?.success() {
        return Err(format!("Failed to clone subrepo: {}", repo.name).into());
    }

    let cmd = &mut Command::new("git");
    cmd
        .current_dir(repo_dir)
        .arg("checkout");
    if let Some(commit) = &repo.commit {
        cmd.arg(commit);
    } else {
        cmd.arg(repo.branch.as_str());
    }

    cmd.stdout(Stdio::inherit())
        .stderr(Stdio::inherit());

    if !cmd.status()?.success() {
        return Err(format!("Failed to checkout commit: {}", repo.name).into());
    }

    Ok(())
}


pub fn clone_all(manifest: &Manifest) -> Result<()> {
    let gits = ensure_gits(&manifest.master.url)?;
    gits_prepare(&gits)?;

    for repo in &manifest.repo {
        match clone(repo, &gits) {
            Ok(_) => println!("Cloned subrepo: {}", repo.name),
            Err(e) => eprintln!("Error cloning subrepo {}: {}", repo.name, e),
        }
    }

    Ok(())
}
