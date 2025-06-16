use std::process::{Command, Stdio};
use std::path::{Path};
use git2::Repository;

use crate::error::*;
use crate::manifest::{Subrepo};

pub fn git_branch(repo: &Repository) -> Result<String> {
    let head = repo.head().map_err(|e| format!("Failed to get HEAD: {}", e))?;
    let branch_name = head.shorthand()
        .ok_or_else(|| "HEAD is not pointing to a branch".to_string())?;
    Ok(branch_name.to_string())
}

pub fn git_branches(repo: &Repository) -> Result<Vec<String>> {
    let mut branches = Vec::new();
    for branch in repo
        .branches(None)
        .map_err(|e| format!("Failed to get branches: {}", e))? 
    {
        let (branch, _) = branch
            .map_err(|e| format!("Failed to get branch: {}", e))?;
        let name = branch
            .name()
            .map_err(|e| format!("Failed to get branch name: {}", e))?;
        if let Some(name) = name {
            branches.push(name.to_string());
        }
    }
    Ok(branches)
}

pub fn repo_dir(repo: &Repository) -> String {
    repo.path().parent()
        .and_then(|p| p.to_str())
        .map(|s| s.to_string())
        .unwrap_or_else(|| {
            panic!("Failed to get repository directory for {}", repo.path().display())
        })
}

pub fn git_fetch(repo: &Repository) -> Result<()> {
    let cmd = &mut Command::new("git");
    cmd.arg("fetch")
        .arg("--progress")
        .arg("--all")
        .arg("--prune")
        .current_dir(repo_dir(repo))
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    println!(">> {:?}", cmd);
    if cmd.status().is_err() {
        return Err("Failed to fetch updates".into());
    }
    Ok(())
}

pub fn switch_to(repo: &Repository, branch: &str) -> Result<()> {
    let cmd = &mut Command::new("git");
    cmd.arg("switch")
        .arg(branch)
        .current_dir(repo_dir(repo))
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    if cmd.status().is_err() {
        return Err(format!("Failed to switch to branch '{}'", branch).into());
    }
    Ok(())
}

pub fn git_pull(repo: &Repository, remote: &Option<String>, branch: &Option<String>) -> Result<()> {
    git_fetch(repo)?;

    let b: String;
    if let Some(br) = branch {
        let branches = git_branches(repo)?;
        if !branches.contains(br) {
            return Err(format!("Branch '{}' does not exist in the repository", br).into());
        }
        switch_to(repo, br)?;
        b = br.to_string();

    } else {
        b = git_branch(repo)?;
    }
    let remote = remote.as_deref().unwrap_or("origin");
    let cmd = &mut Command::new("git");
    cmd.arg("pull")
        .arg(remote)
        .arg(b)
        .current_dir(repo_dir(repo))
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    println!(">> {:?}", cmd);
    if cmd.status().is_err() {
        return Err(format!("Failed to pull from remote '{}'", remote).into());
    }
    println!("Successfully pulled from remote '{}'", remote);

    Ok(())
}

pub fn git_clone(url: &str, path: &str, branch: &str, shallow: bool) -> Result<Repository> {
    let mut cmd = Command::new("git");
    cmd.arg("clone")
        .arg("--progress")
        .arg("--single-branch")
        .arg("--branch")
        .arg(branch)
        .arg(url)
        .arg(path);

    if shallow {
        cmd.args(["--depth", "1"]);
    }

    cmd.stdout(Stdio::inherit())
       .stderr(Stdio::inherit());

    if cmd.status().is_err() {
        return Err(format!("Failed to clone repository from {} to {}", url, path).into());
    }

    let repo = Repository::open(path)
        .map_err(|e| format!("Failed to open cloned repository: {}", e))?;

    Ok(repo)

}

pub fn git_sync(repo: &Subrepo, shallow: bool) -> Result<()> {
    let dir = Path::new(&repo.path);
    let repository: Repository;

    if dir.exists() {
        repository = Repository::open(dir)
            .map_err(|e| format!("{} is not a git repository: {}", repo.path, e))?;
        git_pull(&repository, &repo.remote, &Some(repo.branch.clone()))?;
    } else {
        repository = git_clone(&repo.url, &repo.path, &repo.branch, shallow)?;
    }

    if let Some(commit) = &repo.commit {
        let obj = repository.revparse_single(commit)
            .map_err(|e| format!("Failed to find commit {}: {}", commit, e))?;
        repository.checkout_tree(&obj, None)
            .map_err(|e| format!("Failed to checkout commit {}: {}", commit, e))?;
    }

    Ok(())
}

pub fn sync_all(repos: &[Subrepo], shallow: bool) -> Result<()> {
    for repo in repos {
        match git_sync(repo, shallow) {
            Ok(_) => println!("Successfully synced {}", repo.name),
            Err(e) => eprintln!("Error syncing {}: {}", repo.name, e),
        }
    }
    Ok(())
}