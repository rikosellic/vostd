use serde_derive::Deserialize;
use std::fs;
use std::path::Path;
use crate::error::*;

#[derive(Deserialize)]
pub struct Master {
    pub url: String,
    pub shallow: bool,
}

#[derive(Deserialize)]
pub struct Subrepo {
    pub name: String,
    pub url: String,
    pub path: String,
    pub branch: String,
    pub remote: Option<String>,
    pub commit: Option<String>,
}

#[derive(Deserialize)]
pub struct Manifest {
    pub master: Master,
    pub repo: Vec<Subrepo>,
}

const MANIFEST_PATH: &str = "subrepo.toml";

pub fn load_config() -> Result<Manifest> {
    let manifest_path = Path::new(MANIFEST_PATH);
    if !manifest_path.exists() {
        return Err(format!("Manifest file not found: {}", MANIFEST_PATH).into());
    }

    let content = fs::read_to_string(manifest_path)?;
    let manifest: Manifest = toml::from_str(&content)?;

    Ok(manifest)
}