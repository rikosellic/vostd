use solana_dv_scripts::prelude::*;

fn sync(manifest: &Manifest) -> Result<()> {
    git::sync_all(&manifest.repo, manifest.master.shallow)
}


fn main() {
    let manifest = load_config().expect("Failed to load config");
    let _ = sync(&manifest);
}
