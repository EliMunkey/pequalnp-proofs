"""Rebuild the three-check implication from the two source archives in this package."""
import argparse
import hashlib
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile


def unpack(archive, root_name, destination):
    with tarfile.open(archive, "r:gz") as bundle:
        for member in bundle:
            if member.isdir():
                continue
            name = PurePosixPath(member.name)
            if not member.isfile() or name.is_absolute() or ".." in name.parts or name.parts[0] != root_name:
                raise ValueError(f"Unexpected archive member {member.name!r}")
            path = destination.joinpath(*name.parts[1:])
            if path.exists():
                raise ValueError(f"Duplicate source {path}")
            path.parent.mkdir(parents=True, exist_ok=True)
            with bundle.extractfile(member) as source:
                path.write_bytes(source.read())


def verify(root, filename):
    for line in (root / filename).read_text().splitlines():
        digest, name = line.split("  ", 1)
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"Source checksum mismatch for {name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="Pinned pequalnp-proofs checkout or lean directory")
    parser.add_argument("work", type=Path, help="New directory to retain extracted sources and compiled results")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    unpack(package.parent / "first-gates/ten-input.tar.gz", "petersen-starts", work)
    unpack(package / "additional-lean.tar.gz", "petersen-additional", work)
    verify(work, "SHA256SUMS")
    verify(work, "EXTRA-SHA256SUMS")
    names = (work / "modules.txt").read_text().splitlines() + (work / "extra-modules.txt").read_text().splitlines()
    if len(set(names)) != len(names):
        raise ValueError("A module occurs in both source archives")
    (work / "modules.txt").write_text("\n".join(sorted(names)) + "\n")
    (work / "entry-module.txt").write_text("PetersenThreeChecks\n")
    # Recompute only the two inventory digests edited above. Both original archives have passed verification.
    hashes = []
    for manifest in ("SHA256SUMS", "EXTRA-SHA256SUMS"):
        for line in (work / manifest).read_text().splitlines():
            digest, filename = line.split("  ", 1)
            if filename in ("modules.txt", "entry-module.txt"):
                digest = hashlib.sha256((work / filename).read_bytes()).hexdigest()
            hashes.append(f"{digest}  {filename}")
    (work / "SHA256SUMS").write_text("\n".join(hashes) + "\n")
    verify(work, "SHA256SUMS")
    print(f"Verified {len(names)} source modules", flush=True)
    if not args.prepare_only:
        subprocess.run([sys.executable, str(work / "replay.py"), str(args.project.resolve()),
                        "--jobs", str(args.jobs)], check=True)


if __name__ == "__main__":
    main()
