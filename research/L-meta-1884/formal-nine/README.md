# Kernel-checked bound for every single-vertex deletion

Every signed circuit for the edge function after deleting one Petersen vertex needs at least 15 binary gates. All wire signs are free. Lean checked the lower bound for one representative, `NineCert.fifteen`, and its transfer to all ten deletions, `NineCert.all_deletions`. [Compiler axiom report](../evidence/formal-17.log)

The archive contains all 1,289 proof sources, a SHA-256 manifest and a replay script. [Download the source archive](sources.tar.gz)

With the built [pinned project](https://github.com/open-goat/pequalnp-proofs/tree/074709bd01fc526b9f6279e5b0a028946ceb39fb) and Lean 4.36.0 available, run

```sh
tar -xzf sources.tar.gz
cd petersen-nine
python3 replay.py --project /absolute/path/to/pequalnp-proofs/lean --jobs 4
```

The archive SHA-256 is `65eea9edd992bc479559e01bec3c8da55d7d5713cdf07b6e63dbdc86dd482a88`.
