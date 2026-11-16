# Publish the four Lean packages

Each folder below becomes its own public repository under NousVolition:

- `hug-gap-lean`
- `discrete-poincare-lean`
- `cycle-wirtinger-lean`
- `hypercube-isoperimetric-lean`

Each folder already contains a GitHub Actions check, `.github/workflows/lean.yml`. On every push, the check:

1. installs the Lean version pinned in `lean-toolchain`;
2. downloads the Mathlib cache;
3. runs `lake build`;
4. runs `CheckAxioms.lean`, and fails if any theorem uses `sorryAx` or any axiom other than `propext`, `Classical.choice` and `Quot.sound`.

## Commands (run from inside this folder)

```
for p in hug-gap-lean discrete-poincare-lean cycle-wirtinger-lean hypercube-isoperimetric-lean; do
  (cd "$p" && git init -b main && git add -A \
    && git commit -m "Lean package: $p" \
    && gh repo create "NousVolition/$p" --public --source . --push)
done
```

Then, for each repository, `gh run list -R NousVolition/<name>` shows whether the check passed.

## If a check fails

Open the failed run, copy the first `error:` lines from the "lean-action" or "Axiom check" step, and send them back.

These packages were written without a local Lean build. The first run is the first compile, so small tactic fixes are expected.
