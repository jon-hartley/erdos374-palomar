# Erdős Problem #374 — Lean 4 verification (Palomar edition)

Formal verification, in Lean 4 with Mathlib, of the results of

> J. S. Hartley, M. A. Olson, *A Resolution of Erdős 374* (SSRN, 2026)

This repository is organised for the [Palomar registry](https://palomar-registry.org) of
Lean-verified mathematics. Submissions go through <https://submit.palomar-registry.org/>.

For `m > 1`, `F(m)` is the least `k ≥ 2` such that `a₁! a₂! ⋯ a_k!` is a perfect square for
some `1 ≤ a₁ < ⋯ < a_k = m`, and `D_k = {m > 1 : F(m) = k}`. Erdős and Graham asked whether
`D_6` has positive lower density.

## What is proved

The statements are in [`Challenge.lean`](Challenge.lean), which imports only Mathlib and
documents every definition it uses. [`Solution.lean`](Solution.lean) repeats them verbatim and
proves them from the development in `src/`.

| Statement (namespace `ErdosProblem374`) | Content | Paper |
|---|---|---|
| `D6_positiveLowerDensity` | `D_6` has positive lower density | Thm 1.1 |
| `main_theorem` | `𝒜` has density `δ > 0`; `D_6 ∩ B_{1/100}` has density exactly `δ log(100/99)`; `D_6` has lower density `≥ δ log(100/99)` | Thm 1.1 |
| `D3_asymptotic` | `κ₃ = Σ_{q∈𝒬} q^{-1/2}` converges and `D_3(X) = κ₃ √X + O(X^{2/5+ε})` | Thm 7.1(i) |
| `D3_order` | `√X / 2 ≤ D_3(X) ≤ C √X` for large `X` | Thm 7.1(i) |
| `D4_lowerDensity` | `D_4` has lower density `≥ 1/4` | Thm 7.1(ii) |
| `D5_lowerDensity` | `D_5` has lower density `≥ log 2 / 40000` | Thm 7.1(iii) |

None of these has hypotheses, and all use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The analytic inputs (prime number theorem, an almost-all short-interval prime
estimate, a reciprocal-prime equidistribution estimate, Weil-type bounds, large sieves) are
proved inside the development.

## Checking

Requirements: [elan](https://github.com/leanprover/elan), git, and `bubblewrap` for Comparator.

```bash
lake exe cache get              # prebuilt Mathlib for the pinned commit
lake build                      # builds src/, Challenge and Solution
./scripts/verify-comparator.sh  # Comparator: Solution proves exactly the Challenge statements
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
```

The build compiles about 1,030 modules and takes roughly 2–3 CPU-hours. Eight modules (the
`UpperProfileCertificateData*` tables, `ProfileCertificateIndexed`,
`ProfileCertificateRectangleTables`) each need 3.5–4.5 GB of RAM; the six
`UpperProfileCertificateData*` modules are chained by imports so that they build one at a time.
On a machine with 8 GB of RAM, build the modules in `heavy_build_order` of
`module_inventory.json` first, one at a time.

Toolchain: Lean `v4.35.0-rc2` (`lean-toolchain`). Mathlib:
`487140449b0eceeb60afe04cab75cdcaaebf227f`, a commit on Mathlib `master`
(`lakefile.lean`, `lake-manifest.json`).

## Layout

```
Challenge.lean           the statements (Mathlib only)
Solution.lean            the same statements with proofs, and the bridge lemmas
comparator.json          Comparator configuration
formalization.yaml       Palomar metadata (sources, AI disclosure, scope)
lakefile.lean            package definition; the project modules are listed explicitly
src/                     1,002 modules of the proof of Theorem 1.1 (flat module names)
src/E374/                27 modules: the order-of-growth results
paper/                   the paper
scripts/                 source checks, metadata validator, Comparator runner
THIRD_PARTY_NOTICES.md   attribution for incorporated third-party Lean code
```

## Relation to the earlier repository

This is the development of
[`jon-hartley/erdos374_lean_verification`](https://github.com/jon-hartley/erdos374_lean_verification),
adapted to Palomar's requirements:

* every Lean file uses the module system (`module`, `public import`,
  `@[expose] public section`); modules that Mathlib imports privately, and that the original
  sources relied on, are imported explicitly;
* `Erdos374_Update152.lean` (62,511 lines) is split into `Erdos374_Update152_Part1` …
  `_Part6` and `Erdos374_Update152`, each under 10,000 lines; the parts reproduce the original
  text exactly, with the open sections and namespaces closed and reopened at each cut;
* three proof steps were adjusted for the module system (two tactic implementations marked
  `meta`, one `convert` replaced by a direct rewrite);
* `E374/D5Main.lean` states the explicit `D_5` constant as a separate theorem
  (`D5_lowerDensity`);
* `Challenge.lean`, `Solution.lean`, `comparator.json` and `formalization.yaml` are new.

Comments inside the development that mention "candidate", "conditional" or "uncompiled" are
historical markers from earlier stages of the work; the final theorems are unconditional, as
the axiom checks in `Erdos374CompleteWork.lean` and `src/E374/AuditIntegration.lean` confirm
when they compile.

## Where things are defined

* `Erdos374.HasRep`, `Erdos374.D6`, `Erdos374.sf`, `Erdos374.q`, `Erdos374.A`, `Erdos374.B`,
  `Erdos374.prefixCount`, `Erdos374.MainStatement`: `src/Erdos374_Update152_Part1.lean`.
* `Erdos374.D3`, `Erdos374.D5`: `src/E374/Basic.lean`; `Erdos374.D4`: `src/E374/D4.lean`.
* Final theorems: `Erdos374CompleteWork.erdos374` (Theorem 1.1) and
  `Erdos374.D35.Integration.*_closed` (growth results).
* `Solution.lean` proves that each definition in `Challenge.lean` agrees with the
  corresponding `Erdos374.*` definition (`hasRep_iff`, `D_six`, `count_eq`, …).

## Verification record

On 2026-10-06 every Lean file in this repository was compiled with Lean `v4.35.0-rc2` and
Mathlib `487140449b`, with 0 errors and no `sorry`. The project's own axiom guards
(`Erdos374CompleteWork.lean`, `src/E374/AuditIntegration.lean`) report only `propext`,
`Classical.choice` and `Quot.sound`. `lake comparator` was run on exports of `Challenge` and
`Solution`: the six statements match, and Lean's kernel, nanoda and con-ron accept the solution.

## License

Apache-2.0 (`LICENSE`). See `THIRD_PARTY_NOTICES.md` for incorporated code.
