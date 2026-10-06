# Third-party code incorporated in this repository

Some project sources incorporate Lean code written by others. Copyright headers and license
statements are kept verbatim in the files. The Apache License 2.0 text is in `LICENSE` and
`LICENSES/Apache-2.0.txt`.

`src/Erdos374_Update152.lean` of the earlier repository is split here into
`src/Erdos374_Update152_Part1.lean` … `_Part6.lean` and `src/Erdos374_Update152.lean`; the
locations below refer to the split files.

| Component | Where | Origin and license (as stated in the source) |
|---|---|---|
| PrimeNumberTheoremAnd (14 flattened modules, e.g. `Auxiliary`, `MellinCalculus`, `ZetaBounds`, `MediumPNT`) | `src/Erdos374_Update152_Part4.lean`, `_Part5.lean`, `_Part6.lean`, sections `Flat_PrimeNumberTheoremAnd_*`; shim `src/PrimeNumberTheoremAnd/ZetaBounds.lean` | PrimeNumberTheoremAnd project (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd); Apache-2.0. Headers include Copyright (c) 2024 Michael Stoll. |
| Additive large sieve (`ImportedLargeSieve135`) | `src/Erdos374_Update152_Part4.lean`, §135A | https://github.com/ericlisg/erdos768-lean (`RequestProject/LargeSieve.lean`, parts of `LargeSieveMult.lean`); Apache-2.0, full text reproduced in the file. |
| Mathlib-derived snippet | `src/Erdos374_Update152_Part5.lean` | Copyright (c) 2022 Abby J. Goldberg; authors Abby J. Goldberg, Mario Carneiro, Heather Macbeth; Apache-2.0. |
| Riemann hypothesis for hyperelliptic curves over finite fields (`riemann_hypothesis_hec` and supporting lemmas) | `src/Erdos374_Update152_Part6.lean` (port marked `BEGIN PORTED MODULE`; used by `ExternalInputs149.coarseHyperellipticCount`) | Port of https://github.com/math-inc/RiemannHypothesisCurves at commit `c99880dff2a087d59147ab832074379ac28f7e68` (Math Inc.; produced by the Gauss autoformalization agent). **That repository has no license file or license statement. Permission or a license from Math Inc. is needed for redistribution under Apache-2.0.** |
| Item-1 support files (`Item1Vmvt*.lean` and others with headers) | `src/` | Copyright (c) 2026 Jason Hickey (18 files) and Copyright (c) 2026 Salt contributors (`Item1VmvtPrimeCount.lean`); Apache-2.0. |

Mathlib and its dependencies are not vendored. Lake fetches them at the pinned revisions
(Apache-2.0).
