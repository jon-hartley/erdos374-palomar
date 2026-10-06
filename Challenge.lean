module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Erdős Problem #374: square products of factorials

For `m > 1` let `F(m)` be the least `k ≥ 2` for which there are integers
`1 ≤ a₁ < a₂ < ⋯ < a_k = m` such that `a₁! a₂! ⋯ a_k!` is a perfect square
(`F(m) = ∞` if there are none), and let `D_k = {m > 1 : F(m) = k}`.
Erdős and Graham [*On products of factorials*, Bull. Inst. Math. Acad. Sinica 4 (1976)]
showed that every composite `m` has `F(m) ≤ 6` and asked whether `D_6` has positive
lower density; see <https://www.erdosproblems.com/374>.

This file states, using only Mathlib, the results of
J. S. Hartley and M. A. Olson, *A Resolution of Erdős 374* (SSRN, 2026):

* `D6_positiveLowerDensity`: `D_6` has positive lower density.
* `main_theorem` (Theorem 1.1): an explicit squarefree set `𝒜` has a natural density
  `δ_𝒜 > 0`, the members of `D_6` in `B_{1/100} ⊆ 𝒜` have natural density exactly
  `δ_𝒜 log(100/99)`, and so `D_6` has lower density at least `δ_𝒜 log(100/99)`.
* `D3_asymptotic`, `D3_order` (Theorem 7.1(i)): `D_3(X) = κ₃ √X + O(X^{2/5+ε})` and
  `D_3(X) ≍ √X`.
* `D4_lowerDensity`, `D5_lowerDensity` (Theorem 7.1(ii), (iii)): `D_4` and `D_5` have lower
  densities at least `1/4` and `log 2 / 40000`.

Conventions. The factorial indices are positive. Allowing the index `0` or `1` (whose factorial
is `1`) does not change `F(m)` for `m > 1`: such a factor can be deleted from any
representation with at least three factors, and `1! · m!` or `0! · m!` is a square only for
`m ≤ 1`. A natural number `n` is a square when `IsSquare n`, i.e. `n = r * r` for some
natural `r`. `F(m)` itself is not defined; `D k` is defined directly as the set of `m > 1`
having a representation with `k` factorials and none with `j` factorials, `2 ≤ j < k`.
-/

namespace ErdosProblem374

/-- `HasRep m k`: `k ≥ 2` and there is a set `S` of `k` positive integers whose largest
element is `m` such that `∏_{a ∈ S} a!` is a perfect square. Listing `S` in increasing order,
this says there are `1 ≤ a₁ < a₂ < ⋯ < a_k = m` with `a₁! a₂! ⋯ a_k!` a square. -/
def HasRep (m k : ℕ) : Prop :=
  2 ≤ k ∧ ∃ S : Finset ℕ, S.card = k ∧ m ∈ S ∧ (∀ a ∈ S, 1 ≤ a ∧ a ≤ m) ∧
    IsSquare (∏ a ∈ S, a.factorial)

/-- `D k = {m > 1 : F(m) = k}`: the integers `m > 1` that have a representation with `k`
factorials and none with `j` factorials for any `2 ≤ j < k`. -/
def D (k : ℕ) : Set ℕ :=
  {m | 1 < m ∧ HasRep m k ∧ ∀ j : ℕ, 2 ≤ j → j < k → ¬ HasRep m j}

/-- The counting function `count S N = #(S ∩ [1, N])`. -/
noncomputable def count (S : Set ℕ) (N : ℕ) : ℕ := (S ∩ Set.Icc 1 N).ncard

/-- `S` has natural density `δ`: `count S N / N → δ` as `N → ∞`. -/
def HasDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => (count S N : ℝ) / N) Filter.atTop (nhds δ)

/-- `S` has lower density at least `δ`, i.e. `liminf_{N → ∞} count S N / N ≥ δ`. It is stated
without `liminf`: for every `ε > 0`, eventually `count S N / N ≥ δ - ε`. -/
def LowerDensityAtLeast (S : Set ℕ) (δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, δ - ε ≤ (count S N : ℝ) / N

/-- The squarefree kernel `sf n`: the product of the primes that divide `n` to an odd power.
For `n ≥ 1`, `n / sf n` is a perfect square. (`sf 0 = 1`; it is not used.) -/
def sf (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1), p

/-- `q a = sf (a!)`, the squarefree kernel of `a!`. A product of factorials is a square
exactly when the product of the corresponding kernels is a square. -/
def q (a : ℕ) : ℕ := sf a.factorial

/-- The set `𝒜` of the paper, display (1.1): the squarefree `m ≥ 1` with
`gcd(m, q a)² ≤ q a` for every `a ≥ 2` (for every such `a`, not only for `a < m`). -/
def A : Set ℕ :=
  {m | 1 ≤ m ∧ Squarefree m ∧ ∀ a : ℕ, 2 ≤ a → Nat.gcd m (q a) ^ 2 ≤ q a}

/-- The largest prime factor `P⁺(m)`, with the convention `P⁺(1) = 1` (and `P⁺(0) = 1`). -/
def largestPrime (m : ℕ) : ℕ := max 1 (m.primeFactors.sup id)

/-- `B α = {m ∈ 𝒜 : P⁺(m) > m^{1-α}}`, the members of `𝒜` with a prime factor larger
than `m^{1-α}`. -/
def B (α : ℝ) : Set ℕ :=
  {m | m ∈ A ∧ (m : ℝ) ^ (1 - α) < (largestPrime m : ℝ)}

/-- The set `𝒬` of nontrivial factorial kernels: the values `q a ≠ 1` with `a ≥ 1`.
As a set, each value is recorded once even when it arises from several `a`. -/
def Q : Set ℕ := {n | n ≠ 1 ∧ ∃ a : ℕ, 1 ≤ a ∧ n = q a}

/-- The constant `κ₃ = ∑_{n ∈ 𝒬} n^{-1/2}` (numerically `κ₃ = 2.70975…`). The series converges;
this is part of `D3_asymptotic`. -/
noncomputable def kappa3 : ℝ :=
  ∑' n : ℕ, Set.indicator Q (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) n

/-- **Erdős–Graham (Erdős Problem #374).** `D_6` has positive lower density. -/
theorem D6_positiveLowerDensity : ∃ δ : ℝ, 0 < δ ∧ LowerDensityAtLeast (D 6) δ := by
  sorry

/-- **Theorem 1.1.** There is `δ > 0` (the density of `𝒜`) such that `𝒜` has natural density
`δ`, the set `D_6 ∩ B_{1/100}` has natural density exactly `δ log(100/99)`, and `D_6` has lower
density at least `δ log(100/99)`. The theorem does not claim that `D_6` itself has a natural
density. -/
theorem main_theorem :
    ∃ δ : ℝ, 0 < δ ∧ HasDensity A δ ∧
      HasDensity (D 6 ∩ B (1 / 100)) (δ * Real.log (100 / 99)) ∧
      LowerDensityAtLeast (D 6) (δ * Real.log (100 / 99)) := by
  sorry

/-- **Theorem 7.1(i).** The series defining `κ₃` converges, and for every `ε > 0` there is `C`
with `|D_3(X) - κ₃ √X| ≤ C X^{2/5+ε}` for all large `X`. -/
theorem D3_asymptotic :
    Summable (Set.indicator Q (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ X : ℕ in Filter.atTop,
        |(count (D 3) X : ℝ) - kappa3 * Real.sqrt X| ≤ C * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
  sorry

/-- **Theorem 7.1(i), order of growth.** `D_3(X) ≍ √X`: for some `C`, eventually
`√X / 2 ≤ D_3(X) ≤ C √X`. In particular `D_3` has density zero. -/
theorem D3_order :
    ∃ C : ℝ, ∀ᶠ X : ℕ in Filter.atTop,
      Real.sqrt X / 2 ≤ (count (D 3) X : ℝ) ∧ (count (D 3) X : ℝ) ≤ C * Real.sqrt X := by
  sorry

/-- **Theorem 7.1(ii).** `D_4` has lower density at least `1/4`. -/
theorem D4_lowerDensity : LowerDensityAtLeast (D 4) (1 / 4) := by
  sorry

/-- **Theorem 7.1(iii).** `D_5` has lower density at least `log 2 / 40000`. -/
theorem D5_lowerDensity : LowerDensityAtLeast (D 5) (Real.log 2 / 40000) := by
  sorry

end ErdosProblem374

end
