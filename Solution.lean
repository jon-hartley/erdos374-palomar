module

public import Erdos374CompleteWork
public import E374.IntegrationD5
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Erdős Problem #374: proofs of the statements in `Challenge.lean`

This module repeats the definitions and theorem statements of `Challenge.lean` verbatim and
proves the theorems from the formal development in `src/`. The bridge lemmas below identify
each definition here with the corresponding definition of the development (`Erdos374.*`).

The documentation of `Challenge.lean` follows.

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

/-! ## Bridge to the formal development -/

theorem hasRep_iff (m k : ℕ) : HasRep m k ↔ Erdos374.HasRep m k := by
  constructor
  · rintro ⟨hk, S, hcard, hmS, hpos, hsq⟩
    have hne : S.Nonempty := ⟨m, hmS⟩
    have hmax : S.max' hne = m :=
      le_antisymm (Finset.max'_le _ _ _ fun a ha => (hpos a ha).2) (Finset.le_max' _ _ hmS)
    refine ⟨hk, ⟨⟨fun i => S.orderEmbOfFin hcard i, (S.orderEmbOfFin hcard).strictMono,
      fun i => (hpos _ (S.orderEmbOfFin_mem hcard i)).1, ?_, ?_⟩⟩⟩
    · intro i hi
      have hi' : i = ⟨k - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hi', Finset.orderEmbOfFin_last hcard (by omega), hmax]
    · rw [Erdos374.natSquare_iff_isSquare]
      have himg : (Finset.univ.image fun i => S.orderEmbOfFin hcard i) = S :=
        Finset.image_orderEmbOfFin_univ S hcard
      have hprod : ∏ i : Fin k, (S.orderEmbOfFin hcard i).factorial = ∏ a ∈ S, a.factorial := by
        conv_rhs => rw [← himg]
        rw [Finset.prod_image]
        intro x _ y _ h
        exact (S.orderEmbOfFin hcard).injective h
      rw [hprod]
      exact hsq
  · rintro ⟨hk, ⟨r⟩⟩
    have hlast : r.index ⟨k - 1, by omega⟩ = m := r.endpoint _ (by simp; omega)
    refine ⟨hk, Finset.univ.image r.index, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ r.increasing.injective]
      simp
    · exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, hlast⟩
    · intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      refine ⟨r.positive i, ?_⟩
      calc r.index i ≤ r.index ⟨k - 1, by omega⟩ :=
            r.increasing.monotone (Fin.le_iff_val_le_val.2 (by simp; omega))
        _ = m := hlast
    · rw [Finset.prod_image]
      · exact (Erdos374.natSquare_iff_isSquare _).1 r.square
      · intro x _ y _ h
        exact r.increasing.injective h

theorem D_eq (k : ℕ) :
    D k = {m | 1 < m ∧ Erdos374.HasRep m k ∧ ∀ j : ℕ, 2 ≤ j → j < k → ¬ Erdos374.HasRep m j} := by
  ext m
  simp only [D, Set.mem_ofPred_eq, hasRep_iff]

theorem D_six : D 6 = Erdos374.D6 := D_eq 6

theorem count_eq (S : Set ℕ) (N : ℕ) : count S N = Erdos374.prefixCount S N := by
  classical
  unfold count Erdos374.prefixCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
  tauto

theorem lowerDensity_iff (S : Set ℕ) (δ : ℝ) :
    LowerDensityAtLeast S δ ↔ Erdos374.LowerDensityAtLeast S δ := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h ε hε)
    exact ⟨N, fun X hX => by have := hN X hX; rwa [count_eq] at this⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact Filter.eventually_atTop.2 ⟨N, fun X hX => by rw [count_eq]; exact hN X hX⟩

theorem hasDensity_iff (S : Set ℕ) (δ : ℝ) : HasDensity S δ ↔ Erdos374.HasDensity S δ := by
  unfold HasDensity Erdos374.HasDensity Erdos374.proportion
  rw [Metric.tendsto_atTop]
  simp only [Real.dist_eq, count_eq, ge_iff_le, gt_iff_lt]

theorem sf_eq : sf = Erdos374.sf := by
  funext n
  unfold sf Erdos374.sf
  congr

theorem q_eq : q = Erdos374.q := by
  funext a
  simp only [q, Erdos374.q, sf_eq]

theorem A_eq : A = Erdos374.A := by
  ext m
  simp only [A, Erdos374.A, Set.mem_ofPred_eq, q_eq]

theorem largestPrime_eq : largestPrime = Erdos374.largestPrime := rfl

theorem B_eq (α : ℝ) : B α = Erdos374.B α := by
  ext m
  simp only [B, Erdos374.B, Erdos374.LargePrime, Set.mem_ofPred_eq, A_eq, largestPrime_eq]

theorem D_three : D 3 = Erdos374.D3 := by
  ext m
  simp only [D, Erdos374.D3, Set.mem_ofPred_eq, hasRep_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3 2 le_rfl (by norm_num)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hj3 => ?_⟩
    have hj2 : j = 2 := by omega
    rw [hj2]
    exact h3

theorem D_four : D 4 = Erdos374.D4 := D_eq 4

theorem D_five : D 5 = Erdos374.D5 := D_eq 5

theorem Q_eq : Q = Erdos374.D35.Qset := by
  ext n
  simp only [Q, Erdos374.D35.Qset, Set.mem_ofPred_eq, q_eq]

theorem indicator_eq :
    Set.indicator Q (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) = Erdos374.D35.kappaTerm := by
  classical
  funext n
  rw [Q_eq]
  unfold Erdos374.D35.kappaTerm
  rw [Set.indicator_apply]

theorem kappa3_eq : kappa3 = Erdos374.D35.kappa3 := by
  unfold kappa3 Erdos374.D35.kappa3
  rw [indicator_eq]

/-! ## The theorems of `Challenge.lean` -/

/-- **Theorem 1.1.** There is `δ > 0` (the density of `𝒜`) such that `𝒜` has natural density
`δ`, the set `D_6 ∩ B_{1/100}` has natural density exactly `δ log(100/99)`, and `D_6` has lower
density at least `δ log(100/99)`. The theorem does not claim that `D_6` itself has a natural
density. -/
theorem main_theorem :
    ∃ δ : ℝ, 0 < δ ∧ HasDensity A δ ∧
      HasDensity (D 6 ∩ B (1 / 100)) (δ * Real.log (100 / 99)) ∧
      LowerDensityAtLeast (D 6) (δ * Real.log (100 / 99)) := by
  obtain ⟨δ, hδ, hA, hD, hL, -⟩ := Erdos374CompleteWork.erdos374
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · rw [hasDensity_iff, A_eq]
    exact hA
  · rw [hasDensity_iff, D_six, B_eq]
    exact hD
  · rw [lowerDensity_iff, D_six]
    exact hL

/-- **Erdős–Graham (Erdős Problem #374).** `D_6` has positive lower density. -/
theorem D6_positiveLowerDensity : ∃ δ : ℝ, 0 < δ ∧ LowerDensityAtLeast (D 6) δ := by
  obtain ⟨δ, hδ, -, -, hL⟩ := main_theorem
  exact ⟨δ * Real.log (100 / 99), mul_pos hδ (Real.log_pos (by norm_num)), hL⟩

/-- **Theorem 7.1(i).** The series defining `κ₃` converges, and for every `ε > 0` there is `C`
with `|D_3(X) - κ₃ √X| ≤ C X^{2/5+ε}` for all large `X`. -/
theorem D3_asymptotic :
    Summable (Set.indicator Q (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ X : ℕ in Filter.atTop,
        |(count (D 3) X : ℝ) - kappa3 * Real.sqrt X| ≤ C * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
  refine ⟨?_, fun ε hε => ?_⟩
  · rw [indicator_eq]
    exact Erdos374.D35.kappaTerm_summable Erdos374.D35.Integration.factorialGrowth
  · obtain ⟨C, N, hN⟩ := Erdos374.D35.Integration.D3_asymptotic_closed ε hε
    refine ⟨C, Filter.eventually_atTop.2 ⟨N, fun X hX => ?_⟩⟩
    rw [count_eq, D_three, kappa3_eq]
    exact hN X hX

/-- **Theorem 7.1(i), order of growth.** `D_3(X) ≍ √X`: for some `C`, eventually
`√X / 2 ≤ D_3(X) ≤ C √X`. In particular `D_3` has density zero. -/
theorem D3_order :
    ∃ C : ℝ, ∀ᶠ X : ℕ in Filter.atTop,
      Real.sqrt X / 2 ≤ (count (D 3) X : ℝ) ∧ (count (D 3) X : ℝ) ≤ C * Real.sqrt X := by
  obtain ⟨C, N, hN⟩ := Erdos374.D35.Integration.D3_order_closed
  refine ⟨C, Filter.eventually_atTop.2 ⟨N, fun X hX => ?_⟩⟩
  rw [count_eq, D_three]
  exact hN X hX

/-- **Theorem 7.1(ii).** `D_4` has lower density at least `1/4`. -/
theorem D4_lowerDensity : LowerDensityAtLeast (D 4) (1 / 4) := by
  rw [lowerDensity_iff, D_four]
  exact Erdos374.D35.Integration.D4_lowerDensity_closed

/-- **Theorem 7.1(iii).** `D_5` has lower density at least `log 2 / 40000`. -/
theorem D5_lowerDensity : LowerDensityAtLeast (D 5) (Real.log 2 / 40000) := by
  rw [lowerDensity_iff, D_five]
  exact Erdos374.D35.Integration.D5_lowerDensity_closed

end ErdosProblem374

end
