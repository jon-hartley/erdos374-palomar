/- Part 4 of 7 of `Erdos374_Update152` (split for the 10,000-line limit); continues `Erdos374_Update152_Part3`. -/
module

public import Erdos374_Update152_Part3

@[expose] public section


section Update152_Component_1
section Update151_Component_1
section Update150_Component_1
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace Erdos374
open Filter Asymptotics
namespace RemainingAnalytic115
open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic24 RemainingAnalytic37
open RemainingAnalytic43 RemainingAnalytic47 RemainingAnalytic101
open RemainingAnalytic109 RemainingAnalytic111
namespace RemainingAnalytic132
open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic47 RemainingAnalytic127
open RemainingAnalytic130 RemainingAnalytic131

/-- Six remaining inputs. Only the finite positive-margin witness remains
from the former A_density_limit package; existence/convergence is derived. -/
structure EverythingLeftCorrected132 where
  theta_logsq_remainder : ThetaLogSqRemainder127
  A_positive_margin : FinitePositiveMargin132 theta_logsq_remainder
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  large_sieve : RemainingAnalytic92.ClassicalPrimeAdditiveLargeSieve92
  large_modulus_weil : LargeModulusLinearProductWeil127

noncomputable def EverythingLeftCorrected132.to131 (H : EverythingLeftCorrected132) :
    EverythingLeftCorrected131 where
  A_density_limit := AFiniteDensityLimit_from_margin132 H.theta_logsq_remainder H.A_positive_margin
  theta_logsq_remainder := H.theta_logsq_remainder
  sparse_good_prime_count := H.sparse_good_prime_count
  harman_bad_density := H.harman_bad_density
  large_sieve := H.large_sieve
  large_modulus_weil := H.large_modulus_weil

theorem candidate_main_from_corrected_endgame132 (H : EverythingLeftCorrected132) : MainStatement :=
  candidate_main_from_corrected_endgame131 H.to131

theorem positive_lower_density_from_corrected_endgame132 (H : EverythingLeftCorrected132) :
    PositiveLowerDensity D6 := positive_lower_density_from_corrected_endgame131 H.to131

/-! ### G. Focused verification checkpoints; no new unconditional main claim -/
-- Historical audit output (142): #print axioms proportion_mono132
-- Historical audit output (142): #print axioms hasDensity_nonneg132
-- Historical audit output (142): #print axioms density_le_add132
-- Historical audit output (142): #print axioms density_mono132
-- Historical audit output (142): #print axioms density_gap_le132
-- Historical audit output (142): #print axioms antitone_values_inf132
-- Historical audit output (142): #print axioms hasDensity_of_upper_approximations132
-- Historical audit output (142): #print axioms periodic_shift_mul132
-- Historical audit output (142): #print axioms periodic_block_sum132
-- Historical audit output (142): #print axioms periodic_sum_error132
-- Historical audit output (142): #print axioms periodic_predicate_hasDensity132
-- Historical audit output (142): #print axioms sievePeriod_pos132
-- Historical audit output (142): #print axioms q_dvd_sievePeriod132
-- Historical audit output (142): #print axioms square_dvd_sievePeriod132
-- Historical audit output (142): #print axioms gcd_add_multiple132
-- Historical audit output (142): #print axioms dvd_add_multiple132
-- Historical audit output (142): #print axioms finiteTest_periodic132
-- Historical audit output (142): #print axioms finiteSieve_hasDensity132
-- Historical audit output (142): #print axioms finiteSieve_antitone132
-- Historical audit output (142): #print axioms Afinite_subset_finiteSieve132
-- Historical audit output (142): #print axioms inverse_square_step132
-- Historical audit output (142): #print axioms inverse_square_tail_finite132
-- Historical audit output (142): #print axioms finiteSieve_difference_square_witness132
-- Historical audit output (142): #print axioms finiteSieve_square_tail132
-- Historical audit output (142): #print axioms Afinite_hasDensity132
-- Historical audit output (142): #print axioms AfiniteDensity_bracket132
-- Historical audit output (142): #print axioms Afinite_antitone132
-- Historical audit output (142): #print axioms AfiniteDensity_antitone132
-- Historical audit output (142): #print axioms AfiniteDensity_converges132
-- Historical audit output (142): #print axioms A_hasDensity_from_theta132
-- Historical audit output (142): #print axioms ADensity_finite_lower_bound132
-- Historical audit output (142): #print axioms ADensity_pos_of_finite_margin132
-- Historical audit output (142): #print axioms AFiniteDensityLimit_from_margin132
-- Historical audit output (142): #print axioms EverythingLeftCorrected132.to131
-- Historical audit output (142): #print axioms candidate_main_from_corrected_endgame132
-- Historical audit output (142): #print axioms positive_lower_density_from_corrected_endgame132
-- Historical audit output (142): #check Afinite_hasDensity132
-- Historical audit output (142): #check A_hasDensity_from_theta132
-- Historical audit output (142): #check candidate_main_from_corrected_endgame132
-- Historical audit output (142): #print EverythingLeftCorrected132
-- Frozen historical output: #eval "REPAIR 132 DENSITY CHECKPOINT: new positivity section follows"

end RemainingAnalytic132

/-! ## 133. Positive A-density from theta, without a finite-count witness

The six compilation failures reported for Repair 132 have been edited in place.
This section supplies a new mathematical positivity argument. Numbers coprime
to B! pass the finite sieve with K=B. Euler's totient formula and a telescoping
product with the composite 4 omitted give density at least 4/(3B), for B>=4.
The squarefree tail costs at most 1/B, while the omitted-gcd tail is eventually
less than 1/(6B). This constructs the previously external positive margin.

Verification status: these are new, locally UNCOMPILED proof scripts. They do
not prove the remaining theta, sparse-prime, Harman, large-sieve or Weil inputs.
No contradiction from a historical inconsistent input record is used.
-/
namespace RemainingAnalytic133

open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic47 RemainingAnalytic127
open RemainingAnalytic130 RemainingAnalytic131 RemainingAnalytic132

/-! ### A. A polynomial lower bound for the rough-number density -/

noncomputable def eulerFactor133 (k : ℕ) : ℝ := 1 - 1 / (k : ℝ)

theorem eulerFactor_bounds133 {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ eulerFactor133 k ∧ eulerFactor133 k ≤ 1 := by
  have hkp : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hrec : (1 : ℝ) / (k : ℝ) ≤ 1 := (div_le_one hkp).mpr hk1
  have hrec0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  unfold eulerFactor133
  exact ⟨by linarith, by linarith⟩

/-- Inserting additional factors in [0,1] can only decrease a product.
This proof does not depend on the changing ordered-product subset API. -/
theorem product_subset_lower133 (s t : Finset ℕ) (f : ℕ → ℝ)
    (hst : s ⊆ t) (hf : ∀ k ∈ t, 0 ≤ f k ∧ f k ≤ 1) :
    (∏ k ∈ t, f k) ≤ ∏ k ∈ s, f k := by
  classical
  have hfilter : t.filter (fun k => k ∈ s) = s := by
    ext k
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hst h, h⟩⟩
  calc
    (∏ k ∈ t, f k) ≤ ∏ k ∈ t, (if k ∈ s then f k else 1) := by
      -- Real multiplication is monotone only with a nonnegative factor.
      -- Prove the needed finite-product comparison directly instead of asking
      -- for the globally ordered-monoid instance `MulLeftMono ℝ`.
      have hmono : ∀ u : Finset ℕ, ∀ g : ℕ → ℝ,
          (∀ k ∈ u, 0 ≤ f k) → (∀ k ∈ u, f k ≤ g k) →
          (∏ k ∈ u, f k) ≤ ∏ k ∈ u, g k := by
        intro u
        induction u using Finset.induction_on with
        | empty =>
            intro g h0 hle
            simp
        | @insert a u ha ih =>
            intro g h0 hle
            have hu0 : ∀ k ∈ u, 0 ≤ f k :=
              fun k hk => h0 k (Finset.mem_insert_of_mem hk)
            have hule : ∀ k ∈ u, f k ≤ g k :=
              fun k hk => hle k (Finset.mem_insert_of_mem hk)
            have ha0 := h0 a (Finset.mem_insert_self a u)
            have hale := hle a (Finset.mem_insert_self a u)
            rw [Finset.prod_insert ha, Finset.prod_insert ha]
            exact mul_le_mul hale (ih g hu0 hule)
              (Finset.prod_nonneg hu0) (le_trans ha0 hale)
      apply hmono t (fun k => if k ∈ s then f k else 1)
      · intro k hk
        exact (hf k hk).1
      · intro k hk
        by_cases hks : k ∈ s
        · simp only [hks, ite_true, le_refl]
        · simpa only [hks, ite_false] using (hf k hk).2
    _ = ∏ k ∈ s, f k := by
      rw [← Finset.prod_filter, hfilter]

/-- Omitting just the composite 4 makes the elementary telescope strictly
larger than 1/B. This spare factor will pay for the squarefree tail. -/
theorem all_except_four_product133 (n : ℕ) :
    (∏ k ∈ (Finset.Icc 2 (n + 4)).erase 4, eulerFactor133 k) =
      4 / (3 * ((n + 4 : ℕ) : ℝ)) := by
  classical
  induction n with
  | zero =>
      have hset : (Finset.Icc 2 4).erase 4 = ({2, 3} : Finset ℕ) := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
      norm_num [hset, eulerFactor133]
  | succ n ih =>
      have hset : (Finset.Icc 2 (n + 1 + 4)).erase 4 =
          insert (n + 5) ((Finset.Icc 2 (n + 4)).erase 4) := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n + 5 ∉ (Finset.Icc 2 (n + 4)).erase 4 := by
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      rw [hset, Finset.prod_insert hnot, ih]
      rw [show n + 1 + 4 = n + 5 by omega]
      unfold eulerFactor133
      push_cast
      have hn4 : (n : ℝ) + 4 ≠ 0 := by positivity
      have hn5 : (n : ℝ) + 5 ≠ 0 := by positivity
      field_simp [hn4, hn5] <;> ring

/-- All prime divisors of B! belong to [2,B], and none is the composite 4. -/
theorem factorial_primeFactors_subset133 (B : ℕ) :
    B.factorial.primeFactors ⊆ (Finset.Icc 2 B).erase 4 := by
  intro p hp
  have hdata := Nat.mem_primeFactors.mp hp
  have hpp : p.Prime := hdata.1
  have hpB : p ≤ B := (Nat.Prime.dvd_factorial hpp).mp hdata.2.1
  have hp4 : p ≠ 4 := by
    intro heq
    have hfour : Nat.Prime 4 := by simpa only [heq] using hpp
    norm_num at hfour
  exact Finset.mem_erase.mpr ⟨hp4, Finset.mem_Icc.mpr ⟨hpp.two_le, hpB⟩⟩

/-- Euler's existing rational product identity, transported to real numbers. -/
theorem totient_ratio_product133 {M : ℕ} (hM : 0 < M) :
    (M.totient : ℝ) / (M : ℝ) =
      ∏ p ∈ M.primeFactors, eulerFactor133 p := by
  have hcast := congrArg (fun z : ℚ => (z : ℝ)) (Nat.totient_eq_mul_prod_factors M)
  push_cast at hcast
  have hreal : (M.totient : ℝ) =
      (M : ℝ) * (∏ p ∈ M.primeFactors, eulerFactor133 p) := by
    simpa only [eulerFactor133, one_div] using hcast
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  rw [hreal]
  field_simp [hM0] <;> ring

/-- A completely elementary lower bound, with no prime-distribution input. -/
theorem factorial_totient_ratio_lower133 {B : ℕ} (hB : 4 ≤ B) :
    4 / (3 * (B : ℝ)) ≤ (B.factorial.totient : ℝ) / (B.factorial : ℝ) := by
  rw [totient_ratio_product133 (Nat.factorial_pos B)]
  have hprod := product_subset_lower133 B.factorial.primeFactors
    ((Finset.Icc 2 B).erase 4) eulerFactor133 (factorial_primeFactors_subset133 B)
    (fun k hk => eulerFactor_bounds133 (Finset.mem_Icc.mp (Finset.mem_erase.mp hk).2).1)
  have htel := all_except_four_product133 (B - 4)
  have hidx : B - 4 + 4 = B := by omega
  rw [hidx] at htel
  rw [htel] at hprod
  exact hprod

/-! ### B. Coprime residues have their actual totient density -/

/-- Count one shifted complete residue block. Positivity of m does not alter
this block count because the block starts at 1, including the endpoint M. -/
theorem coprime_block_sum133 (M : ℕ) :
    (∑ i ∈ Finset.range M, if M.Coprime (i + 1) then (1 : ℝ) else 0) =
      (M.totient : ℝ) := by
  classical
  have hshift := sum_range_succ_eq_Icc127
    (fun m : ℕ => if M.Coprime m then (1 : ℝ) else 0) M
  have hinterval : Finset.Icc 1 M = Finset.Ico 1 (1 + M) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  calc
    (∑ i ∈ Finset.range M, if M.Coprime (i + 1) then (1 : ℝ) else 0) =
        ∑ m ∈ Finset.Icc 1 M, (if M.Coprime m then (1 : ℝ) else 0) := hshift
    _ = (M.totient : ℝ) := by
      rw [hinterval, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.filter_coprime_Ico_eq_totient]

theorem coprime_hasDensity133 {M : ℕ} (hM : 0 < M) :
    HasDensity {m : ℕ | 1 ≤ m ∧ M.Coprime m}
      ((M.totient : ℝ) / (M : ℝ)) := by
  classical
  -- Work with one explicitly fixed indicator, rather than transporting between
  -- elaborator-generated conditionals under HasDensity.
  let f : ℕ → ℝ := fun i => if M.Coprime (i + 1) then 1 else 0
  have hf : ∀ i : ℕ, 0 ≤ f i ∧ f i ≤ 1 := by
    intro i
    dsimp only [f]
    split_ifs <;> norm_num
  have hper : ∀ i : ℕ, f (i + M) = f i := by
    intro i
    have hcop : M.Coprime (i + 1 + M) ↔ M.Coprime (i + 1) :=
      Nat.coprime_add_self_right
    have hidx : i + M + 1 = i + 1 + M := by omega
    simp only [f, hidx, hcop]
  have hblock : (∑ i ∈ Finset.range M, f i) = (M.totient : ℝ) := by
    exact coprime_block_sum133 M
  have hcount : ∀ X : ℕ,
      (prefixCount {m : ℕ | 1 ≤ m ∧ M.Coprime m} X : ℝ) =
        ∑ i ∈ Finset.range X, f i := by
    intro X
    have hshift := sum_range_succ_eq_Icc127
      (fun m : ℕ => if M.Coprime m then (1 : ℝ) else 0) X
    -- Rewrite from the proved identity so that its own Decidable instance
    -- is retained. Do not restate its indicator with a new instDecidableAnd.
    rw [prefixCount_eq_indicator_sum127]
    calc
      _ = ∑ m ∈ Finset.Icc 1 X,
            (if M.Coprime m then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        by_cases hc : M.Coprime m
        · have hmS : m ∈ {m : ℕ | 1 ≤ m ∧ M.Coprime m} := ⟨hm1, hc⟩
          rw [if_pos hmS, if_pos hc]
        · have hmS : m ∉ {m : ℕ | 1 ≤ m ∧ M.Coprime m} :=
            fun h => hc h.2
          rw [if_neg hmS, if_neg hc]
      _ = ∑ i ∈ Finset.range X, f i := hshift.symm
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((M : ℝ) / ε)
  refine ⟨max N 1, ?_⟩
  intro X hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlarge : (M : ℝ) / ε < (X : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hXN)
  have hsmall : (M : ℝ) / (X : ℝ) < ε := by
    apply (div_lt_iff₀ hXp).mpr
    have hh := (div_lt_iff₀ hε).mp hlarge
    nlinarith only [hh]
  have hb := periodic_sum_error132 f M hM hper hf X
  rw [hblock] at hb
  have hid : (∑ i ∈ Finset.range X, f i) / (X : ℝ) -
      (M.totient : ℝ) / (M : ℝ) =
      ((∑ i ∈ Finset.range X, f i) -
        (X : ℝ) * ((M.totient : ℝ) / (M : ℝ))) / (X : ℝ) := by
    field_simp [ne_of_gt hXp] <;> ring
  unfold proportion
  rw [hcount, hid, abs_div, abs_of_pos hXp]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hb hXp.le) hsmall

/-- Rough integers satisfy every finite gcd condition and every small-square
condition. The two distinct restrictions are both checked here. -/
theorem coprime_factorial_subset_finiteSieve133 (B : ℕ) :
    {m : ℕ | 1 ≤ m ∧ B.factorial.Coprime m} ⊆ finiteSieve132 B B := by
  intro m hm
  refine ⟨hm.1, ?_, ?_⟩
  · intro a ha2 haB
    have hcop : m.Coprime (q a) := by
      apply Nat.coprime_of_dvd
      intro p hp hpm hpq
      have hpa := RemainingAnalytic65.primeDivisorQLe_proved65 a p hp hpq
      have hpF : p ∣ B.factorial := Nat.dvd_factorial hp.pos (le_trans hpa haB)
      have hone : p = 1 := Nat.eq_one_of_dvd_coprimes hm.2 hpF hpm
      exact hp.ne_one hone
    have hg : Nat.gcd m (q a) = 1 := hcop
    rw [hg, one_pow]
    exact Nat.one_le_iff_ne_zero.mpr (q_ne_zero a)
  · intro p hp hpB hsq
    have hpsq : p ∣ p ^ 2 := by rw [pow_two]; exact dvd_mul_right p p
    have hpm : p ∣ m := dvd_trans hpsq hsq
    have hpF : p ∣ B.factorial := Nat.dvd_factorial hp.pos hpB
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hm.2 hpF hpm)

/-- The finite periodic sieve has a polynomial, not exponentially tiny,
lower bound. In particular no enumeration of its enormous period is needed. -/
theorem finiteSieveDensity_diagonal_lower133 {B : ℕ} (hB : 4 ≤ B) :
    4 / (3 * (B : ℝ)) ≤ finiteSieveDensity132 B B := by
  have hdensity := density_mono132 (coprime_factorial_subset_finiteSieve133 B)
    (coprime_hasDensity133 (Nat.factorial_pos B)) (finiteSieve_hasDensity132 B B)
  exact le_trans (factorial_totient_ratio_lower133 hB) hdensity

/-- Even after imposing all squarefree conditions, a finite gcd level retains
at least 1/(3B) density. This theorem has no theta hypothesis. -/
theorem AfiniteDensity_polynomial_lower133 {B : ℕ} (hB : 4 ≤ B) :
    1 / (3 * (B : ℝ)) ≤ AfiniteDensity132 B := by
  have hfinite := finiteSieveDensity_diagonal_lower133 hB
  have hbracket := (AfiniteDensity_bracket132 B B (by omega)).2
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have hid : 4 / (3 * (B : ℝ)) - 1 / (B : ℝ) = 1 / (3 * (B : ℝ)) := by
    field_simp [hB0] <;> ring
  linarith only [hfinite, hbracket, hid]

/-! ### C. An explicit elementary threshold beats the exponential tail -/

noncomputable def geometricDenominator133 : ℝ := 1 - Real.exp (-(1 : ℝ) / 8)

theorem geometricDenominator_pos133 : 0 < geometricDenominator133 := by
  have hh := Real.exp_lt_exp.mpr (show -(1 : ℝ) / 8 < 0 by norm_num)
  rw [Real.exp_zero] at hh
  exact sub_pos.mpr hh

/-- A quadratic lower bound for exp suffices; no asymptotic theorem about
exponential decay is needed. The intentionally loose constant is explicit. -/
theorem exponential_tail_lt_sixth133 {B : ℕ} (hB : 1 ≤ B)
    (hscale : 1536 / geometricDenominator133 < (B : ℝ)) :
    Real.exp (-((B + 1 : ℕ) : ℝ) / 8) / geometricDenominator133 <
      1 / (6 * (B : ℝ)) := by
  have hb : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hc : 0 < geometricDenominator133 := geometricDenominator_pos133
  have hbc : 1536 < (B : ℝ) * geometricDenominator133 := (div_lt_iff₀ hc).mp hscale
  let w : ℝ := Real.exp (((B : ℝ) + 1) / 16)
  let z : ℝ := Real.exp (((B : ℝ) + 1) / 8)
  have hw : 0 < w := Real.exp_pos _
  have hz : 0 < z := Real.exp_pos _
  have htangent := Real.add_one_le_exp (((B : ℝ) + 1) / 16)
  have hbW : (B : ℝ) < 16 * w := by
    dsimp [w]
    linarith only [htangent]
  have hprodpos : 0 < (16 * w - (B : ℝ)) * (16 * w + (B : ℝ)) :=
    mul_pos (sub_pos.mpr hbW) (by positivity)
  have hwsquare : w * w = z := by
    dsimp [w, z]
    rw [← Real.exp_add]
    congr 1
    ring
  have hquad : (B : ℝ) ^ 2 < 256 * z := by
    nlinarith only [hprodpos, hwsquare]
  have hquadC := mul_lt_mul_of_pos_left hquad hc
  have hbcB := mul_lt_mul_of_pos_right hbc hb
  have hbig : 6 * (B : ℝ) < geometricDenominator133 * z := by
    nlinarith only [hquadC, hbcB]
  have hneg : -((B + 1 : ℕ) : ℝ) / 8 = -(((B : ℝ) + 1) / 8) := by
    push_cast
    ring
  have heq : Real.exp (-((B + 1 : ℕ) : ℝ) / 8) / geometricDenominator133 =
      1 / (geometricDenominator133 * z) := by
    rw [hneg, Real.exp_neg]
    change z⁻¹ / geometricDenominator133 = 1 / (geometricDenominator133 * z)
    field_simp [ne_of_gt hz, ne_of_gt hc] <;> ring
  rw [heq]
  exact one_div_lt_one_div_of_lt (by positivity) hbig

/-- All scale constraints are met by one fixed B. There is no computational
search over residues and no unproved existence-of-margin input. -/
theorem positivity_scale_exists133 (HT : ThetaLogSqRemainder127) :
    ∃ B : ℕ, thetaTailCutoff132 HT ≤ B ∧ 4 ≤ B ∧
      1536 / geometricDenominator133 < (B : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1536 / geometricDenominator133)
  let B := max (thetaTailCutoff132 HT) (max N 4)
  have hNB : N ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨B, le_max_left _ _, le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  exact lt_of_lt_of_le hN (by exact_mod_cast hNB)

/-- Construct the exact formerly external finite positive-margin proposition.
Only the already-retained theta input is used. -/
theorem finitePositiveMargin_from_theta133 (HT : ThetaLogSqRemainder127) :
    FinitePositiveMargin132 HT := by
  obtain ⟨B, hBT, hB4, hscale⟩ := positivity_scale_exists133 HT
  have htail := exponential_tail_lt_sixth133 (by omega : 1 ≤ B) hscale
  have hfinite := finiteSieveDensity_diagonal_lower133 hB4
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have hBp : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hgap : (0 : ℝ) < 1 / (6 * (B : ℝ)) := by positivity
  have hid : 1 / (B : ℝ) + 1 / (6 * (B : ℝ)) + 1 / (6 * (B : ℝ)) =
      4 / (3 * (B : ℝ)) := by
    field_simp [hB0] <;> ring
  refine ⟨B, B, hBT, by omega, ?_⟩
  change 1 / (B : ℝ) + Real.exp (-((B + 1 : ℕ) : ℝ) / 8) /
    geometricDenominator133 < finiteSieveDensity132 B B
  linarith only [htail, hfinite, hgap, hid]

/-- A quantitative positive lower bound at any eligible scale B. -/
theorem ADensity_quantitative_lower133 (HT : ThetaLogSqRemainder127)
    {B : ℕ} (hBT : thetaTailCutoff132 HT ≤ B) (hB4 : 4 ≤ B)
    (hscale : 1536 / geometricDenominator133 < (B : ℝ)) :
    1 / (6 * (B : ℝ)) < ADensity132 := by
  have htail : ∀ X : ℕ, proportion (Afinite B \ A) X ≤
      Real.exp (-((B + 1 : ℕ) : ℝ) / 8) / geometricDenominator133 :=
    Classical.choose_spec (Afinite_tail_explicit131 HT) B hBT
  have hfinite := AfiniteDensity_polynomial_lower133 hB4
  have hgap := density_gap_le132 (A_subset_Afinite B) (A_hasDensity_from_theta132 HT)
    (Afinite_hasDensity132 B) htail
  have he := exponential_tail_lt_sixth133 (by omega : 1 ≤ B) hscale
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have hid : 1 / (3 * (B : ℝ)) =
      1 / (6 * (B : ℝ)) + 1 / (6 * (B : ℝ)) := by
    field_simp [hB0] <;> ring
  linarith only [hfinite, hgap, he, hid]

/-- Positivity is now derived, not assumed separately from density existence. -/
theorem ADensity_pos_from_theta133 (HT : ThetaLogSqRemainder127) : 0 < ADensity132 :=
  ADensity_pos_of_finite_margin132 HT (finitePositiveMargin_from_theta133 HT)

noncomputable def AFiniteDensityLimit_from_theta133 (HT : ThetaLogSqRemainder127) :
    RemainingAnalytic21.AFiniteDensityLimit :=
  AFiniteDensityLimit_from_margin132 HT (finitePositiveMargin_from_theta133 HT)

/-! ### D. Five remaining analytic inputs; no A-density field or witness -/

structure EverythingLeftCorrected133 where
  theta_logsq_remainder : ThetaLogSqRemainder127
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  large_sieve : RemainingAnalytic92.ClassicalPrimeAdditiveLargeSieve92
  large_modulus_weil : LargeModulusLinearProductWeil127

noncomputable def EverythingLeftCorrected133.to132 (H : EverythingLeftCorrected133) :
    EverythingLeftCorrected132 where
  theta_logsq_remainder := H.theta_logsq_remainder
  A_positive_margin := finitePositiveMargin_from_theta133 H.theta_logsq_remainder
  sparse_good_prime_count := H.sparse_good_prime_count
  harman_bad_density := H.harman_bad_density
  large_sieve := H.large_sieve
  large_modulus_weil := H.large_modulus_weil

theorem candidate_main_from_corrected_endgame133 (H : EverythingLeftCorrected133) : MainStatement :=
  candidate_main_from_corrected_endgame132 H.to132

theorem positive_lower_density_from_corrected_endgame133 (H : EverythingLeftCorrected133) :
    PositiveLowerDensity D6 := positive_lower_density_from_corrected_endgame132 H.to132

/-! The historical regression lemmas and each mathematical branch are checked
separately. The final theorem remains a function FROM the five input proofs. -/
-- Historical audit output (142): #print axioms prefixCount_pos_of_member133
-- Historical audit output (142): #print axioms q_two130
-- Historical audit output (142): #print axioms not_legacy_exact_cofactor_count130
-- Historical audit output (142): #print axioms prefixCount_real_le_sum_of_cover131
-- Historical audit output (142): #print axioms prefixCount_multiples_le_natDiv131
-- Historical audit output (142): #print axioms squarefree_divisor_card_le_pow131
-- Historical audit output (142): #print axioms periodic_predicate_hasDensity132
-- Historical audit output (142): #print axioms AUniformTail_from_theta131
-- Historical audit output (142): #print axioms Afinite_hasDensity132
-- Historical audit output (142): #print axioms A_hasDensity_from_theta132
-- Historical audit output (142): #print axioms eulerFactor_bounds133
-- Historical audit output (142): #print axioms product_subset_lower133
-- Historical audit output (142): #print axioms all_except_four_product133
-- Historical audit output (142): #print axioms factorial_primeFactors_subset133
-- Historical audit output (142): #print axioms totient_ratio_product133
-- Historical audit output (142): #print axioms factorial_totient_ratio_lower133
-- Historical audit output (142): #print axioms coprime_block_sum133
-- Historical audit output (142): #print axioms coprime_hasDensity133
-- Historical audit output (142): #print axioms coprime_factorial_subset_finiteSieve133
-- Historical audit output (142): #print axioms finiteSieveDensity_diagonal_lower133
-- Historical audit output (142): #print axioms AfiniteDensity_polynomial_lower133
-- Historical audit output (142): #print axioms geometricDenominator_pos133
-- Historical audit output (142): #print axioms exponential_tail_lt_sixth133
-- Historical audit output (142): #print axioms positivity_scale_exists133
-- Historical audit output (142): #print axioms finitePositiveMargin_from_theta133
-- Historical audit output (142): #print axioms ADensity_quantitative_lower133
-- Historical audit output (142): #print axioms ADensity_pos_from_theta133
-- Historical audit output (142): #print axioms AFiniteDensityLimit_from_theta133
-- Historical audit output (142): #print axioms EverythingLeftCorrected133.to132
-- Historical audit output (142): #print axioms candidate_main_from_corrected_endgame133
-- Historical audit output (142): #print axioms positive_lower_density_from_corrected_endgame133
-- Historical audit output (142): #check factorial_totient_ratio_lower133
-- Historical audit output (142): #check finitePositiveMargin_from_theta133
-- Historical audit output (142): #check AFiniteDensityLimit_from_theta133
-- Historical audit output (142): #check candidate_main_from_corrected_endgame133
-- Historical audit output (142): #print EverythingLeftCorrected133
-- Frozen historical output: #eval "REPAIR 133 POSITIVITY CHECKPOINT: PNT adapter section follows"

end RemainingAnalytic133

/-! ## 134. Standard Chebyshev functions and a quantitative PNT adapter

The two Repair-133 compilation failures are repaired in their original bodies.
This section makes an independently useful analytic connection: an error-term
PNT for Mathlib's Chebyshev.psi supplies the precise theta hypothesis used by
this project.  The psi-theta error and both logarithmic decay estimates are
proved using existing Mathlib theorems, rather than introduced as assumptions.

The standalone file DOES NOT import or assert the external PNT theorem.  The
optional PNT+ hook must be built in a compatible dependency environment and its
axiom report checked before the theta input can be counted as discharged.
All new scripts in this release are locally uncompiled.
-/
namespace RemainingAnalytic134

open scoped BigOperators
open Filter Asymptotics
open RemainingAnalytic127 RemainingAnalytic130 RemainingAnalytic131
open RemainingAnalytic132 RemainingAnalytic133

/-! ### A. Identify the project's prime-log sum with the standard function -/

/-- Exact identity, including the natural floor and the lower endpoint. -/
theorem thetaPrefix_eq_mathlib134 (n : ℕ) :
    thetaPrefix127 n = Chebyshev.theta (n : ℝ) := by
  classical
  have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [thetaPrefix_eq_primeSum130]
  simp only [Chebyshev.theta, Nat.floor_natCast, hI]

/-- The contribution of non-prime prime powers is controlled by Mathlib's
explicit Chebyshev comparison, with no prime-distribution hypothesis. -/
theorem psi_thetaPrefix_gap134 {n : ℕ} (hn : 1 ≤ n) :
    |Chebyshev.psi (n : ℝ) - thetaPrefix127 n| ≤
      2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  rw [thetaPrefix_eq_mathlib134]
  exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hn)

/-! ### B. Absorb the logarithmic weights in the two error terms -/

/-- The exp(-c (log x)^(1/10)) error remains small after multiplication
by (log x)^2.  This is a calculus theorem, not a PNT assumption. -/
theorem medium_weight_eventually_small134
    (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) *
        (Real.log x) ^ 2 < ε := by
  have hroot : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
  have hlim :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (20 : ℝ) c hc).comp hroot
  have hsmall := (tendsto_order.mp hlim).2 ε hε
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hxsmall hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpower : ((Real.log x) ^ ((1 : ℝ) / 10)) ^ (20 : ℝ) =
      (Real.log x) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul hlog0]
    norm_num
  change ((Real.log x) ^ ((1 : ℝ) / 10)) ^ (20 : ℝ) *
    Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < ε at hxsmall
  rw [hpower] at hxsmall
  simpa only [mul_comm] using hxsmall

/-- Even the elementary O(sqrt(x) log x) prime-power error, multiplied
by log(x)^2, is o(x). -/
theorem prime_power_weight_eventually_small134
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (2 * Real.sqrt x * Real.log x) * (Real.log x) ^ 2 ≤ ε * x := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
      (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).bound
        (show 0 < ε / 2 by linarith)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hxsmall hx1
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogNorm : ‖(Real.log x) ^ (3 : ℝ)‖ = (Real.log x) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 3)]
  have hsqrtNorm : ‖x ^ ((1 : ℝ) / 2)‖ = Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg x)]
  change ‖(Real.log x) ^ (3 : ℝ)‖ ≤
    (ε / 2) * ‖x ^ ((1 : ℝ) / 2)‖ at hxsmall
  rw [hlogNorm, hsqrtNorm] at hxsmall
  calc
    (2 * Real.sqrt x * Real.log x) * (Real.log x) ^ 2 =
        (2 * Real.sqrt x) * (Real.log x) ^ 3 := by ring
    _ ≤ (2 * Real.sqrt x) * ((ε / 2) * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hxsmall (by positivity)
    _ = ε * (Real.sqrt x) ^ 2 := by ring
    _ = ε * x := by rw [Real.sq_sqrt hx0]

/-- The actual standard psi-theta difference satisfies the weighted o(x)
estimate; all prime-power bookkeeping has now been discharged. -/
theorem psi_theta_logsq_eventually_small134
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - Chebyshev.theta x| * (Real.log x) ^ 2 ≤ ε * x := by
  filter_upwards [prime_power_weight_eventually_small134 ε hε,
    eventually_ge_atTop (1 : ℝ)] with x hxsmall hx1
  have hbound := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  exact le_trans
    (mul_le_mul_of_nonneg_right hbound (sq_nonneg (Real.log x))) hxsmall

/-! ### C. A direct interface for the external error-term PNT

This proposition intentionally matches the statement of `MediumPNT` in the
PNT+ project: Chebyshev.psi(x) - x = O(x exp(-c (log x)^(1/10))), c > 0.
It is an INPUT here, not an axiom or a theorem that has been silently imported.
-/

def PsiMediumPNT134 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))

/-- Full conversion of a standard quantitative PNT for psi into the exact
natural-endpoint, log-squared theta statement used by the project. -/
theorem thetaLogSqRemainder_from_mediumPNT134
    (HP : PsiMediumPNT134) : ThetaLogSqRemainder127 := by
  obtain ⟨c, hc, hPNT⟩ := HP
  obtain ⟨C, hC, hbound⟩ := Asymptotics.isBigO_iff'.mp hPNT
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hweight := medium_weight_eventually_small134 c hc (ε / (2 * C)) (by positivity)
  have hgap := psi_theta_logsq_eventually_small134 (ε / 2) hε2
  have hreal : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| * (Real.log x) ^ 2 ≤ ε * x := by
    filter_upwards [hbound, hweight, hgap, eventually_ge_atTop (1 : ℝ)]
      with x hxPNT hxweight hxgap hx1
    have hx0 : 0 ≤ x := by linarith
    have hlogSq0 : 0 ≤ (Real.log x) ^ 2 := sq_nonneg _
    have hright0 : 0 ≤ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by positivity
    have hxPNT' : |Chebyshev.psi x - x| ≤
        C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hright0] using hxPNT
    have hCweight := mul_le_mul_of_nonneg_left hxweight.le hC.le
    have hcancel : C * (ε / (2 * C)) = ε / 2 := by
      field_simp [ne_of_gt hC] <;> ring
    rw [hcancel] at hCweight
    have hmain : |Chebyshev.psi x - x| * (Real.log x) ^ 2 ≤ (ε / 2) * x := by
      calc
        |Chebyshev.psi x - x| * (Real.log x) ^ 2 ≤
            (C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))) *
              (Real.log x) ^ 2 := mul_le_mul_of_nonneg_right hxPNT' hlogSq0
        _ = x * (C * (Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) *
              (Real.log x) ^ 2)) := by ring
        _ ≤ x * (ε / 2) := mul_le_mul_of_nonneg_left hCweight hx0
        _ = (ε / 2) * x := by ring
    have htri : |Chebyshev.theta x - x| ≤
        |Chebyshev.psi x - Chebyshev.theta x| + |Chebyshev.psi x - x| := by
      have hh := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
      simpa only [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] using hh
    have hweighted := mul_le_mul_of_nonneg_right htri hlogSq0
    nlinarith only [hweighted, hxgap, hmain]
  have hnat : ∀ᶠ n : ℕ in atTop,
      |Chebyshev.theta (n : ℝ) - (n : ℝ)| * (Real.log (n : ℝ)) ^ 2 ≤ ε * (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually hreal
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnat
  refine ⟨N, ?_⟩
  intro n hn
  rw [thetaPrefix_eq_mathlib134]
  exact hN n hn

/-- A natural density and its strictly positive value follow from the external
psi PNT alone.  The positive constant is the actual density constructed in 132. -/
theorem A_positive_density_from_mediumPNT134
    (HP : PsiMediumPNT134) : HasDensity A ADensity132 ∧ 0 < ADensity132 := by
  have HT := thetaLogSqRemainder_from_mediumPNT134 HP
  exact ⟨A_hasDensity_from_theta132 HT, ADensity_pos_from_theta133 HT⟩

/-- Four NON-PNT analytic obligations.  This record is not by itself sufficient
for the main theorem: the standard PNT input remains a separate explicit
argument until a compatible external theorem has actually been connected. -/
structure NonPNTInputs134 where
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  large_sieve : RemainingAnalytic92.ClassicalPrimeAdditiveLargeSieve92
  large_modulus_weil : LargeModulusLinearProductWeil127

/-- Five total inputs remain in the standalone file: HP plus these four fields.
No assumption count is reduced merely by changing the record layout. -/
noncomputable def NonPNTInputs134.to133
    (H : NonPNTInputs134) (HP : PsiMediumPNT134) : EverythingLeftCorrected133 where
  theta_logsq_remainder := thetaLogSqRemainder_from_mediumPNT134 HP
  sparse_good_prime_count := H.sparse_good_prime_count
  harman_bad_density := H.harman_bad_density
  large_sieve := H.large_sieve
  large_modulus_weil := H.large_modulus_weil

theorem candidate_main_from_mediumPNT134
    (HP : PsiMediumPNT134) (H : NonPNTInputs134) : MainStatement :=
  candidate_main_from_corrected_endgame133 (H.to133 HP)

theorem positive_lower_density_from_mediumPNT134
    (HP : PsiMediumPNT134) (H : NonPNTInputs134) : PositiveLowerDensity D6 :=
  positive_lower_density_from_corrected_endgame133 (H.to133 HP)

-- Historical audit output (142): #print axioms product_subset_lower133
-- Historical audit output (142): #print axioms coprime_hasDensity133
-- Historical audit output (142): #print axioms factorial_totient_ratio_lower133
-- Historical audit output (142): #print axioms AfiniteDensity_polynomial_lower133
-- Historical audit output (142): #print axioms ADensity_pos_from_theta133
-- Historical audit output (142): #print axioms candidate_main_from_corrected_endgame133
-- Historical audit output (142): #print axioms thetaPrefix_eq_mathlib134
-- Historical audit output (142): #print axioms psi_thetaPrefix_gap134
-- Historical audit output (142): #print axioms medium_weight_eventually_small134
-- Historical audit output (142): #print axioms prime_power_weight_eventually_small134
-- Historical audit output (142): #print axioms psi_theta_logsq_eventually_small134
-- Historical audit output (142): #print axioms thetaLogSqRemainder_from_mediumPNT134
-- Historical audit output (142): #print axioms A_positive_density_from_mediumPNT134
-- Historical audit output (142): #print axioms NonPNTInputs134.to133
-- Historical audit output (142): #print axioms candidate_main_from_mediumPNT134
-- Historical audit output (142): #print axioms positive_lower_density_from_mediumPNT134
-- Historical audit output (142): #check thetaLogSqRemainder_from_mediumPNT134
-- Historical audit output (142): #check candidate_main_from_mediumPNT134
-- Historical audit output (142): #print PsiMediumPNT134
-- Historical audit output (142): #print NonPNTInputs134
-- Frozen historical output: #eval "REPAIR 134 CHECKPOINT: included large-sieve proof and specialization follow"

end RemainingAnalytic134




/-!
## 135A. Included additive-large-sieve proof bodies

ADAPTED THIRD-PARTY SOURCE, not a new analytic hypothesis.
Source repository: https://github.com/ericlisg/erdos768-lean
Sources inspected 2026-09-23:
  RequestProject/LargeSieve.lean
  RequestProject/LargeSieveMult.lean (only additive/Farey/casting lemmas)
License: Apache-2.0. The full license is reproduced at the end of this file.
Attribution: ericlisg/erdos768-lean contributors.

Changes for this distribution: namespace changed to ImportedLargeSieve135;
imports absorbed into the host's import Mathlib; comments condensed; only the
additive dependency closure retained. No multiplicative-sieve or PNT module is
imported. The proofs below must be rechecked against the user's Mathlib version.
They are NOT claimed to have compiled in this preparation environment.
-/
namespace ImportedLargeSieve135

open scoped Classical BigOperators Real
open Finset Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 4000000

/-- The additive character e(t)=exp(2*pi*i*t). -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- A finite exponential sum with arbitrary complex coefficients. -/
noncomputable def S (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * e (n * θ)

lemma integral_e_int (k : ℤ) :
    (∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) * θ))
      = if k = 0 then 1 else 0 := by
  have := @integral_exp_mul_complex 0 1 (2 * Real.pi * Complex.I * k)
  simp_all +decide [mul_comm, mul_left_comm]
  by_cases hk : k = 0 <;> simp_all +decide
  exact sub_eq_zero_of_eq (Complex.exp_eq_one_iff.mpr ⟨k, by ring⟩)

lemma periodic_int (h : ℝ → ℝ) (hper : ∀ x, h (x + 1) = h x) (n : ℤ) (y : ℝ) :
    h (y + n) = h y := by
  simpa using Function.Periodic.int_mul hper n y

/-- Integrals over disjoint-mod-one intervals fit in a single period. -/
lemma periodic_cover_bound (h : ℝ → ℝ) (hper : ∀ x, h (x + 1) = h x)
    (hcont : Continuous h) (hnn : ∀ x, 0 ≤ h x)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (c : Fin R → ℝ)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |c i - c j - (k : ℝ)|) :
    ∑ r : Fin R, (∫ y in (c r - δ/2)..(c r + δ/2), h y) ≤
      ∫ y in (0:ℝ)..1, h y := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ i : Fin R, ∃ m : ℤ,
      a ≤ c i - δ / 2 - m ∧ c i - δ / 2 - m < a + 1 ∧
        c i + δ / 2 - m ≤ a + 1 := by
    by_cases hR : R = 0
    · aesop
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin R, ∀ i : Fin R, ∃ m : ℤ,
          c i - δ / 2 - m ≥ c i₀ - δ / 2 ∧
            c i - δ / 2 - m < c i₀ - δ / 2 + 1 := by
        obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin R, ∀ i : Fin R,
            c i - δ / 2 - ⌊c i - δ / 2⌋ ≥ c i₀ - δ / 2 - ⌊c i₀ - δ / 2⌋ := by
          simpa using Finset.exists_min_image Finset.univ
            (fun i => c i - δ / 2 - ⌊c i - δ / 2⌋)
              ⟨⟨0, Nat.pos_of_ne_zero hR⟩, Finset.mem_univ _⟩
        use i₀
        intro i
        use ⌊c i - δ / 2⌋ - ⌊c i₀ - δ / 2⌋
        constructor <;> push_cast <;>
          linarith [hi₀ i, Int.floor_le (c i - δ / 2),
            Int.lt_floor_add_one (c i - δ / 2), Int.floor_le (c i₀ - δ / 2),
            Int.lt_floor_add_one (c i₀ - δ / 2)]
      use c i₀ - δ / 2
      intro i
      obtain ⟨m, hm₁, hm₂⟩ := hi₀ i
      use m
      exact ⟨hm₁, hm₂, by
        by_cases hi : i = i₀ <;> simp_all +decide
        · rcases m with ⟨_ | m⟩ <;> norm_num at * <;> linarith
        · contrapose! hsp
          exact ⟨i, i₀, hi, m + 1, by
            rw [abs_lt]; constructor <;> push_cast <;> linarith⟩⟩
  choose m hm using ha
  have h_shift : ∀ i : Fin R,
      (∫ y in (c i - δ / 2)..(c i + δ / 2), h y) =
        ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y := by
    intro i
    convert intervalIntegral.integral_comp_sub_right _ _ using 2
    exact funext fun x => by
      simpa using Function.Periodic.int_mul hper (m i) (x - m i)
  have h_disjoint : ∀ i j : Fin R, i ≠ j →
      Disjoint (Set.Ico (c i - δ / 2 - m i) (c i + δ / 2 - m i))
        (Set.Ico (c j - δ / 2 - m j) (c j + δ / 2 - m j)) := by
    intros i j hij
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    specialize hsp i j hij (m i - m j)
    simp_all +decide
    grind
  have h_union :
      (∑ i : Fin R, ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y) ≤
        ∫ y in a..(a + 1), h y := by
    have h_union :
        (∑ i : Fin R, ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y) =
          ∫ y in (⋃ i : Fin R, Set.Ico (c i - δ / 2 - m i) (c i + δ / 2 - m i)), h y := by
      rw [MeasureTheory.integral_iUnion]
      · rw [tsum_fintype, Finset.sum_congr rfl]
        intros
        rw [← MeasureTheory.integral_Icc_eq_integral_Ico,
          MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le]
        linarith [hm ‹_›]
      · exact fun i => measurableSet_Ico
      · exact fun i j hij => h_disjoint i j hij
      · exact Continuous.integrableOn_Icc (by continuity) |>
          fun h => h.mono_set (Set.iUnion_subset fun i =>
            Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc (hm i |>.1) (hm i |>.2.2)))
    rw [h_union, intervalIntegral.integral_of_le (by linarith)]
    refine' MeasureTheory.setIntegral_mono_set _ _ _
    · exact hcont.integrableOn_Ioc
    · exact Filter.Eventually.of_forall hnn
    · filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
        (MeasureTheory.measure_singleton a)] with x hx using fun hx' => by
        rcases Set.mem_iUnion.mp hx' with ⟨i, hi⟩
        exact ⟨lt_of_le_of_ne (by linarith [hm i, hi.1]) (Ne.symm hx),
          by linarith [hm i, hi.2]⟩
  have h_periodic : (∫ y in a..a + 1, h y) = ∫ y in (0 : ℝ)..1, h y := by
    have h_split : (∫ y in a..a + 1, h y) =
        (∫ y in a..0, h y) + (∫ y in (0 : ℝ)..1, h y) +
          (∫ y in (1 : ℝ)..a + 1, h y) := by
      rw [intervalIntegral.integral_add_adjacent_intervals,
        intervalIntegral.integral_add_adjacent_intervals] <;>
          apply_rules [Continuous.intervalIntegrable, hcont]
    have h_periodic : (∫ y in a..0, h y) = ∫ y in (a + 1)..1, h y := by
      convert intervalIntegral.integral_comp_add_right _ 1 using 2 <;> norm_num [hper]
    rw [h_split, h_periodic, intervalIntegral.integral_symm]
    ring
  grind +splitImp

/-- Gallagher's sampling inequality, proved by local integration. -/
lemma gallagher_sampling (g g' : ℝ → ℝ)
    (hper : ∀ x, g (x + 1) = g x) (hnonneg : ∀ x, 0 ≤ g x)
    (hderiv : ∀ x, HasDerivAt g (g' x) x) (hcont : Continuous g')
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (x : Fin R → ℝ) (hmem : ∀ r, x r ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k : ℝ)|) :
    ∑ r : Fin R, g (x r) ≤
      δ⁻¹ * (∫ θ in (0:ℝ)..1, g θ) + ∫ θ in (0:ℝ)..1, |g' θ| := by
  have h_bound : ∀ r, g (x r) ≤
      (δ⁻¹ * ∫ θ in (x r - δ / 2)..(x r + δ / 2), g θ) +
        ∫ θ in (x r - δ / 2)..(x r + δ / 2), |g' θ| := by
    intro r
    have h_integral_bound : ∀ y ∈ Set.Icc (x r - δ / 2) (x r + δ / 2),
        g (x r) ≤ g y + ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t| := by
      intro y hy
      have h_integral_bound : |g (x r) - g y| ≤
          ∫ t in (min y (x r))..(max y (x r)), |g' t| := by
        cases le_total y (x r) <;> simp_all +decide [intervalIntegral.integral_of_le]
        · have h_integral_bound : |g (x r) - g y| = |∫ t in y..x r, g' t| := by
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
            · exact fun z _ => hderiv z
            · exact hcont.intervalIntegrable _ _
          rw [h_integral_bound, intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.norm_integral_le_integral_norm g'
        · have h_integral_bound : g y - g (x r) = ∫ t in (x r)..y, g' t := by
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
            · grind +splitImp
            · exact hcont.intervalIntegrable _ _
          rw [← intervalIntegral.integral_of_le (by linarith)]
          rw [abs_sub_comm]
          exact h_integral_bound ▸ by
            simpa only [intervalIntegral.integral_of_le (by linarith : x r ≤ y),
              Real.norm_eq_abs] using
              (MeasureTheory.norm_integral_le_integral_norm
                (μ := volume.restrict (Set.Ioc (x r) y)) g')
      generalize_proofs at *
      have h_integral_bound :
          (∫ t in (min y (x r))..(max y (x r)), |g' t|) ≤
            ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t| := by
        apply_rules [intervalIntegral.integral_mono_interval] <;> norm_num [hy.1, hy.2]
        · linarith
        · linarith
        · exact Filter.eventually_inf_principal.mpr
            (Filter.Eventually.of_forall fun x hx => abs_nonneg _)
        · exact hcont.abs.intervalIntegrable _ _
      generalize_proofs at *
      linarith [abs_le.mp ‹_›]
    generalize_proofs at *
    have h_sum_integral_bound :
        (∫ y in (x r - δ / 2)..(x r + δ / 2), g (x r)) ≤
          ∫ y in (x r - δ / 2)..(x r + δ / 2),
            (g y + ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t|) := by
      apply_rules [intervalIntegral.integral_mono_on]
      · linarith [hmem r |>.1, hmem r |>.2]
      · norm_num +zetaDelta at *
      · exact Continuous.intervalIntegrable
          (by exact Continuous.add (show Continuous g from
            continuous_iff_continuousAt.mpr fun x =>
              HasDerivAt.continuousAt (hderiv x)) continuous_const) _ _
    simp_all +decide
    rw [intervalIntegral.integral_add] at h_sum_integral_bound <;> norm_num at *
    · nlinarith [inv_mul_cancel_left₀ hδ0.ne' (∫ θ in x r - δ / 2..x r + δ / 2, g θ)]
    · exact Continuous.intervalIntegrable
        (by exact continuous_iff_continuousAt.mpr fun _ =>
          HasDerivAt.continuousAt (hderiv _)) _ _
  have h_sum_bound :
      (∑ r, (∫ θ in (x r - δ / 2)..(x r + δ / 2), g θ)) ≤
        (∫ θ in (0:ℝ)..1, g θ) ∧
      (∑ r, (∫ θ in (x r - δ / 2)..(x r + δ / 2), |g' θ|)) ≤
        ∫ θ in (0:ℝ)..1, |g' θ| := by
    apply And.intro
    · convert periodic_cover_bound g hper
        (show Continuous g from continuous_iff_continuousAt.mpr fun x =>
          HasDerivAt.continuousAt (hderiv x)) hnonneg δ hδ0 hδ1 R x hsp using 1
    · convert periodic_cover_bound (fun θ => |g' θ|) _ _ _ δ hδ0 hδ1 R x hsp using 1
      · intro θ
        have := hderiv θ
        have := this.deriv
        have := hderiv (θ + 1)
        have := this.deriv
        simp_all +decide
        rw [show g = fun x => g (x - 1) from funext fun x => by
          simpa using hper (x - 1)] at this
        erw [deriv_comp] at this <;>
          norm_num [hderiv _ |> HasDerivAt.differentiableAt] at *
        aesop
      · exact hcont.abs
      · exact fun _ => abs_nonneg _
  refine le_trans (Finset.sum_le_sum fun r _ => h_bound r) ?_
  simpa only [Finset.mul_sum _ _ _, Finset.sum_add_distrib] using
    add_le_add (mul_le_mul_of_nonneg_left h_sum_bound.1 <| inv_nonneg.2 hδ0.le) h_sum_bound.2

/-- Typed continuity helpers for the included analytic proof. -/
lemma continuous_e136 : Continuous e := by
  unfold e
  continuity

lemma continuous_frequency136 (n : ℕ) :
    Continuous (fun θ : ℝ => e ((n : ℝ) * θ)) :=
  continuous_e136.comp (continuous_const.mul continuous_id)

lemma continuous_S136 (N : ℕ) (a : ℕ → ℂ) : Continuous (S N a) := by
  unfold S
  exact continuous_finsetSum (Finset.Icc 1 N)
    (fun n hn => continuous_const.mul (continuous_frequency136 n))

/-- Parseval for finite exponential sums on one period. -/
lemma parseval_expsum (N : ℕ) (c : ℕ → ℂ) :
    (∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  have h_expand :
      (∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2) =
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (c m * (star (c n))) * (∫ θ in (0:ℝ)..1, e (m * θ) * (star (e (n * θ)))) := by
    have h_expand :
        (∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2) =
          ∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (c m * (star (c n))) * (e (m * θ) * (star (e (n * θ))))) := by
      have h_expand : ∀ θ : ℝ,
          ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 =
            ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              (c m * (star (c n))) * (e (m * θ) * (star (e (n * θ)))) := by
        intro θ
        have h_expand : ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 =
            (∑ m ∈ Finset.Icc 1 N, c m * e (m * θ)) *
              (∑ n ∈ Finset.Icc 1 N, star (c n) * star (e (n * θ))) := by
          have h_expand : ∀ z : ℂ, ‖z‖ ^ 2 = z * star z := by
            norm_num [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          convert h_expand _ using 2
          norm_num [Complex.ext_iff]
        exact h_expand.trans (by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by ring)
      convert intervalIntegral.integral_ofReal.symm
      aesop
    have hterm : ∀ m n : ℕ, Continuous (fun θ : ℝ =>
        (c m * star (c n)) *
          (e ((m : ℝ) * θ) * star (e ((n : ℝ) * θ)))) := by
      intro m n
      exact continuous_const.mul
        ((continuous_frequency136 m).mul (continuous_frequency136 n).star)
    have hrow : ∀ m : ℕ, IntervalIntegrable
        (fun θ : ℝ => ∑ n ∈ Finset.Icc 1 N,
          (c m * star (c n)) *
            (e ((m : ℝ) * θ) * star (e ((n : ℝ) * θ)))) volume 0 1 := by
      intro m
      exact (continuous_finsetSum (Finset.Icc 1 N)
        (fun n hn => hterm m n)).intervalIntegrable 0 1
    calc
      ((∫ θ in (0 : ℝ)..1,
          ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 : ℝ) : ℂ) =
          ∫ θ in (0 : ℝ)..1, ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (c m * star (c n)) *
              (e ((m : ℝ) * θ) * star (e ((n : ℝ) * θ))) := h_expand
      _ = ∑ m ∈ Finset.Icc 1 N, ∫ θ in (0 : ℝ)..1,
            ∑ n ∈ Finset.Icc 1 N, (c m * star (c n)) *
              (e ((m : ℝ) * θ) * star (e ((n : ℝ) * θ))) :=
        intervalIntegral.integral_finsetSum (fun m hm => hrow m)
      _ = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (c m * star (c n)) *
              (∫ θ in (0 : ℝ)..1, e ((m : ℝ) * θ) * star (e ((n : ℝ) * θ))) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [intervalIntegral.integral_finsetSum
          (fun n hn => (hterm m n).intervalIntegrable 0 1)]
        apply Finset.sum_congr rfl
        intro n hn
        exact intervalIntegral.integral_const_mul _ _
  have h_integral : ∀ m n : ℕ,
      (∫ θ in (0:ℝ)..1, e (m * θ) * (star (e (n * θ)))) = if m = n then 1 else 0 := by
    intros m n
    have h_integral_eval :
        (∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (m - n) * θ)) =
          if m = n then 1 else 0 := by
      convert integral_e_int (m - n) using 1
      aesop
      grind
    convert h_integral_eval using 3
    norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im, e]
    ring_nf
    exact ⟨by rw [Real.cos_sub], by rw [Real.sin_sub]; ring⟩
  rw [← Complex.ofReal_inj]
  simp_all +decide [Complex.mul_conj, Complex.normSq_eq_norm_sq]

noncomputable def Sderiv (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (2 * Real.pi * Complex.I * n) * e (n * θ)

noncomputable def gsq (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℝ := ‖S N a θ‖ ^ 2

noncomputable def gsqderiv (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℝ :=
  2 * ((starRingEnd ℂ) (S N a θ) * Sderiv N a θ).re

lemma S_periodic (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : S N a (θ + 1) = S N a θ := by
  unfold S
  unfold e
  congr
  ext
  ring_nf
  exact congrArg _ (Complex.exp_eq_exp_iff_exists_int.mpr ⟨‹ℕ›, by push_cast; ring⟩)

lemma hasDerivAt_S (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    HasDerivAt (S N a) (Sderiv N a θ) θ := by
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      HasDerivAt (fun y : ℝ => a n * e ((n : ℝ) * y))
        (a n * (2 * Real.pi * Complex.I * (n : ℂ)) * e ((n : ℝ) * θ)) θ := by
    intro n hn
    -- The field-specialized lemma already has the desired linear function
    -- and derivative. Keep its inferred instances instead of using simpa to
    -- transport a NormedAlgebra construction to the field's module structure.
    have hlin := hasDerivAt_const_mul (x := θ) (n : ℝ)
    have hphase := HasDerivAt.const_mul
      (2 * Real.pi * Complex.I : ℂ) hlin.ofReal_comp
    have hexp := (Complex.hasDerivAt_exp _).comp θ hphase
    have hprod := HasDerivAt.const_mul (a n) hexp
    simpa [e, mul_assoc, mul_left_comm, mul_comm] using hprod
  -- Expose the function before assembling its derivative. Full transparency
  -- is local to this exact step; it only unfolds the canonical instance
  -- wrappers and does not change the theorem or the kernel's checking rules.
  unfold S Sderiv
  with_unfolding_all exact HasDerivAt.fun_sum hterm

lemma continuous_Sderiv136 (N : ℕ) (a : ℕ → ℂ) : Continuous (Sderiv N a) := by
  unfold Sderiv
  exact continuous_finsetSum (Finset.Icc 1 N)
    (fun n hn => continuous_const.mul (continuous_frequency136 n))

lemma hasDerivAt_gsq (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    HasDerivAt (gsq N a) (gsqderiv N a θ) θ := by
  unfold gsq gsqderiv
  convert HasDerivAt.norm_sq (hasDerivAt_S N a θ) using 1
  norm_num [Complex.normSq, Complex.sq_norm]
  ring

lemma continuous_gsqderiv (N : ℕ) (a : ℕ → ℂ) : Continuous (gsqderiv N a) := by
  unfold gsqderiv
  refine' continuous_const.mul (Complex.continuous_re.comp _)
  refine' Continuous.mul _ _
  · exact Complex.continuous_conj.comp
      (by exact continuous_finset_sum _ fun _ _ =>
        Continuous.mul continuous_const (Complex.continuous_exp.comp (by continuity)))
  · exact continuous_finset_sum _ fun _ _ =>
      Continuous.mul (continuous_const.mul continuous_const) (Complex.continuous_exp.comp <| by continuity)

/-- Exact norm of a differentiated Fourier frequency. The coefficient is
first written as a nonnegative real scalar times the unit imaginary number. -/
lemma frequency_norm136 (n : ℕ) :
    ‖(2 * Real.pi * Complex.I * (n : ℂ))‖ = 2 * Real.pi * (n : ℝ) := by
  have heq : (2 * Real.pi * Complex.I * (n : ℂ)) =
      ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_I, mul_one]
  exact Complex.norm_of_nonneg (by positivity)

/-- Integral of the derivative is bounded by 4*pi*N times coefficient energy. -/
lemma deriv_integral_bound (N : ℕ) (a : ℕ → ℂ) :
    (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|) ≤
      4 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  by_cases hN : N = 0
  · simp +decide [hN, gsqderiv]
    unfold S Sderiv
    norm_num
  · have h_ineq : ∀ θ : ℝ, |gsqderiv N a θ| ≤
        (2 * Real.pi * N) * ‖S N a θ‖ ^ 2 +
          (1 / (2 * Real.pi * N)) * ‖Sderiv N a θ‖ ^ 2 := by
      intro θ
      have h_am_gm : |gsqderiv N a θ| ≤ 2 * ‖S N a θ‖ * ‖Sderiv N a θ‖ := by
        convert mul_le_mul_of_nonneg_left
          (Complex.abs_re_le_norm (starRingEnd ℂ (S N a θ) * Sderiv N a θ)) zero_le_two using 1
        ring_nf!
        · unfold gsqderiv
          norm_num [Complex.normSq, Complex.norm_def]
          ring
        · norm_num [mul_assoc]
      field_simp
      nlinarith [sq_nonneg (2 * Real.pi * N * ‖S N a θ‖ - ‖Sderiv N a θ‖),
        Real.pi_pos, show (0 : ℝ) < N * Real.pi by positivity]
    have hIleft : IntervalIntegrable
        (fun θ : ℝ => (2 * Real.pi * (N : ℝ)) * ‖S N a θ‖ ^ 2) volume 0 1 :=
      (continuous_const.mul ((continuous_S136 N a).norm.pow 2)).intervalIntegrable 0 1
    have hIright : IntervalIntegrable
        (fun θ : ℝ => (1 / (2 * Real.pi * (N : ℝ))) * ‖Sderiv N a θ‖ ^ 2) volume 0 1 :=
      (continuous_const.mul ((continuous_Sderiv136 N a).norm.pow 2)).intervalIntegrable 0 1
    have hIabs : IntervalIntegrable
        (fun θ : ℝ => |gsqderiv N a θ|) volume 0 1 :=
      (continuous_gsqderiv N a).abs.intervalIntegrable 0 1
    have h_integral_ineq : (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|) ≤
        (2 * Real.pi * N) * (∫ θ in (0:ℝ)..1, ‖S N a θ‖ ^ 2) +
          (1 / (2 * Real.pi * N)) * (∫ θ in (0:ℝ)..1, ‖Sderiv N a θ‖ ^ 2) := by
      calc
        (∫ θ in (0 : ℝ)..1, |gsqderiv N a θ|) ≤
            ∫ θ in (0 : ℝ)..1,
              ((2 * Real.pi * N) * ‖S N a θ‖ ^ 2 +
                (1 / (2 * Real.pi * N)) * ‖Sderiv N a θ‖ ^ 2) :=
          intervalIntegral.integral_mono_on (by norm_num) hIabs
            (hIleft.add hIright) (fun θ hθ => h_ineq θ)
        _ = (2 * Real.pi * N) * (∫ θ in (0 : ℝ)..1, ‖S N a θ‖ ^ 2) +
            (1 / (2 * Real.pi * N)) * (∫ θ in (0 : ℝ)..1, ‖Sderiv N a θ‖ ^ 2) := by
          rw [intervalIntegral.integral_add hIleft hIright,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have h_parseval :
        (∫ θ in (0:ℝ)..1, ‖S N a θ‖ ^ 2) = (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ∧
        (∫ θ in (0:ℝ)..1, ‖Sderiv N a θ‖ ^ 2) =
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (2 * Real.pi * n) ^ 2 := by
      constructor
      · exact parseval_expsum N a
      · calc
          (∫ θ in (0 : ℝ)..1, ‖Sderiv N a θ‖ ^ 2) =
              ∑ n ∈ Finset.Icc 1 N,
                ‖a n * (2 * Real.pi * Complex.I * (n : ℂ))‖ ^ 2 :=
            parseval_expsum N (fun n => a n * (2 * Real.pi * Complex.I * (n : ℂ)))
          _ = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (2 * Real.pi * (n : ℝ)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [norm_mul, frequency_norm136, mul_pow]
    have h_second_term :
        (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (2 * Real.pi * n) ^ 2) ≤
          (2 * Real.pi * N) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum _ _ _]
      exact Finset.sum_le_sum fun i hi => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left
              (Nat.cast_le.mpr <| Finset.mem_Icc.mp hi |>.2) <| by positivity) _) <| by positivity
    have hCpos : 0 < 2 * Real.pi * (N : ℝ) := by
      have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
      positivity
    rw [h_parseval.1, h_parseval.2] at h_integral_ineq
    calc
      (∫ θ in (0 : ℝ)..1, |gsqderiv N a θ|) ≤
          (2 * Real.pi * N) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) +
            (1 / (2 * Real.pi * N)) *
              (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (2 * Real.pi * n) ^ 2) :=
        h_integral_ineq
      _ ≤ (2 * Real.pi * N) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) +
            (1 / (2 * Real.pi * N)) *
              ((2 * Real.pi * N) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h_second_term
          (one_div_pos.mpr hCpos).le)
      _ = 4 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
        field_simp [ne_of_gt hCpos] <;> ring

/-- Gallagher additive large sieve, with an explicit absolute constant. -/
theorem additive_large_sieve (N : ℕ) (a : ℕ → ℂ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (R : ℕ) (x : Fin R → ℝ)
    (hmem : ∀ r, x r ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k : ℝ)|) :
    ∑ r : Fin R, ‖S N a (x r)‖ ^ 2 ≤
      (δ⁻¹ + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hg : (∑ r, gsq N a (x r)) ≤
      δ⁻¹ * (∫ θ in (0:ℝ)..1, gsq N a θ) +
        (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|) := by
    convert gallagher_sampling (fun θ => gsq N a θ) (fun θ => gsqderiv N a θ)
      _ _ _ _ δ hδ0 hδ1 R x hmem hsp using 1
    · exact fun θ => congr_arg (· ^ 2) (congr_arg Norm.norm (S_periodic N a θ))
    · exact fun _ => sq_nonneg _
    · exact fun θ => hasDerivAt_gsq N a θ
    · exact continuous_gsqderiv N a
  have h_integrals :
      (∫ θ in (0:ℝ)..1, gsq N a θ) = (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ∧
      (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|) ≤
        4 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    exact ⟨parseval_expsum N a, deriv_integral_bound N a⟩
  change (∑ r : Fin R, ‖S N a (x r)‖ ^ 2) ≤
    δ⁻¹ * (∫ θ in (0 : ℝ)..1, gsq N a θ) +
      (∫ θ in (0 : ℝ)..1, |gsqderiv N a θ|) at hg
  calc
    (∑ r : Fin R, ‖S N a (x r)‖ ^ 2) ≤
        δ⁻¹ * (∫ θ in (0 : ℝ)..1, gsq N a θ) +
          (∫ θ in (0 : ℝ)..1, |gsqderiv N a θ|) := hg
    _ ≤ δ⁻¹ * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) +
          4 * Real.pi * N * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left h_integrals.1.le (inv_nonneg.mpr hδ0.le))
        h_integrals.2
    _ = (δ⁻¹ + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring

/-- Arbitrary finite-index form, reindexed through Fintype.equivFin. -/
theorem additive_large_sieve_indexed (N : ℕ) (a : ℕ → ℂ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ι : Type*) [Fintype ι] (x : ι → ℝ) (hmem : ∀ i, x i ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : ι, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k:ℝ)|) :
    ∑ i, ‖S N a (x i)‖ ^ 2 ≤
      (δ⁻¹ + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  convert additive_large_sieve N a δ hδ0 hδ1 (Fintype.card ι)
    (fun i => x (e.symm i)) ?_ ?_ using 1
  · conv_lhs => rw [← Equiv.sum_comp e.symm]
  · exact fun i => hmem _
  · exact fun i j hij k => hsp _ _ (by simpa [e.symm.injective.eq_iff] using hij) k

noncomputable def frac (q : ℕ) (b : ZMod q) : ℝ := (ZMod.val b : ℝ) / q

/-- Exact agreement between the exponential and Mathlib's finite character. -/
lemma e_frac (q n : ℕ) [NeZero q] (b : ZMod q) :
    e ((n : ℝ) * frac q b) = ZMod.stdAddChar ((n : ZMod q) * b) := by
  -- Use the existing character formula on an integer lift. No explicit
  -- quotient of the difference of two representatives is required.
  have hlift : ((((n * b.val : ℕ) : ℤ) : ZMod q)) = (n : ZMod q) * b := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hchar := ZMod.stdAddChar_coe (N := q) ((n * b.val : ℕ) : ℤ)
  rw [hlift] at hchar
  rw [hchar]
  unfold e frac
  congr 1
  push_cast
  ring

def coprimeRes (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun m => Nat.Coprime m q)

/-- Farey spacing: the denominator in the spacing bound is explicit. -/
lemma farey_spacing_nat (Q q q' m m' : ℕ) (hq1 : 1 ≤ q) (hqQ : q ≤ Q)
    (hq'1 : 1 ≤ q') (hq'Q : q' ≤ Q) (hm : m < q) (hm' : m' < q')
    (hcop : Nat.Coprime m q) (hcop' : Nat.Coprime m' q')
    (hne : q ≠ q' ∨ m ≠ m') (k : ℤ) :
    (1:ℝ)/(Q:ℝ)^2 ≤ |(m : ℝ)/q - (m' : ℝ)/q' - (k:ℝ)| := by
  have h_mul : |(m : ℝ) * q' - (m' : ℝ) * q - k * (q * q')| ≥ 1 := by
    contrapose! hne
    norm_cast at *
    simp_all +decide [sub_eq_iff_eq_add]
    have h_eq : q = q' := by
      have h_eq : q ∣ q' ∧ q' ∣ q := by
        have h_div : q ∣ (m * q') ∧ q' ∣ (m' * q) := by
          rw [Int.subNatNat_eq_coe] at hne
          exact ⟨Int.natCast_dvd_natCast.mp ⟨k * q' + m', by push_cast at *; linarith⟩,
            Int.natCast_dvd_natCast.mp ⟨-k * q + m, by push_cast at *; linarith⟩⟩
        exact ⟨hcop.symm.dvd_of_dvd_mul_left h_div.1,
          hcop'.symm.dvd_of_dvd_mul_left h_div.2⟩
      exact Nat.dvd_antisymm h_eq.left h_eq.right
    simp_all +decide [Int.subNatNat_eq_coe]
    nlinarith [show k = 0 by nlinarith]
  field_simp
  rw [abs_div, div_le_div_iff₀] <;> norm_cast at * <;> simp_all +decide [mul_comm]
  · exact le_trans (by norm_cast; nlinarith)
      (mul_le_mul_of_nonneg_right h_mul (sq_nonneg _))
  · nlinarith
  · exact ⟨hq1, hq'1⟩

/-- Sum the sampling inequality over reduced fractions with denominator <=Q. -/
lemma farey_sum_bound (N Q : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ m ∈ coprimeRes q, ‖S N a ((m : ℝ) / q)‖ ^ 2 ≤
      ((Q:ℝ)^2 + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  set s := (Finset.Icc 1 Q).sigma (fun q => coprimeRes q) with hs_def
  set ι := {i : Σ _ : ℕ, ℕ // i ∈ s} with hι_def
  have h_apply : (∑ i : ι, ‖S N a ((i.val.2 : ℝ) / (i.val.1 : ℝ))‖ ^ 2) ≤
      ((1 : ℝ) / (Q : ℝ) ^ 2)⁻¹ * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) +
        4 * Real.pi * N * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
    convert additive_large_sieve_indexed N a (1 / (Q : ℝ) ^ 2) ?_ ?_ ι
      (fun i => (i.val.2 : ℝ) / (i.val.1 : ℝ)) ?_ ?_ using 1
    · ring
    · positivity
    · exact div_le_self zero_le_one (mod_cast Nat.one_le_pow _ _ hQ)
    · simp +zetaDelta at *
      exact fun a ha₁ ha₂ ha₃ => ⟨by positivity, by
        rw [div_lt_one (by positivity)]
        exact_mod_cast Finset.mem_range.mp (Finset.mem_filter.mp ha₃ |>.1)⟩
    · simp +zetaDelta at *
      intro a ha₁ ha₂ ha₃ b hb₁ hb₂ hb₃ hab k
      convert farey_spacing_nat Q a.fst b.fst a.snd b.snd ha₁ ha₂ hb₁ hb₂
        (Finset.mem_range.mp (Finset.mem_filter.mp ha₃ |>.1))
        (Finset.mem_range.mp (Finset.mem_filter.mp hb₃ |>.1))
        (Finset.mem_filter.mp ha₃ |>.2) (Finset.mem_filter.mp hb₃ |>.2) ?_ k using 1
      · ring
      · exact not_and_or.mp fun h => hab <| by cases a; cases b; aesop
  convert h_apply using 1
  · convert Finset.sum_sigma' (Finset.Icc 1 Q) (fun q => coprimeRes q)
      (fun q m => ‖S N a (m / q : ℝ)‖ ^ 2) using 1
    refine' Finset.sum_bij (fun x hx => x.val) _ _ _ _ <;> aesop
  · norm_num
    ring

-- Historical audit output (142): #print axioms continuous_e136
-- Historical audit output (142): #print axioms continuous_frequency136
-- Historical audit output (142): #print axioms continuous_S136
-- Historical audit output (142): #print axioms continuous_Sderiv136
-- Historical audit output (142): #print axioms integral_e_int
-- Historical audit output (142): #print axioms periodic_cover_bound
-- Historical audit output (142): #print axioms gallagher_sampling
-- Historical audit output (142): #print axioms parseval_expsum
-- Historical audit output (142): #print axioms hasDerivAt_S
-- Historical audit output (142): #print axioms hasDerivAt_gsq
-- Historical audit output (142): #print axioms frequency_norm136
-- Historical audit output (142): #print axioms deriv_integral_bound
-- Historical audit output (142): #print axioms additive_large_sieve
-- Historical audit output (142): #print axioms additive_large_sieve_indexed
-- Historical audit output (142): #print axioms e_frac
-- Historical audit output (142): #print axioms farey_spacing_nat
-- Historical audit output (142): #print axioms farey_sum_bound

end ImportedLargeSieve135


/-! ## 135B. Specialize the included large sieve to the project's exact energy

The imported proof bodies above supply the analytic inequality. This section
proves the remaining normalization, finite reindexing, indicator-energy and
real-cutoff steps. No large-sieve hypothesis is introduced here.

New scripts are locally UNCOMPILED. The remaining external quantitative PNT,
sparse prime supply, Harman and nontrivial Weil inputs are NOT proved here.
-/
namespace RemainingAnalytic135

open scoped BigOperators
open RemainingAnalytic59 RemainingAnalytic92 RemainingAnalytic127
open RemainingAnalytic130 RemainingAnalytic131 RemainingAnalytic132
open RemainingAnalytic133 RemainingAnalytic134

set_option maxHeartbeats 4000000

/-- Explicit indicator coefficients, indexed by natural numbers. -/
noncomputable def indicatorCoeff135 (T : Finset ℕ) (n : ℕ) : ℂ :=
  if n ∈ T then 1 else 0

/-- Restriction to T loses no terms when T is contained in [1,N]. -/
theorem exponentialSum_indicator135 (N : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.Icc 1 N) (x : ℝ) :
    ImportedLargeSieve135.S N (indicatorCoeff135 T) x =
      ∑ n ∈ T, ImportedLargeSieve135.e ((n : ℝ) * x) := by
  classical
  have hfilter : (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ T) = T := by
    ext n
    exact ⟨fun hn => (Finset.mem_filter.mp hn).2,
      fun hn => Finset.mem_filter.mpr ⟨hT hn, hn⟩⟩
  unfold ImportedLargeSieve135.S
  calc
    (∑ n ∈ Finset.Icc 1 N, indicatorCoeff135 T n *
        ImportedLargeSieve135.e ((n : ℝ) * x)) =
      ∑ n ∈ Finset.Icc 1 N, if n ∈ T then
        ImportedLargeSieve135.e ((n : ℝ) * x) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hnT : n ∈ T <;> simp [indicatorCoeff135, hnT]
    _ = ∑ n ∈ T, ImportedLargeSieve135.e ((n : ℝ) * x) := by
      rw [← Finset.sum_filter, hfilter]

/-- The coefficient squared norm is exactly the number of selected integers. -/
theorem indicatorCoeff_energy135 (N : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.Icc 1 N) :
    (∑ n ∈ Finset.Icc 1 N, ‖indicatorCoeff135 T n‖ ^ 2) = (T.card : ℝ) := by
  classical
  have hfilter : (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ T) = T := by
    ext n
    exact ⟨fun hn => (Finset.mem_filter.mp hn).2,
      fun hn => Finset.mem_filter.mpr ⟨hT hn, hn⟩⟩
  calc
    (∑ n ∈ Finset.Icc 1 N, ‖indicatorCoeff135 T n‖ ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, if n ∈ T then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnT : n ∈ T <;> simp [indicatorCoeff135, hnT]
    _ = (T.card : ℝ) := by
      rw [← Finset.sum_filter, hfilter]
      simp

/-- The minus sign in the source's DFT is handled by the point (-k).val/q,
not silently discarded. This identity is pointwise, before taking norms. -/
theorem exponentialSum_at_negative_residue135 (N : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.Icc 1 N) (q : ℕ) [NeZero q] (k : ZMod q) :
    ImportedLargeSieve135.S N (indicatorCoeff135 T)
        (ImportedLargeSieve135.frac q (-k)) =
      ∑ n ∈ T, ZMod.stdAddChar (-((n : ZMod q) * k)) := by
  rw [exponentialSum_indicator135 N T hT]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ImportedLargeSieve135.e_frac]
  congr 1
  ring

/-- Nonzero residue frequencies reindex bijectively by the natural values of
-k. The zero term is kept explicitly until the next prime-modulus step. -/
theorem additiveFourierEnergy_eq_fraction_sum135 (N : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.Icc 1 N) {q : ℕ} (hq : 0 < q) :
    additiveFourierEnergy59 T q =
      ∑ m ∈ Finset.range q, if m = 0 then 0 else
        ‖ImportedLargeSieve135.S N (indicatorCoeff135 T) ((m : ℝ) / (q : ℝ))‖ ^ 2 := by
  classical
  letI : NeZero q := ⟨ne_of_gt hq⟩
  unfold additiveFourierEnergy59
  rw [dif_neg (ne_of_gt hq)]
  change (∑ k : ZMod q, if k = 0 then (0 : ℝ) else
    ‖∑ n ∈ T, ZMod.stdAddChar (-((n : ZMod q) * k))‖ ^ 2) = _
  apply Finset.sum_bij (fun k _ => (-k).val)
  · intro k hk
    exact Finset.mem_range.mpr (ZMod.val_lt (-k))
  · intro k hk l hl hkl
    exact neg_injective (ZMod.val_injective q hkl)
  · intro m hm
    refine ⟨-(m : ZMod q), Finset.mem_univ _, ?_⟩
    simp only [neg_neg, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hm)]
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hval0 : (-k).val ≠ 0 := (ZMod.val_ne_zero (-k)).mpr (neg_ne_zero.mpr hk0)
      rw [if_neg hk0, if_neg hval0]
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
        (exponentialSum_at_negative_residue135 N T hT q k).symm

/-- For a prime modulus, the reduced residues are precisely the nonzero ones. -/
theorem prime_coprime_iff_nonzero135 {q m : ℕ} (hq : q.Prime) (hm : m < q) :
    m.Coprime q ↔ m ≠ 0 := by
  constructor
  · intro hc hm0
    subst m
    have hq1 : q = 1 := by simpa using hc
    exact hq.ne_one hq1
  · intro hm0
    have hnot : ¬ q ∣ m := by
      intro hd
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd
      exact (not_le_of_gt hm) hle
    exact ((hq.coprime_iff_not_dvd).mpr hnot).symm

/-- Exact compatibility with the reduced-fraction large-sieve summands. -/
theorem additiveFourierEnergy_eq_reduced_sum135 (N : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.Icc 1 N) {q : ℕ} (hq : q.Prime) :
    additiveFourierEnergy59 T q =
      ∑ m ∈ ImportedLargeSieve135.coprimeRes q,
        ‖ImportedLargeSieve135.S N (indicatorCoeff135 T) ((m : ℝ) / (q : ℝ))‖ ^ 2 := by
  classical
  rw [additiveFourierEnergy_eq_fraction_sum135 N T hT hq.pos]
  unfold ImportedLargeSieve135.coprimeRes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hiff := prime_coprime_iff_nonzero135 hq (Finset.mem_range.mp hm)
  by_cases hm0 : m = 0
  · have hcop : ¬ m.Coprime q := fun hh => (hiff.mp hh) hm0
    rw [if_pos hm0, if_neg hcop]
  · have hcop : m.Coprime q := hiff.mpr hm0
    rw [if_neg hm0, if_pos hcop]

/-- The project's exact prime-modulus energy has the quantitative Gallagher
bound. Q is real, including 1 <= Q < 2; no rounding error is dropped. -/
theorem primeAdditiveLargeSieve_explicit135
    (N : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) (Primes : Finset ℕ)
    (hPrimes : ∀ q : ℕ, q ∈ Primes → q.Prime ∧ (q : ℝ) ≤ Q)
    (T : Finset ℕ) (hT : T ⊆ Finset.Icc 1 N) :
    (∑ q ∈ Primes, additiveFourierEnergy59 T q) ≤
      (Q ^ 2 + 4 * Real.pi * (N : ℝ)) * (T.card : ℝ) := by
  classical
  let R : ℕ := ⌊Q⌋₊
  have hQ0 : 0 ≤ Q := by linarith
  have hR1 : 1 ≤ R := (Nat.le_floor_iff hQ0).mpr (by simpa using hQ)
  have hRQ : (R : ℝ) ≤ Q := Nat.floor_le hQ0
  have hsub : Primes ⊆ Finset.Icc 1 R := by
    intro q hq
    have hd := hPrimes q hq
    exact Finset.mem_Icc.mpr ⟨hd.1.one_le, (Nat.le_floor_iff hQ0).mpr hd.2⟩
  let F : ℕ → ℝ := fun q =>
    ∑ m ∈ ImportedLargeSieve135.coprimeRes q,
      ‖ImportedLargeSieve135.S N (indicatorCoeff135 T) ((m : ℝ) / (q : ℝ))‖ ^ 2
  have hF0 : ∀ q : ℕ, 0 ≤ F q := by
    intro q
    exact Finset.sum_nonneg (fun m hm => sq_nonneg _)
  have hsum : (∑ q ∈ Primes, additiveFourierEnergy59 T q) = ∑ q ∈ Primes, F q := by
    apply Finset.sum_congr rfl
    intro q hq
    exact additiveFourierEnergy_eq_reduced_sum135 N T hT (hPrimes q hq).1
  have hFarey := ImportedLargeSieve135.farey_sum_bound N R hR1 (indicatorCoeff135 T)
  rw [indicatorCoeff_energy135 N T hT] at hFarey
  have hR2 : (R : ℝ) ^ 2 ≤ Q ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (R : ℝ) by positivity]
  calc
    (∑ q ∈ Primes, additiveFourierEnergy59 T q) = ∑ q ∈ Primes, F q := hsum
    _ ≤ ∑ q ∈ Finset.Icc 1 R, F q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hnot => hF0 q)
    _ ≤ ((R : ℝ) ^ 2 + 4 * Real.pi * (N : ℝ)) * (T.card : ℝ) := hFarey
    _ ≤ (Q ^ 2 + 4 * Real.pi * (N : ℝ)) * (T.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hR2]) (by positivity)

/-- The old large-sieve interface now has an input-free proof script. The
constant 1+4*pi is deliberately loose and is uniform in every parameter. -/
theorem classicalPrimeAdditiveLargeSieve_proved135 : ClassicalPrimeAdditiveLargeSieve92 := by
  refine ⟨1 + 4 * Real.pi, by positivity, ?_⟩
  intro N Q hQ Primes hPrimes T hT
  have hbound := primeAdditiveLargeSieve_explicit135 N Q hQ Primes hPrimes T hT
  have hcoef : Q ^ 2 + 4 * Real.pi * (N : ℝ) ≤
      (1 + 4 * Real.pi) * ((N : ℝ) + Q ^ 2) := by
    have hnonneg : 0 ≤ 4 * Real.pi * Q ^ 2 := by positivity
    nlinarith [show (0 : ℝ) ≤ (N : ℝ) by positivity]
  exact le_trans hbound (mul_le_mul_of_nonneg_right hcoef (by positivity))

/-! ### C. Endgame without the independent large-sieve field

The standalone file still requires FOUR total analytic inputs: quantitative
PNT, sparse valuation-one prime supply, Harman bad-set density and the
large-modulus Weil bound. The PNT theorem has not been imported here.
-/
structure RemainingNonPNTInputs135 where
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  large_modulus_weil : LargeModulusLinearProductWeil127

noncomputable def RemainingNonPNTInputs135.to134 (H : RemainingNonPNTInputs135) : NonPNTInputs134 where
  sparse_good_prime_count := H.sparse_good_prime_count
  harman_bad_density := H.harman_bad_density
  large_sieve := classicalPrimeAdditiveLargeSieve_proved135
  large_modulus_weil := H.large_modulus_weil

theorem candidate_main_from_mediumPNT135
    (HP : PsiMediumPNT134) (H : RemainingNonPNTInputs135) : MainStatement :=
  candidate_main_from_mediumPNT134 HP H.to134

theorem positive_lower_density_from_mediumPNT135
    (HP : PsiMediumPNT134) (H : RemainingNonPNTInputs135) : PositiveLowerDensity D6 :=
  positive_lower_density_from_mediumPNT134 HP H.to134

-- Historical audit output (142): #print axioms coprime_hasDensity133
-- Historical audit output (142): #print axioms ADensity_pos_from_theta133
-- Historical audit output (142): #print axioms AFiniteDensityLimit_from_theta133
-- Historical audit output (142): #print axioms thetaLogSqRemainder_from_mediumPNT134
-- Historical audit output (142): #print axioms exponentialSum_indicator135
-- Historical audit output (142): #print axioms indicatorCoeff_energy135
-- Historical audit output (142): #print axioms exponentialSum_at_negative_residue135
-- Historical audit output (142): #print axioms additiveFourierEnergy_eq_fraction_sum135
-- Historical audit output (142): #print axioms prime_coprime_iff_nonzero135
-- Historical audit output (142): #print axioms additiveFourierEnergy_eq_reduced_sum135
-- Historical audit output (142): #print axioms primeAdditiveLargeSieve_explicit135
-- Historical audit output (142): #print axioms classicalPrimeAdditiveLargeSieve_proved135
-- Historical audit output (142): #print axioms RemainingNonPNTInputs135.to134
-- Historical audit output (142): #print axioms candidate_main_from_mediumPNT135
-- Historical audit output (142): #print axioms positive_lower_density_from_mediumPNT135
-- Historical audit output (142): #check classicalPrimeAdditiveLargeSieve_proved135
-- Historical audit output (142): #check candidate_main_from_mediumPNT135
-- Historical audit output (142): #print RemainingNonPNTInputs135
-- Frozen historical output: #eval "REPAIR 135 CHECKPOINT: weighted sampling consequences and Repair 136 audit follow"

end RemainingAnalytic135

/-! ## 136. Weighted sampling and large-frequency counting consequences

These corollaries use the included additive large sieve for arbitrary complex
coefficients, not only the indicator of a set of integers. They also handle a
real modulus cutoff and any selected positive moduli, not just prime moduli.
They do NOT prove distribution of primes in short intervals: a connection
between the relevant bad intervals and this sampling bound is still required.
The original four remaining analytic inputs are unchanged.

All new/edited scripts in this release are locally UNCOMPILED.
-/
namespace RemainingAnalytic136

open scoped BigOperators
open RemainingAnalytic127 RemainingAnalytic133 RemainingAnalytic134
open RemainingAnalytic135

/-- Coefficient energy for a finite exponential sum. -/
noncomputable def coefficientEnergy136 (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2

/-- Squared samples at all reduced fractions of one denominator. -/
noncomputable def reducedEnergy136 (N : ℕ) (a : ℕ → ℂ) (q : ℕ) : ℝ :=
  ∑ m ∈ ImportedLargeSieve135.coprimeRes q,
    ‖ImportedLargeSieve135.S N a ((m : ℝ) / (q : ℝ))‖ ^ 2

/-- Selected denominators, a real cutoff, and arbitrary complex coefficients.
The proof supplies the restriction and rounding steps; the analytic sampling
bound is the included theorem with individual compilation checkpoints, not an input. -/
theorem weightedReducedLargeSieve136
    (N : ℕ) (a : ℕ → ℂ) (Q : ℝ) (hQ : 1 ≤ Q) (D : Finset ℕ)
    (hD : ∀ q ∈ D, 1 ≤ q ∧ (q : ℝ) ≤ Q) :
    (∑ q ∈ D, reducedEnergy136 N a q) ≤
      (Q ^ 2 + 4 * Real.pi * (N : ℝ)) * coefficientEnergy136 N a := by
  classical
  let R : ℕ := ⌊Q⌋₊
  have hQ0 : 0 ≤ Q := by linarith
  have hR1 : 1 ≤ R := (Nat.le_floor_iff hQ0).mpr (by simpa using hQ)
  have hRQ : (R : ℝ) ≤ Q := Nat.floor_le hQ0
  have hsub : D ⊆ Finset.Icc 1 R := by
    intro q hq
    exact Finset.mem_Icc.mpr
      ⟨(hD q hq).1, (Nat.le_floor_iff hQ0).mpr (hD q hq).2⟩
  have hnonneg : ∀ q : ℕ, 0 ≤ reducedEnergy136 N a q := by
    intro q
    exact Finset.sum_nonneg (fun m hm => sq_nonneg _)
  have hFarey := ImportedLargeSieve135.farey_sum_bound N R hR1 a
  have hR2 : (R : ℝ) ^ 2 ≤ Q ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (R : ℝ) by positivity]
  have hE0 : 0 ≤ coefficientEnergy136 N a :=
    Finset.sum_nonneg (fun n hn => sq_nonneg _)
  calc
    (∑ q ∈ D, reducedEnergy136 N a q) ≤
        ∑ q ∈ Finset.Icc 1 R, reducedEnergy136 N a q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hnot => hnonneg q)
    _ ≤ ((R : ℝ) ^ 2 + 4 * Real.pi * (N : ℝ)) * coefficientEnergy136 N a := hFarey
    _ ≤ (Q ^ 2 + 4 * Real.pi * (N : ℝ)) * coefficientEnergy136 N a :=
      mul_le_mul_of_nonneg_right (by linarith only [hR2]) hE0

/-- Reduced frequencies at which the squared exponential sum reaches tau^2.
This is a finite set; no asymptotic or prime-distribution claim is built in. -/
noncomputable def largeFrequencies136
    (N : ℕ) (a : ℕ → ℂ) (q : ℕ) (τ : ℝ) : Finset ℕ :=
  (ImportedLargeSieve135.coprimeRes q).filter
    (fun m => τ ^ 2 ≤ ‖ImportedLargeSieve135.S N a ((m : ℝ) / (q : ℝ))‖ ^ 2)

/-- The local second-moment counting step, including tau=0. -/
theorem largeFrequencyCount_mul_le_energy136
    (N : ℕ) (a : ℕ → ℂ) (q : ℕ) (τ : ℝ) :
    τ ^ 2 * ((largeFrequencies136 N a q τ).card : ℝ) ≤ reducedEnergy136 N a q := by
  classical
  let F : Finset ℕ := largeFrequencies136 N a q τ
  have hsub : F ⊆ ImportedLargeSieve135.coprimeRes q :=
    Finset.filter_subset _ _
  calc
    τ ^ 2 * (F.card : ℝ) = ∑ m ∈ F, τ ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ m ∈ F,
        ‖ImportedLargeSieve135.S N a ((m : ℝ) / (q : ℝ))‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact (Finset.mem_filter.mp hm).2
    _ ≤ reducedEnergy136 N a q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm hnot => sq_nonneg _)

/-- Explicit upper bound for the total number of large reduced-frequency
samples. This is a consequence of the actual large-sieve proof, not a new
hypothesis about those samples. -/
theorem largeFrequencyCount_le136
    (N : ℕ) (a : ℕ → ℂ) (Q : ℝ) (hQ : 1 ≤ Q) (D : Finset ℕ)
    (hD : ∀ q ∈ D, 1 ≤ q ∧ (q : ℝ) ≤ Q) (τ : ℝ) (hτ : 0 < τ) :
    (∑ q ∈ D, ((largeFrequencies136 N a q τ).card : ℝ)) ≤
      ((Q ^ 2 + 4 * Real.pi * (N : ℝ)) * coefficientEnergy136 N a) / τ ^ 2 := by
  have hsmall := Finset.sum_le_sum
    (s := D) (fun q hq => largeFrequencyCount_mul_le_energy136 N a q τ)
  rw [← Finset.mul_sum] at hsmall
  have hbound := le_trans hsmall (weightedReducedLargeSieve136 N a Q hQ D hD)
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
  simpa only [mul_comm] using hbound

/-- Set-indicator specialization. It retains the exact cardinality |T| in
place of coefficient energy and costs no additional analytic assumption. -/
theorem largeFrequencyCount_indicator136
    (N : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.Icc 1 N)
    (Q : ℝ) (hQ : 1 ≤ Q) (D : Finset ℕ)
    (hD : ∀ q ∈ D, 1 ≤ q ∧ (q : ℝ) ≤ Q) (τ : ℝ) (hτ : 0 < τ) :
    (∑ q ∈ D, ((largeFrequencies136 N (indicatorCoeff135 T) q τ).card : ℝ)) ≤
      ((Q ^ 2 + 4 * Real.pi * (N : ℝ)) * (T.card : ℝ)) / τ ^ 2 := by
  have hE : coefficientEnergy136 N (indicatorCoeff135 T) = (T.card : ℝ) :=
    indicatorCoeff_energy135 N T hT
  have hbound := largeFrequencyCount_le136 N (indicatorCoeff135 T) Q hQ D hD τ hτ
  rw [hE] at hbound
  exact hbound

/-- Versioned endpoint. The PNT argument plus the three fields of H remain
unconstructed. The weighted corollaries do not remove any of these inputs. -/
theorem candidate_main_from_mediumPNT136
    (HP : PsiMediumPNT134) (H : RemainingNonPNTInputs135) : MainStatement :=
  candidate_main_from_mediumPNT135 HP H

theorem positive_lower_density_from_mediumPNT136
    (HP : PsiMediumPNT134) (H : RemainingNonPNTInputs135) : PositiveLowerDensity D6 :=
  positive_lower_density_from_mediumPNT135 HP H

/-! These checks include every directly repaired declaration. A clean result
for a conditional theorem is not an inhabitant of its remaining input types. -/
-- Historical audit output (142): #print axioms coprime_hasDensity133
-- Historical audit output (142): #print axioms ADensity_pos_from_theta133
-- Historical audit output (142): #print axioms ImportedLargeSieve135.continuous_e136
-- Historical audit output (142): #print axioms ImportedLargeSieve135.continuous_frequency136
-- Historical audit output (142): #print axioms ImportedLargeSieve135.continuous_S136
-- Historical audit output (142): #print axioms ImportedLargeSieve135.continuous_Sderiv136
-- Historical audit output (142): #print axioms ImportedLargeSieve135.gallagher_sampling
-- Historical audit output (142): #print axioms ImportedLargeSieve135.parseval_expsum
-- Historical audit output (142): #print axioms ImportedLargeSieve135.hasDerivAt_S
-- Historical audit output (142): #print axioms ImportedLargeSieve135.frequency_norm136
-- Historical audit output (142): #print axioms ImportedLargeSieve135.deriv_integral_bound
-- Historical audit output (142): #print axioms ImportedLargeSieve135.additive_large_sieve
-- Historical audit output (142): #print axioms ImportedLargeSieve135.e_frac
-- Historical audit output (142): #print axioms ImportedLargeSieve135.farey_sum_bound
-- Historical audit output (142): #print axioms classicalPrimeAdditiveLargeSieve_proved135
-- Historical audit output (142): #print axioms weightedReducedLargeSieve136
-- Historical audit output (142): #print axioms largeFrequencyCount_mul_le_energy136
-- Historical audit output (142): #print axioms largeFrequencyCount_le136
-- Historical audit output (142): #print axioms largeFrequencyCount_indicator136
-- Historical audit output (142): #print axioms candidate_main_from_mediumPNT136
-- Historical audit output (142): #print axioms positive_lower_density_from_mediumPNT136
-- Historical audit output (142): #check weightedReducedLargeSieve136
-- Historical audit output (142): #check largeFrequencyCount_le136
-- Historical audit output (142): #check candidate_main_from_mediumPNT136
-- Historical audit output (142): #print PsiMediumPNT134
-- Historical audit output (142): #print RemainingNonPNTInputs135
-- Frozen historical output: #eval "REPAIR 136 CHECKPOINT: exact residue-variance consequences follow"

end RemainingAnalytic136

/-! ## 137. Exact residue variance and exceptional-residue estimates

The three failing declarations are repaired in their original bodies above.
This section connects the already-developed collision/Fourier identity to
actual residue-count discrepancies. It is a consequence of the included
large sieve, NOT an additional distribution hypothesis.

For c_q(u) = #{n in T : n mod q = u}, J = #T, and q > 0:
  q * sum_{0 <= u < q} (c_q(u) - J/q)^2 = additiveFourierEnergy59 T q.
Thus prime-modulus mean-square discrepancies have the same absolute bound
(Q^2 + 4*pi*N)*J, with no forgotten zero-frequency or normalization term.

All new/edited scripts in this release remain locally UNCOMPILED.
The PNT, sparse prime, Harman and nontrivial Weil inputs are unchanged.
-/
namespace RemainingAnalytic137

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic88
open RemainingAnalytic127 RemainingAnalytic133 RemainingAnalytic134
open RemainingAnalytic135 RemainingAnalytic136

/-- Count one residue class using the same fiber count as the collision identity. -/
noncomputable def residueProfile137 (T : Finset ℕ) (q u : ℕ) : ℝ :=
  (fiberCount T (fun n : ℕ => n % q) u : ℝ)

/-- All occupied residues lie in the complete standard residue interval. -/
theorem residueSupport_subset_range137 (T : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    imageSupport T (fun n : ℕ => n % q) ⊆ Finset.range q := by
  intro u hu
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
  exact Finset.mem_range.mpr (Nat.mod_lt n hq)

/-- Fibers outside the occupied support are exactly empty. -/
theorem residueProfile_zero_off_support137 (T : Finset ℕ) (q u : ℕ)
    (hu : u ∉ imageSupport T (fun n : ℕ => n % q)) :
    residueProfile137 T q u = 0 := by
  classical
  have hempty : T.filter (fun n : ℕ => n % q = u) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnT, hnu⟩ := Finset.mem_filter.mp hn
    exact hu (Finset.mem_image.mpr ⟨n, hnT, hnu⟩)
  simp only [residueProfile137, fiberCount, hempty, Finset.card_empty, Nat.cast_zero]

/-- Total mass over all q residue classes is exactly the cardinality of T. -/
theorem residueProfile_sum137 (T : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    (∑ u ∈ Finset.range q, residueProfile137 T q u) = (T.card : ℝ) := by
  classical
  have hsub := residueSupport_subset_range137 T hq
  calc
    (∑ u ∈ Finset.range q, residueProfile137 T q u) =
        ∑ u ∈ imageSupport T (fun n : ℕ => n % q), residueProfile137 T q u := by
      symm
      exact Finset.sum_subset hsub
        (fun u hu hnot => residueProfile_zero_off_support137 T q u hnot)
    _ = (T.card : ℝ) := by
      change (∑ u ∈ imageSupport T (fun n : ℕ => n % q),
        (fiberCount T (fun n : ℕ => n % q) u : ℝ)) = (T.card : ℝ)
      exact_mod_cast sum_fiberCount_image T (fun n : ℕ => n % q)

/-- Adding zero fibers leaves the original collision sum unchanged. -/
theorem residueProfile_square_sum137 (T : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    (∑ u ∈ Finset.range q, (residueProfile137 T q u) ^ 2) =
      residueCollisionSum T q := by
  classical
  have hsub := residueSupport_subset_range137 T hq
  calc
    (∑ u ∈ Finset.range q, (residueProfile137 T q u) ^ 2) =
        ∑ u ∈ imageSupport T (fun n : ℕ => n % q),
          (residueProfile137 T q u) ^ 2 := by
      symm
      apply Finset.sum_subset hsub
      intro u hu hnot
      rw [residueProfile_zero_off_support137 T q u hnot, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    _ = residueCollisionSum T q := rfl

/-- Finite centered-square identity with every mean term retained. -/
theorem sum_centered_squares137 (s : Finset ℕ) (f : ℕ → ℝ) (μ : ℝ) :
    (∑ u ∈ s, (f u - μ) ^ 2) =
      (∑ u ∈ s, (f u) ^ 2) - (2 * μ) * (∑ u ∈ s, f u) +
        (s.card : ℝ) * μ ^ 2 := by
  calc
    (∑ u ∈ s, (f u - μ) ^ 2) =
        ∑ u ∈ s, ((f u) ^ 2 - (2 * μ) * f u + μ ^ 2) := by
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = (∑ u ∈ s, (f u) ^ 2) - (2 * μ) * (∑ u ∈ s, f u) +
        (s.card : ℝ) * μ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Unnormalized variance around the uniform profile J/q, including empty classes. -/
noncomputable def residueVariance137 (T : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ u ∈ Finset.range q, (residueProfile137 T q u - (T.card : ℝ) / (q : ℝ)) ^ 2

theorem residueVariance_nonneg137 (T : Finset ℕ) (q : ℕ) :
    0 ≤ residueVariance137 T q :=
  Finset.sum_nonneg (fun u hu => sq_nonneg _)

/-- Exact normalization: nonzero-frequency energy is q times the residue variance.
The assumption q>0 is essential for the complete-residue and mean identities. -/
theorem residueVariance_eq_energy137 (T : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    (q : ℝ) * residueVariance137 T q = residueEnergy T q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  unfold residueVariance137
  rw [sum_centered_squares137, residueProfile_square_sum137 T hq,
    residueProfile_sum137 T hq, Finset.card_range]
  unfold residueEnergy
  field_simp [hq0] <;> ring

/-- The old exact DFT identity now yields a centered count interpretation. -/
theorem residueVariance_eq_fourier137 (T : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    (q : ℝ) * residueVariance137 T q = additiveFourierEnergy59 T q :=
  (residueVariance_eq_energy137 T hq).trans
    (additiveEnergyIdentity_proved88 T q hq).symm

/-- Explicit prime-modulus variance bound. This concerns the actual counts,
not just an unspecified Fourier discrepancy. No new analytic input is taken. -/
theorem primeResidueVariance_bound137
    (N : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) (Primes : Finset ℕ)
    (hPrimes : ∀ q ∈ Primes, q.Prime ∧ (q : ℝ) ≤ Q)
    (T : Finset ℕ) (hT : T ⊆ Finset.Icc 1 N) :
    (∑ q ∈ Primes, (q : ℝ) * residueVariance137 T q) ≤
      (Q ^ 2 + 4 * Real.pi * (N : ℝ)) * (T.card : ℝ) := by
  calc
    (∑ q ∈ Primes, (q : ℝ) * residueVariance137 T q) =
        ∑ q ∈ Primes, additiveFourierEnergy59 T q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact residueVariance_eq_fourier137 T (hPrimes q hq).1.pos
    _ ≤ (Q ^ 2 + 4 * Real.pi * (N : ℝ)) * (T.card : ℝ) :=
      primeAdditiveLargeSieve_explicit135 N Q hQ Primes hPrimes T hT

/-- Residues whose squared deviation is at least tau^2. With tau>0 this is
exactly an absolute deviation at least tau; equality is included. -/
noncomputable def exceptionalResidues137 (T : Finset ℕ) (q : ℕ) (τ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range q).filter (fun u =>
    τ ^ 2 ≤ (residueProfile137 T q u - (T.card : ℝ) / (q : ℝ)) ^ 2)

/-- The local counting inequality is finite and needs no prime hypothesis. -/
theorem exceptionalResidueCount_mul_le137 (T : Finset ℕ) (q : ℕ) (τ : ℝ) :
    τ ^ 2 * ((exceptionalResidues137 T q τ).card : ℝ) ≤ residueVariance137 T q := by
  classical
  let F : Finset ℕ := exceptionalResidues137 T q τ
  have hsub : F ⊆ Finset.range q := Finset.filter_subset _ _
  calc
    τ ^ 2 * (F.card : ℝ) = ∑ u ∈ F, τ ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ u ∈ F, (residueProfile137 T q u - (T.card : ℝ) / (q : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact (Finset.mem_filter.mp hu).2
    _ ≤ residueVariance137 T q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u hu hnot => sq_nonneg _)

/-- A q-weighted count of residue classes with large count discrepancy.
The q weight is required by the exact Fourier normalization; it is not omitted. -/
theorem exceptionalResidueCount_bound137
    (N : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) (Primes : Finset ℕ)
    (hPrimes : ∀ q ∈ Primes, q.Prime ∧ (q : ℝ) ≤ Q)
    (T : Finset ℕ) (hT : T ⊆ Finset.Icc 1 N) (τ : ℝ) (hτ : 0 < τ) :
    (∑ q ∈ Primes, (q : ℝ) * ((exceptionalResidues137 T q τ).card : ℝ)) ≤
      ((Q ^ 2 + 4 * Real.pi * (N : ℝ)) * (T.card : ℝ)) / τ ^ 2 := by
  have hlocal : ∀ q ∈ Primes,
      τ ^ 2 * ((q : ℝ) * ((exceptionalResidues137 T q τ).card : ℝ)) ≤
        (q : ℝ) * residueVariance137 T q := by
    intro q hq
    calc
      τ ^ 2 * ((q : ℝ) * ((exceptionalResidues137 T q τ).card : ℝ)) =
          (q : ℝ) * (τ ^ 2 * ((exceptionalResidues137 T q τ).card : ℝ)) := by ring
      _ ≤ (q : ℝ) * residueVariance137 T q :=
        mul_le_mul_of_nonneg_left (exceptionalResidueCount_mul_le137 T q τ) (by positivity)
  have hsum := Finset.sum_le_sum hlocal
  rw [← Finset.mul_sum] at hsum
  have hbound := le_trans hsum (primeResidueVariance_bound137 N Q hQ Primes hPrimes T hT)
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
  simpa only [mul_comm] using hbound

/-- Versioned endpoint: HP plus the three fields of H are still unconstructed.
The new variance results do not prove sparse/Harman/Weil distribution estimates. -/
theorem candidate_main_from_mediumPNT137
    (HP : PsiMediumPNT134) (H : RemainingNonPNTInputs135) : MainStatement :=
  candidate_main_from_mediumPNT136 HP H

theorem positive_lower_density_from_mediumPNT137
    (HP : PsiMediumPNT134) (H : RemainingNonPNTInputs135) : PositiveLowerDensity D6 :=
  positive_lower_density_from_mediumPNT136 HP H

/-! Individual checks, including all directly repaired declarations. -/
-- Historical audit output (142): #print axioms coprime_hasDensity133
-- Historical audit output (142): #print axioms ADensity_pos_from_theta133
-- Historical audit output (142): #print axioms AFiniteDensityLimit_from_theta133
-- Historical audit output (142): #print axioms ImportedLargeSieve135.hasDerivAt_S
-- Historical audit output (142): #print axioms ImportedLargeSieve135.deriv_integral_bound
-- Historical audit output (142): #print axioms ImportedLargeSieve135.gallagher_sampling
-- Historical audit output (142): #print axioms ImportedLargeSieve135.parseval_expsum
-- Historical audit output (142): #print axioms ImportedLargeSieve135.additive_large_sieve
-- Historical audit output (142): #print axioms ImportedLargeSieve135.e_frac
-- Historical audit output (142): #print axioms ImportedLargeSieve135.farey_sum_bound
-- Historical audit output (142): #print axioms classicalPrimeAdditiveLargeSieve_proved135
-- Historical audit output (142): #print axioms residueSupport_subset_range137
-- Historical audit output (142): #print axioms residueProfile_zero_off_support137
-- Historical audit output (142): #print axioms residueProfile_sum137
-- Historical audit output (142): #print axioms residueProfile_square_sum137
-- Historical audit output (142): #print axioms sum_centered_squares137
-- Historical audit output (142): #print axioms residueVariance_nonneg137
-- Historical audit output (142): #print axioms residueVariance_eq_energy137
-- Historical audit output (142): #print axioms residueVariance_eq_fourier137
-- Historical audit output (142): #print axioms primeResidueVariance_bound137
-- Historical audit output (142): #print axioms exceptionalResidueCount_mul_le137
-- Historical audit output (142): #print axioms exceptionalResidueCount_bound137
-- Historical audit output (142): #print axioms candidate_main_from_mediumPNT137
-- Historical audit output (142): #print axioms positive_lower_density_from_mediumPNT137
-- Historical audit output (142): #check classicalPrimeAdditiveLargeSieve_proved135
-- Historical audit output (142): #check residueVariance_eq_fourier137
-- Historical audit output (142): #check primeResidueVariance_bound137
-- Historical audit output (142): #check exceptionalResidueCount_bound137
-- Historical audit output (142): #check candidate_main_from_mediumPNT137
-- Historical audit output (142): #print PsiMediumPNT134
-- Historical audit output (142): #print RemainingNonPNTInputs135
-- Frozen historical output: #eval "REPAIR 137 VERIFIED-BASELINE CHECKPOINT: new finite-field section follows"

end RemainingAnalytic137

/-! ## 138. Exact low-degree character sums and removal of repeated roots

Repair 137 is verified by the user's complete Lean 4.35.0-rc2 log. Its proof
bodies are preserved. The new work below is locally UNCOMPILED.

This section attacks the remaining finite-field input, not another large-sieve
corollary. It proves the one-root and two-distinct-root character sums, removes
nonzero scalar factors, and retains the correction at zeros of deleted square
factors. It then normalizes the ACTUAL anchor products (the I product omits 0,
and the V product omits t) to sets of roots.

The higher-degree distinct-root Weil estimate remains an explicit input.
No theorem below asserts that this missing input has been proved or imported.
-/
namespace RemainingAnalytic138

open scoped BigOperators
open RemainingAnalytic61 RemainingAnalytic62 RemainingAnalytic63 RemainingAnalytic96
open RemainingAnalytic127 RemainingAnalytic134 RemainingAnalytic135

set_option maxHeartbeats 4000000

/-! ### A. Real-valued quadratic characters and exact changes of variable -/
section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The existing integer-valued quadratic character, cast to the reals. -/
noncomputable def realQuadraticChar138 (x : F) : ℝ := (quadraticChar F x : ℝ)

@[simp] theorem realQuadraticChar_zero138 : realQuadraticChar138 (0 : F) = 0 := by
  simp only [realQuadraticChar138, quadraticChar_zero, Int.cast_zero]

@[simp] theorem realQuadraticChar_one138 : realQuadraticChar138 (1 : F) = 1 := by
  simp only [realQuadraticChar138, map_one, Int.cast_one]

theorem realQuadraticChar_mul138 (x y : F) :
    realQuadraticChar138 (x * y) = realQuadraticChar138 x * realQuadraticChar138 y := by
  simp only [realQuadraticChar138, map_mul, Int.cast_mul]

theorem realQuadraticChar_square138 {x : F} (hx : x ≠ 0) :
    realQuadraticChar138 (x ^ 2) = 1 := by
  unfold realQuadraticChar138
  rw [quadraticChar_sq_one' hx]
  norm_num

theorem realQuadraticChar_abs138 (x : F) : |realQuadraticChar138 x| ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · rcases quadraticChar_dichotomy hx with h | h <;>
      simp only [realQuadraticChar138, h] <;> norm_num

theorem realQuadraticChar_abs_of_ne_zero138 {x : F} (hx : x ≠ 0) :
    |realQuadraticChar138 x| = 1 := by
  rcases quadraticChar_dichotomy hx with h | h <;>
    simp only [realQuadraticChar138, h] <;> norm_num

theorem realQuadraticChar_sum_zero138 (hF : ringChar F ≠ 2) :
    (∑ x : F, realQuadraticChar138 x) = 0 := by
  unfold realQuadraticChar138
  exact_mod_cast quadraticChar_sum_zero hF

/-- An affine change of variable is an exact permutation of the finite field. -/
theorem sum_affine138 (f : F → ℝ) (a b : F) (ha : a ≠ 0) :
    (∑ x : F, f (a * x + b)) = ∑ x : F, f x := by
  apply Finset.sum_bij (fun x _ => a * x + b)
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy hxy
    exact mul_left_cancel₀ ha (add_right_cancel hxy)
  · intro y hy
    refine ⟨(y - b) / a, Finset.mem_univ _, ?_⟩
    field_simp [ha] <;> ring
  · intro x hx
    rfl

/-- Nonzero scalar factors do not change the absolute character sum. -/
theorem characterSum_scalar_abs138 (f : F → F) (c : F) (hc : c ≠ 0) :
    |∑ x : F, realQuadraticChar138 (c * f x)| =
      |∑ x : F, realQuadraticChar138 (f x)| := by
  simp_rw [realQuadraticChar_mul138]
  rw [← Finset.mul_sum, abs_mul, realQuadraticChar_abs_of_ne_zero138 hc, one_mul]

/-- One linear factor gives exact cancellation in odd characteristic. -/
theorem characterSum_one_root138 (hF : ringChar F ≠ 2) (u : F) :
    (∑ x : F, realQuadraticChar138 (x - u)) = 0 := by
  have hh := sum_affine138 (fun x : F => realQuadraticChar138 x) 1 (-u) one_ne_zero
  simpa only [one_mul, ← sub_eq_add_neg, realQuadraticChar_sum_zero138 hF] using hh

/-- The fractional-linear involution, extended by fixing its pole. -/
noncomputable def fractionalInvolution138 (x : F) : F :=
  if x = 1 then 1 else x / (x - 1)

theorem fractional_quotient_ne_one138 {x : F} (hx : x ≠ 1) :
    x / (x - 1) ≠ 1 := by
  intro hh
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have heq := (div_eq_iff hd).mp hh
  have h10 : (1 : F) = 0 := by linear_combination heq
  exact one_ne_zero h10

theorem fractionalInvolution_involutive138 :
    Function.Involutive (fractionalInvolution138 : F → F) := by
  intro x
  by_cases hx : x = 1
  · subst x
    simp [fractionalInvolution138]
  · have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have hy := fractional_quotient_ne_one138 hx
    have hfx : fractionalInvolution138 x = x / (x - 1) := by
      simp only [fractionalInvolution138, if_neg hx]
    rw [hfx]
    simp only [fractionalInvolution138, if_neg hy]
    have hden : x / (x - 1) - 1 = 1 / (x - 1) := by
      field_simp [hd] <;> ring
    rw [hden]
    field_simp [hd]

theorem sum_fractionalInvolution138 (f : F → ℝ) :
    (∑ x : F, f (fractionalInvolution138 x)) = ∑ x : F, f x := by
  apply Finset.sum_bij (fun x _ => fractionalInvolution138 x)
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy hxy
    exact fractionalInvolution_involutive138.injective hxy
  · intro y hy
    exact ⟨fractionalInvolution138 y, Finset.mem_univ _,
      fractionalInvolution_involutive138 y⟩
  · intro x hx
    rfl

/-- The pole contributes exactly one unit; it cannot be silently discarded. -/
theorem character_fractional_identity138 (x : F) :
    realQuadraticChar138 (x * (x - 1)) =
      realQuadraticChar138 (fractionalInvolution138 x) -
        (if x = 1 then (1 : ℝ) else 0) := by
  by_cases hx : x = 1
  · subst x
    simp [fractionalInvolution138]
  · have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have heq : x * (x - 1) = (x / (x - 1)) * (x - 1) ^ 2 := by
      field_simp [hd] <;> ring
    rw [heq, realQuadraticChar_mul138, realQuadraticChar_square138 hd, mul_one]
    simp only [fractionalInvolution138, if_neg hx, sub_zero]

/-- Exact quadratic-character identity, proved by a finite-field involution. -/
theorem characterSum_x_mul_x_sub_one138 (hF : ringChar F ≠ 2) :
    (∑ x : F, realQuadraticChar138 (x * (x - 1))) = -1 := by
  simp_rw [character_fractional_identity138]
  rw [Finset.sum_sub_distrib, sum_fractionalInvolution138,
    realQuadraticChar_sum_zero138 hF]
  simp

/-- Exact sum for any two distinct roots. No Weil theorem is assumed. -/
theorem characterSum_two_roots138 (hF : ringChar F ≠ 2) (u v : F) (huv : u ≠ v) :
    (∑ x : F, realQuadraticChar138 ((x - u) * (x - v))) = -1 := by
  let d : F := v - u
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hchange := sum_affine138
    (fun x : F => realQuadraticChar138 ((x - u) * (x - v))) d u hd
  calc
    (∑ x : F, realQuadraticChar138 ((x - u) * (x - v))) =
        ∑ x : F, realQuadraticChar138 ((d * x + u - u) * (d * x + u - v)) :=
      hchange.symm
    _ = ∑ x : F, realQuadraticChar138 (x * (x - 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have heq : (d * x + u - u) * (d * x + u - v) = d ^ 2 * (x * (x - 1)) := by
        dsimp [d]
        ring
      rw [heq, realQuadraticChar_mul138, realQuadraticChar_square138 hd, one_mul]
    _ = -1 := characterSum_x_mul_x_sub_one138 hF

/-! ### B. Products over actual root sets and exact square-factor correction -/

/-- Monic product with precisely these distinct roots. -/
noncomputable def rootProduct138 (U : Finset F) (x : F) : F := ∏ u ∈ U, (x - u)

/-- The roots that occur in exactly one of the two squarefree factors. -/
def oddRoots138 (U V : Finset F) : Finset F := (U \ V) ∪ (V \ U)

theorem rootProduct_zero_iff138 (U : Finset F) (x : F) :
    rootProduct138 U x = 0 ↔ x ∈ U := by
  unfold rootProduct138
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨u, hu, hxu⟩
    exact (sub_eq_zero.mp hxu).symm ▸ hu
  · intro hx
    exact ⟨x, hx, sub_self x⟩

theorem rootProduct_partition138 (U V : Finset F) (x : F) :
    rootProduct138 U x = rootProduct138 (U \ V) x * rootProduct138 (U ∩ V) x := by
  have hset : U = (U \ V) ∪ (U ∩ V) := by
    ext u
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hd : Disjoint (U \ V) (U ∩ V) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mp hv).2
  calc
    rootProduct138 U x = rootProduct138 ((U \ V) ∪ (U ∩ V)) x :=
      congrArg (fun W : Finset F => rootProduct138 W x) hset
    _ = rootProduct138 (U \ V) x * rootProduct138 (U ∩ V) x :=
      Finset.prod_union hd

theorem oddRoots_disjoint_parts138 (U V : Finset F) : Disjoint (U \ V) (V \ U) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).1

theorem rootProduct_two_families138 (U V : Finset F) (x : F) :
    rootProduct138 U x * rootProduct138 V x =
      rootProduct138 (oddRoots138 U V) x * (rootProduct138 (U ∩ V) x) ^ 2 := by
  have hU := rootProduct_partition138 U V x
  have hV := rootProduct_partition138 V U x
  rw [Finset.inter_comm V U] at hV
  have hodd : rootProduct138 (oddRoots138 U V) x =
      rootProduct138 (U \ V) x * rootProduct138 (V \ U) x :=
    Finset.prod_union (oddRoots_disjoint_parts138 U V)
  rw [hU, hV, hodd]
  ring

theorem oddRoots_card_balance138 (U V : Finset F) :
    (oddRoots138 U V).card + 2 * (U ∩ V).card = U.card + V.card := by
  have hU : (U \ V).card + (U ∩ V).card = U.card := by
    have hset : (U \ V) ∪ (U ∩ V) = U := by
      ext u
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hd : Disjoint (U \ V) (U ∩ V) := by
      apply Finset.disjoint_left.mpr
      intro u hu hv
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mp hv).2
    rw [← Finset.card_union_of_disjoint hd, hset]
  have hV : (V \ U).card + (U ∩ V).card = V.card := by
    have hset : (V \ U) ∪ (U ∩ V) = V := by
      ext u
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hd : Disjoint (V \ U) (U ∩ V) := by
      apply Finset.disjoint_left.mpr
      intro u hu hv
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mp hv).1
    rw [← Finset.card_union_of_disjoint hd, hset]
  have hodd : (oddRoots138 U V).card = (U \ V).card + (V \ U).card :=
    Finset.card_union_of_disjoint (oddRoots_disjoint_parts138 U V)
  omega

/-- Exact value correction at a common root. Away from the common-root set
multiplication by the square contributes one; at a common root it contributes zero. -/
theorem squareDeletion_pointwise_identity138 (U V : Finset F) (x : F) :
    realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x) =
      realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x) -
        (if x ∈ U ∩ V then realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x) else 0) := by
  rw [rootProduct_two_families138]
  by_cases hx : x ∈ U ∩ V
  · have hz : rootProduct138 (U ∩ V) x = 0 := (rootProduct_zero_iff138 _ _).mpr hx
    rw [hz]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      realQuadraticChar_zero138, if_pos hx, sub_self]
  · have hz : rootProduct138 (U ∩ V) x ≠ 0 :=
      fun hh => hx ((rootProduct_zero_iff138 _ _).mp hh)
    rw [realQuadraticChar_mul138, realQuadraticChar_square138 hz, mul_one,
      if_neg hx, sub_zero]

/-- Exact complete-sum formula, including the finite common-root correction. -/
theorem squareDeletion_sum_identity138 (U V : Finset F) :
    (∑ x : F, realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x)) =
      (∑ x : F, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x)) -
        ∑ x ∈ U ∩ V, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x) := by
  have hfilter : (Finset.univ : Finset F).filter
      (fun x : F => x ∈ U ∩ V) = U ∩ V := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [squareDeletion_pointwise_identity138]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter, hfilter]

/-- Each deleted square factor only changes character values at its zeros. -/
theorem squareDeletion_pointwise138 (U V : Finset F) (x : F) :
    |realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x) -
      realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x)| ≤
        if x ∈ U ∩ V then (1 : ℝ) else 0 := by
  rw [rootProduct_two_families138]
  by_cases hx : x ∈ U ∩ V
  · have hz : rootProduct138 (U ∩ V) x = 0 := (rootProduct_zero_iff138 _ _).mpr hx
    rw [hz]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      realQuadraticChar_zero138, zero_sub, abs_neg, if_pos hx]
    exact realQuadraticChar_abs138 _
  · have hz : rootProduct138 (U ∩ V) x ≠ 0 :=
      fun hh => hx ((rootProduct_zero_iff138 _ _).mp hh)
    rw [realQuadraticChar_mul138, realQuadraticChar_square138 hz, mul_one,
      sub_self, abs_zero, if_neg hx]

/-- Complete-sum correction; no unjustified deletion of the zero set. -/
theorem squareDeletion_sum_bound138 (U V : Finset F) :
    |(∑ x : F, realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x)) -
      (∑ x : F, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x))| ≤
        ((U ∩ V).card : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : F,
        |realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x) -
          realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x)| :=
      RemainingAnalytic117.abs_finset_sum_le_sum_abs117 _ _
    _ ≤ ∑ x : F, if x ∈ U ∩ V then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun x hx => squareDeletion_pointwise138 U V x)
    _ = ((U ∩ V).card : ℝ) := by
      have hfilter : (Finset.univ : Finset F).filter
          (fun x : F => x ∈ U ∩ V) = U ∩ V := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← Finset.sum_filter, hfilter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The degree-one monic product has sum zero. -/
theorem rootCharacterSum_card_one138 (hF : ringChar F ≠ 2)
    (U : Finset F) (hU : U.card = 1) :
    (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) = 0 := by
  obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hU
  simpa only [rootProduct138, Finset.prod_singleton] using characterSum_one_root138 hF u

/-- The degree-two monic product has sum minus one. -/
theorem rootCharacterSum_card_two138 (hF : ringChar F ≠ 2)
    (U : Finset F) (hU : U.card = 2) :
    (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) = -1 := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hU
  simpa only [rootProduct138, Finset.prod_pair huv] using characterSum_two_roots138 hF u v huv

/-- Exact low-degree results give the usual degree-minus-one bound. -/
theorem rootCharacterSum_lowDegree138 (hF : ringChar F ≠ 2)
    (U : Finset F) (hne : U.Nonempty) (hU : U.card ≤ 2)
    (R : ℝ) (hR : 1 ≤ R) :
    |∑ x : F, realQuadraticChar138 (rootProduct138 U x)| ≤ ((U.card : ℝ) - 1) * R := by
  have hcpos : 0 < U.card := Finset.card_pos.mpr hne
  have hcases : U.card = 1 ∨ U.card = 2 := by omega
  rcases hcases with hc | hc
  · rw [rootCharacterSum_card_one138 hF U hc, hc]
    norm_num
  · rw [rootCharacterSum_card_two138 hF U hc, hc]
    convert hR using 1 <;> norm_num

/-- An already-proved bound for the odd-multiplicity roots transfers to the
original two-family product. The finite correction is absorbed explicitly. -/
theorem twoFamily_bound_from_oddRoots138 (U V : Finset F) (R : ℝ) (hR : 1 ≤ R)
    (H : |∑ x : F, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x)| ≤
      (((oddRoots138 U V).card : ℝ) - 1) * R) :
    |∑ x : F, realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x)| ≤
      ((U.card : ℝ) + (V.card : ℝ)) * R := by
  have hcorr := squareDeletion_sum_bound138 U V
  have htri : |∑ x : F, realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x)| ≤
      |(∑ x : F, realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x)) -
        (∑ x : F, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x))| +
      |∑ x : F, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x)| := by
    simpa only [sub_add_cancel] using abs_add_le
      ((∑ x : F, realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x)) -
        (∑ x : F, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x)))
      (∑ x : F, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x))
  have hcard : ((oddRoots138 U V).card : ℝ) + 2 * ((U ∩ V).card : ℝ) =
      (U.card : ℝ) + (V.card : ℝ) := by exact_mod_cast oddRoots_card_balance138 U V
  have hC0 : (0 : ℝ) ≤ ((U ∩ V).card : ℝ) := by positivity
  have hCR : ((U ∩ V).card : ℝ) ≤ ((U ∩ V).card : ℝ) * R := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hC0
  have hCR0 : 0 ≤ ((U ∩ V).card : ℝ) * R := mul_nonneg hC0 (by linarith)
  have hcardR := congrArg (fun z : ℝ => z * R) hcard
  nlinarith only [hcorr, htri, H, hcardR, hCR, hCR0, hR]

/-- Scalar times a product over an injectively indexed root family. -/
theorem scalarRootProduct138 (I : Finset ℕ) (f : ℕ → F)
    (hf : Set.InjOn f I) (a x : F) :
    (∏ i ∈ I, a * (x - f i)) = a ^ I.card * rootProduct138 (I.image f) x := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  unfold rootProduct138
  rw [Finset.prod_image hf]

end FiniteField

/-! ### C. The source's two actual root families, with their omitted indices -/

/-- I indices are 1,...,ell-1, NOT 0,...,ell-1. -/
def iIndices138 (ell : ℕ) : Finset ℕ := (Finset.range ell).filter (fun i => 1 ≤ i)

/-- V indices are 0,...,h-1 except t. -/
def vIndices138 (t h : ℕ) : Finset ℕ := (Finset.range h).filter (fun v => v ≠ t)

theorem iIndices_card138 (ell : ℕ) (hell : 0 < ell) : (iIndices138 ell).card = ell - 1 := by
  have heq : iIndices138 ell = (Finset.range ell).erase 0 := by
    ext i
    simp only [iIndices138, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    omega
  rw [heq, Finset.card_erase_of_mem (Finset.mem_range.mpr hell), Finset.card_range]

theorem vIndices_card138 (t h : ℕ) (ht : t < h) : (vIndices138 t h).card = h - 1 := by
  have heq : vIndices138 t h = (Finset.range h).erase t := by
    ext v
    simp only [vIndices138, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    tauto
  rw [heq, Finset.card_erase_of_mem (Finset.mem_range.mpr ht), Finset.card_range]

/-- Canonical finite-field roots, not the natural representatives in Repair 61. -/
noncomputable def iRoots138 (lam : ℕ) [Fact lam.Prime] (r ell : ℕ) : Finset (ZMod lam) :=
  (iIndices138 ell).image (fun i : ℕ => (i : ZMod lam) / (r : ZMod lam))

noncomputable def vRoots138 (lam : ℕ) [Fact lam.Prime] (j t h : ℕ) : Finset (ZMod lam) :=
  (vIndices138 t h).image
    (fun v : ℕ => ((v : ZMod lam) - (t : ZMod lam)) / (j : ZMod lam))

theorem natCast_injective_below138 {lam i k : ℕ} [Fact lam.Prime]
    (hi : i < lam) (hk : k < lam) (heq : (i : ZMod lam) = (k : ZMod lam)) : i = k := by
  have hv := congrArg (fun z : ZMod lam => z.val) heq
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk] using hv

theorem iRoots_injective138 {lam r ell : ℕ} [Fact lam.Prime]
    (hr : (r : ZMod lam) ≠ 0) (hell : ell ≤ lam) :
    Set.InjOn (fun i : ℕ => (i : ZMod lam) / (r : ZMod lam)) (iIndices138 ell) := by
  intro i hi k hk heq
  have hiL : i < lam := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hi).1) hell
  have hkL : k < lam := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hk).1) hell
  have hcast : (i : ZMod lam) = (k : ZMod lam) := (div_left_inj' hr).mp heq
  exact natCast_injective_below138 hiL hkL hcast

theorem vRoots_injective138 {lam j t h : ℕ} [Fact lam.Prime]
    (hj : (j : ZMod lam) ≠ 0) (hh : h ≤ lam) :
    Set.InjOn (fun v : ℕ => ((v : ZMod lam) - (t : ZMod lam)) / (j : ZMod lam))
      (vIndices138 t h) := by
  intro v hv w hw heq
  have hvL : v < lam := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hv).1) hh
  have hwL : w < lam := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hw).1) hh
  have hd : (v : ZMod lam) - (t : ZMod lam) = (w : ZMod lam) - (t : ZMod lam) :=
    (div_left_inj' hj).mp heq
  exact natCast_injective_below138 hvL hwL (sub_left_inj.mp hd)

theorem iRoots_card138 {lam r ell : ℕ} [Fact lam.Prime]
    (hr : (r : ZMod lam) ≠ 0) (hell : 0 < ell) (heL : ell ≤ lam) :
    (iRoots138 lam r ell).card = ell - 1 := by
  unfold iRoots138
  exact (Finset.card_image_iff.mpr (iRoots_injective138 hr heL)).trans
    (iIndices_card138 ell hell)

theorem vRoots_card138 {lam j t h : ℕ} [Fact lam.Prime]
    (hj : (j : ZMod lam) ≠ 0) (ht : t < h) (hhL : h ≤ lam) :
    (vRoots138 lam j t h).card = h - 1 := by
  unfold vRoots138
  exact (Finset.card_image_iff.mpr (vRoots_injective138 hj hhL)).trans
    (vIndices_card138 t h ht)

theorem anchorIProduct_roots138 {lam r ell : ℕ} [Fact lam.Prime]
    (hr : (r : ZMod lam) ≠ 0) (heL : ell ≤ lam) (z : ZMod lam) :
    anchorIProduct61 r ell lam z =
      (r : ZMod lam) ^ (iIndices138 ell).card * rootProduct138 (iRoots138 lam r ell) z := by
  calc
    anchorIProduct61 r ell lam z = ∏ i ∈ iIndices138 ell,
        (r : ZMod lam) * (z - (i : ZMod lam) / (r : ZMod lam)) := by
      apply Finset.prod_congr rfl
      intro i hi
      field_simp [hr] <;> ring
    _ = (r : ZMod lam) ^ (iIndices138 ell).card * rootProduct138 (iRoots138 lam r ell) z :=
      scalarRootProduct138 (iIndices138 ell) _ (iRoots_injective138 hr heL) _ _

theorem anchorVProduct_roots138 {lam j t h : ℕ} [Fact lam.Prime]
    (hj : (j : ZMod lam) ≠ 0) (hhL : h ≤ lam) (z : ZMod lam) :
    anchorVProduct61 j t h lam z =
      (j : ZMod lam) ^ (vIndices138 t h).card * rootProduct138 (vRoots138 lam j t h) z := by
  calc
    anchorVProduct61 j t h lam z = ∏ v ∈ vIndices138 t h,
        (j : ZMod lam) * (z - ((v : ZMod lam) - (t : ZMod lam)) / (j : ZMod lam)) := by
      apply Finset.prod_congr rfl
      intro v hv
      field_simp [hj] <;> ring
    _ = (j : ZMod lam) ^ (vIndices138 t h).card * rootProduct138 (vRoots138 lam j t h) z :=
      scalarRootProduct138 (vIndices138 t h) _ (vRoots_injective138 hj hhL) _ _

/-- The original scalar and both slopes are removed without changing the
absolute sum. All products use their original multiplicities. -/
theorem linearProduct_abs_eq_rootPair138 {lam r j t h ell : ℕ} (hp : lam.Prime)
    (hr : (r : ZMod lam) ≠ 0) (hj : (j : ZMod lam) ≠ 0)
    (heL : ell ≤ lam) (hhL : h ≤ lam) (c : ZMod lam) (hc : c ≠ 0) :
    letI : Fact lam.Prime := ⟨hp⟩
    |((linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| =
      |∑ z : ZMod lam, realQuadraticChar138
        (rootProduct138 (iRoots138 lam r ell) z * rootProduct138 (vRoots138 lam j t h) z)| := by
  letI : Fact lam.Prime := ⟨hp⟩
  let C : ZMod lam := c * (r : ZMod lam) ^ (iIndices138 ell).card *
    (j : ZMod lam) ^ (vIndices138 t h).card
  have hC : C ≠ 0 := mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ hr)) (pow_ne_zero _ hj)
  have heq : ((linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ) =
      ∑ z : ZMod lam, realQuadraticChar138
        (C * (rootProduct138 (iRoots138 lam r ell) z * rootProduct138 (vRoots138 lam j t h) z)) := by
    unfold linearProductQuadraticSum96
    push_cast
    apply Finset.sum_congr rfl
    intro z hz
    rw [quadraticCharValue_of_prime62 hp]
    change realQuadraticChar138 (c * anchorIProduct61 r ell lam z * anchorVProduct61 j t h lam z) = _
    rw [anchorIProduct_roots138 hr heL, anchorVProduct_roots138 hj hhL]
    congr 1
    dsimp [C]
    ring
  rw [heq]
  exact characterSum_scalar_abs138 _ C hC

/-! ### D. Verify an odd-multiplicity root for every legal tuple -/

/-- Elementary consequences of the original separation hypothesis. -/
theorem legalPrime_geometry138 {r j t h ell lam : ℕ}
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 0 < ell) (ht : t < h)
    (hsep : 2 * r * max h ell < lam) :
    2 < lam ∧ h ≤ lam ∧ ell ≤ lam ∧ j + r * t < lam ∧
      (∀ v : ℕ, v < h → r * v < lam) := by
  have hr2 : 2 ≤ r := by omega
  have hH1 : 1 ≤ max h ell := by omega
  have hhH : h ≤ max h ell := le_max_left _ _
  have heH : ell ≤ max h ell := le_max_right _ _
  have hRH : r * max h ell < lam := by
    have hnonneg : 0 ≤ r * max h ell := Nat.zero_le _
    nlinarith only [hsep, hnonneg]
  have hH_le : max h ell ≤ r * max h ell := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (max h ell) (show 1 ≤ r by omega)
  have hr_le : r ≤ r * max h ell := by
    simpa only [mul_one] using Nat.mul_le_mul_left r hH1
  have hHL : max h ell < lam := lt_of_le_of_lt hH_le hRH
  have hrL : r < lam := lt_of_le_of_lt hr_le hRH
  have hrt : r * (t + 1) ≤ r * h := Nat.mul_le_mul_left r (by omega)
  have hrh : r * h ≤ r * max h ell := Nat.mul_le_mul_left r hhH
  have hcross : j + r * t < lam := by
    have hlt : j + r * t < r * (t + 1) := by nlinarith only [hjr]
    exact lt_of_lt_of_le hlt (le_trans hrt (le_trans hrh hRH.le))
  refine ⟨by omega, by omega, by omega, hcross, ?_⟩
  intro v hv
  have hvh : r * v ≤ r * h := Nat.mul_le_mul_left r hv.le
  exact lt_of_le_of_lt (le_trans hvh hrh) hRH

/-- For ell>=2, the I root 1/r cannot be a V root. The modular equality
would force 0<j<r to be divisible by r, after using the separation bound. -/
theorem firstIRoot_not_vRoots138 {lam r j t h ell : ℕ} (hp : lam.Prime)
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 2 ≤ ell) (ht : t < h)
    (hsep : 2 * r * max h ell < lam) :
    letI : Fact lam.Prime := ⟨hp⟩
    (1 : ZMod lam) / (r : ZMod lam) ∉ vRoots138 lam j t h := by
  letI : Fact lam.Prime := ⟨hp⟩
  have hepos : 0 < ell := by omega
  have hr0 := r_nonzero_mod63 hp hj hjr hh hepos hsep
  have hj0 := j_nonzero_mod63 hp hj hjr hh hepos hsep
  have hgeo := legalPrime_geometry138 hj hjr hh hepos ht hsep
  intro hz
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hz
  have hvh : v < h := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  have heq' : (1 : ZMod lam) / (r : ZMod lam) =
      ((v : ZMod lam) - (t : ZMod lam)) / (j : ZMod lam) := heq.symm
  have hcross : (1 : ZMod lam) * (j : ZMod lam) =
      ((v : ZMod lam) - (t : ZMod lam)) * (r : ZMod lam) :=
    (div_eq_div_iff hr0 hj0).mp heq'
  have hcast : ((j + r * t : ℕ) : ZMod lam) = ((r * v : ℕ) : ZMod lam) := by
    push_cast
    linear_combination hcross
  have hnat : j + r * t = r * v :=
    natCast_injective_below138 hgeo.2.2.2.1 (hgeo.2.2.2.2 v hvh) hcast
  have hmod := congrArg (fun n : ℕ => n % r) hnat
  have hjz : j = 0 := by
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
      add_zero, Nat.mod_eq_of_lt hjr] using hmod
  omega

/-- At least one root survives square deletion. This is a proved algebraic
fact about the actual legal tuple, not an extra nonsquare hypothesis. -/
theorem anchorOddRoots_nonempty138 {lam r j t h ell : ℕ} (hp : lam.Prime)
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 0 < ell) (ht : t < h)
    (hnp : h ≠ 1 ∨ ell ≠ 1) (hsep : 2 * r * max h ell < lam) :
    letI : Fact lam.Prime := ⟨hp⟩
    (oddRoots138 (iRoots138 lam r ell) (vRoots138 lam j t h)).Nonempty := by
  letI : Fact lam.Prime := ⟨hp⟩
  by_cases he2 : 2 ≤ ell
  · have hI : (1 : ZMod lam) / (r : ZMod lam) ∈ iRoots138 lam r ell := by
      apply Finset.mem_image.mpr
      refine ⟨1, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl⟩
      · simp
    have hV := firstIRoot_not_vRoots138 hp hj hjr hh he2 ht hsep
    exact ⟨_, Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hI, hV⟩))⟩
  · have he1 : ell = 1 := by omega
    have hh2 : 2 ≤ h := by omega
    have hI : iRoots138 lam r ell = ∅ := by
      subst ell
      simp [iRoots138, iIndices138, Finset.range_one]
    have hindex : ∃ v : ℕ, v ∈ vIndices138 t h := by
      by_cases ht0 : t = 0
      · exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩⟩
      · exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, Ne.symm ht0⟩⟩
    obtain ⟨v, hv⟩ := hindex
    have hV : ((v : ZMod lam) - (t : ZMod lam)) / (j : ZMod lam) ∈ vRoots138 lam j t h :=
      Finset.mem_image.mpr ⟨v, hv, rfl⟩
    refine ⟨_, Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hV, ?_⟩))⟩
    rw [hI]
    exact Finset.notMem_empty _

/-! ### E. The only retained cancellation input: at least three distinct roots -/

/-- The standard distinct-root Weil estimate, restricted to prime fields and
monic split polynomials of degree at least three. THIS IS AN INPUT, NOT A PROOF.
The low-degree statements below are proved without this proposition. -/
def DistinctRootWeil138 : Prop :=
  ∀ lam : ℕ, ∀ hp : lam.Prime, lam ≠ 2 →
    letI : Fact lam.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod lam), 3 ≤ U.card →
      |∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)| ≤
        ((U.card : ℝ) - 1) * Real.sqrt (lam : ℝ)

/-- Complete distinct-root bound: only degree>=3 invokes the retained input. -/
theorem distinctRootWeil_all_degrees138 (HW : DistinctRootWeil138)
    (lam : ℕ) (hp : lam.Prime) (hl2 : lam ≠ 2) :
    letI : Fact lam.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod lam), U.Nonempty →
      |∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)| ≤
        ((U.card : ℝ) - 1) * Real.sqrt (lam : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  intro U hU
  by_cases hc : U.card ≤ 2
  · have hchar : ringChar (ZMod lam) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hl2
    have hsqrt : 1 ≤ Real.sqrt (lam : ℝ) := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (lam : ℝ) by exact_mod_cast hp.one_le)
    exact rootCharacterSum_lowDegree138 hchar U hU hc _ hsqrt
  · exact HW lam hp hl2 U (by omega)

/-- A local cancellation bound for the actual odd-root set is all the project
needs. Scalar normalization and the correction at zeros of square factors are supplied. -/
theorem linearProductWeil_from_oddRoot_bound138 {lam r j t h ell : ℕ} (hp : lam.Prime)
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 0 < ell) (ht : t < h)
    (hsep : 2 * r * max h ell < lam)
    (c : ZMod lam) (hc : c ≠ 0)
    (HB : letI : Fact lam.Prime := ⟨hp⟩
      |∑ z : ZMod lam, realQuadraticChar138
          (rootProduct138 (oddRoots138 (iRoots138 lam r ell) (vRoots138 lam j t h)) z)| ≤
        (((oddRoots138 (iRoots138 lam r ell) (vRoots138 lam j t h)).card : ℝ) - 1) *
          Real.sqrt (lam : ℝ)) :
    |((linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| ≤
      2 * (max h ell : ℝ) * Real.sqrt (lam : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  have hgeo := legalPrime_geometry138 hj hjr hh hell ht hsep
  have hr0 := r_nonzero_mod63 hp hj hjr hh hell hsep
  have hj0 := j_nonzero_mod63 hp hj hjr hh hell hsep
  have hsqrt : 1 ≤ Real.sqrt (lam : ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (lam : ℝ) by exact_mod_cast hp.one_le)
  rw [linearProduct_abs_eq_rootPair138 hp hr0 hj0 hgeo.2.2.1 hgeo.2.1 c hc]
  have hbound := twoFamily_bound_from_oddRoots138
    (iRoots138 lam r ell) (vRoots138 lam j t h) _ hsqrt HB
  have hI : (iRoots138 lam r ell).card ≤ ell := by
    rw [iRoots_card138 hr0 hell hgeo.2.2.1]
    omega
  have hV : (vRoots138 lam j t h).card ≤ h := by
    rw [vRoots_card138 hj0 ht hgeo.2.1]
    omega
  have hcard : ((iRoots138 lam r ell).card : ℝ) + ((vRoots138 lam j t h).card : ℝ) ≤
      2 * (max h ell : ℝ) := by
    exact_mod_cast (show (iRoots138 lam r ell).card + (vRoots138 lam j t h).card ≤
      2 * max h ell by omega)
  exact le_trans hbound (mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _))

/-- Cancellation can reduce a high displayed degree to one or two odd roots.
This case is elementary too, regardless of how many common roots were deleted. -/
theorem linearProductWeil_fewOddRoots138 {lam r j t h ell : ℕ} (hp : lam.Prime)
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 0 < ell) (ht : t < h)
    (hnp : h ≠ 1 ∨ ell ≠ 1) (hsep : 2 * r * max h ell < lam)
    (hodd : letI : Fact lam.Prime := ⟨hp⟩
      (oddRoots138 (iRoots138 lam r ell) (vRoots138 lam j t h)).card ≤ 2)
    (c : ZMod lam) (hc : c ≠ 0) :
    |((linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| ≤
      2 * (max h ell : ℝ) * Real.sqrt (lam : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  have hgeo := legalPrime_geometry138 hj hjr hh hell ht hsep
  have hne := anchorOddRoots_nonempty138 hp hj hjr hh hell ht hnp hsep
  have hl2 : lam ≠ 2 := by omega
  have hchar : ringChar (ZMod lam) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n] using hl2
  have hsqrt : 1 ≤ Real.sqrt (lam : ℝ) := by
    simpa using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ (lam : ℝ) by exact_mod_cast hp.one_le)
  exact linearProductWeil_from_oddRoot_bound138 hp hj hjr hh hell ht hsep c hc
    (rootCharacterSum_lowDegree138 hchar _ hne hodd _ hsqrt)

/-- Actual project cases with degree at most two are proved with no Weil input.
The total displayed degree is (ell-1)+(h-1), so h+ell<=4 is the right cutoff. -/
theorem linearProductWeil_lowDegree138 {lam r j t h ell : ℕ} (hp : lam.Prime)
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 0 < ell) (ht : t < h)
    (hnp : h ≠ 1 ∨ ell ≠ 1) (hsep : 2 * r * max h ell < lam)
    (hdegree : h + ell ≤ 4) (c : ZMod lam) (hc : c ≠ 0) :
    |((linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| ≤
      2 * (max h ell : ℝ) * Real.sqrt (lam : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  have hgeo := legalPrime_geometry138 hj hjr hh hell ht hsep
  have hr0 := r_nonzero_mod63 hp hj hjr hh hell hsep
  have hj0 := j_nonzero_mod63 hp hj hjr hh hell hsep
  have hI := iRoots_card138 hr0 hell hgeo.2.2.1
  have hV := vRoots_card138 hj0 ht hgeo.2.1
  have hbalance := oddRoots_card_balance138 (iRoots138 lam r ell) (vRoots138 lam j t h)
  have hdegree' : (oddRoots138 (iRoots138 lam r ell) (vRoots138 lam j t h)).card ≤ 2 := by omega
  exact linearProductWeil_fewOddRoots138 hp hj hjr hh hell ht hnp hsep hdegree' c hc

/-- Full conversion from the standard distinct-root estimate to the old
large-modulus two-family input, including its scalar and possible common roots. -/
theorem largeModulusWeil_from_distinctRoots138 (HW : DistinctRootWeil138) :
    LargeModulusLinearProductWeil127 := by
  intro r j t h ell lam hj hjr hh hell ht hnp hp hsep hlarge c hc
  letI : Fact lam.Prime := ⟨hp⟩
  have hgeo := legalPrime_geometry138 hj hjr hh hell ht hsep
  have hl2 : lam ≠ 2 := by omega
  have hne := anchorOddRoots_nonempty138 hp hj hjr hh hell ht hnp hsep
  have HB := distinctRootWeil_all_degrees138 HW lam hp hl2 _ hne
  exact linearProductWeil_from_oddRoot_bound138 hp hj hjr hh hell ht hsep c hc HB

/-! ### F. Integrated sufficient endgame; four analytic inputs still remain -/

/-- This replaces the specialized two-family Weil input by a standard monic
 distinct-root estimate. It is a sufficient interface, NOT an equivalence claim.
 Quantitative PNT is still a separate argument to the final theorem. -/
structure RemainingNonPNTInputs138 where
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  distinct_root_weil : DistinctRootWeil138

theorem RemainingNonPNTInputs138.to135 (H : RemainingNonPNTInputs138) : RemainingNonPNTInputs135 where
  sparse_good_prime_count := H.sparse_good_prime_count
  harman_bad_density := H.harman_bad_density
  large_modulus_weil := largeModulusWeil_from_distinctRoots138 H.distinct_root_weil

theorem candidate_main_from_mediumPNT138 (HP : PsiMediumPNT134) (H : RemainingNonPNTInputs138) :
    MainStatement := candidate_main_from_mediumPNT135 HP H.to135

theorem positive_lower_density_from_mediumPNT138 (HP : PsiMediumPNT134) (H : RemainingNonPNTInputs138) :
    PositiveLowerDensity D6 := positive_lower_density_from_mediumPNT135 HP H.to135

-- Historical audit output (142): #print axioms realQuadraticChar_sum_zero138
-- Historical audit output (142): #print axioms sum_affine138
-- Historical audit output (142): #print axioms characterSum_scalar_abs138
-- Historical audit output (142): #print axioms fractionalInvolution_involutive138
-- Historical audit output (142): #print axioms characterSum_x_mul_x_sub_one138
-- Historical audit output (142): #print axioms characterSum_two_roots138
-- Historical audit output (142): #print axioms rootProduct_two_families138
-- Historical audit output (142): #print axioms oddRoots_card_balance138
-- Historical audit output (142): #print axioms squareDeletion_sum_identity138
-- Historical audit output (142): #print axioms squareDeletion_sum_bound138
-- Historical audit output (142): #print axioms rootCharacterSum_lowDegree138
-- Historical audit output (142): #print axioms twoFamily_bound_from_oddRoots138
-- Historical audit output (142): #print axioms iRoots_injective138
-- Historical audit output (142): #print axioms vRoots_injective138
-- Historical audit output (142): #print axioms anchorIProduct_roots138
-- Historical audit output (142): #print axioms anchorVProduct_roots138
-- Historical audit output (142): #print axioms linearProduct_abs_eq_rootPair138
-- Historical audit output (142): #print axioms firstIRoot_not_vRoots138
-- Historical audit output (142): #print axioms anchorOddRoots_nonempty138
-- Historical audit output (142): #print axioms linearProductWeil_fewOddRoots138
-- Historical audit output (142): #print axioms linearProductWeil_lowDegree138
-- Historical audit output (142): #print axioms distinctRootWeil_all_degrees138
-- Historical audit output (142): #print axioms largeModulusWeil_from_distinctRoots138
-- Historical audit output (142): #print axioms candidate_main_from_mediumPNT138
-- Historical audit output (142): #print axioms positive_lower_density_from_mediumPNT138
-- Historical audit output (142): #check linearProductWeil_lowDegree138
-- Historical audit output (142): #check candidate_main_from_mediumPNT138
-- Historical audit output (142): #print DistinctRootWeil138
-- Historical audit output (142): #print RemainingNonPNTInputs138
-- Frozen historical output: #eval "REPAIR 138 REPAIRED CHECKPOINT: inversion and odd-degree normalization follow"

end RemainingAnalytic138

/-! ## 139. Inversion at a root and an odd-degree normalized Weil frontier

The finite-field reduction below keeps both correction terms: the common-root
correction in Repair 138 and the single missing-point correction under inversion.
For an even-cardinality root set U and a in U, the map x=a+1/y gives
  sum chi(P_U) = chi(c) * sum chi(P_V) - 1,
where V={1/(u-a) : u in U, u != a} and |V|=|U|-1.
Thus only odd degrees need a nontrivial Weil estimate. A separate affine change
of variables reduces that input to root sets containing 0 and 1.

These scripts are locally UNCOMPILED. The odd-degree estimate itself, quantitative
PNT, sparse prime supply and Harman bad-set density remain explicit inputs.
-/
namespace RemainingAnalytic139

open scoped BigOperators
open RemainingAnalytic127 RemainingAnalytic134 RemainingAnalytic135
open RemainingAnalytic138

set_option maxHeartbeats 4000000

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Inversion, with the field convention 0^-1=0, followed by translation is
an exact permutation of the WHOLE field. Its value at zero is a. -/
theorem sum_inverse_translate139 (f : F → ℝ) (a : F) :
    (∑ y : F, f (a + y⁻¹)) = ∑ x : F, f x := by
  apply Finset.sum_bij (fun y _ => a + y⁻¹)
  · intro y hy
    exact Finset.mem_univ _
  · intro x hx y hy hxy
    have hi : x⁻¹ = y⁻¹ := add_left_cancel hxy
    have hh := congrArg (fun z : F => z⁻¹) hi
    simpa only [inv_inv] using hh
  · intro x hx
    refine ⟨(x - a)⁻¹, Finset.mem_univ _, ?_⟩
    rw [inv_inv]
    ring
  · intro y hy
    rfl

/-- A nonzero element to an even power is a nonzero square. -/
theorem realQuadraticChar_even_pow139 (x : F) (hx : x ≠ 0)
    (d : ℕ) (hd : Even d) : realQuadraticChar138 (x ^ d) = 1 := by
  obtain ⟨k, hk⟩ := hd
  have heq : x ^ d = (x ^ k) ^ 2 := by
    rw [hk, pow_add, pow_two]
  rw [heq]
  exact realQuadraticChar_square138 (pow_ne_zero _ hx)

/-- Polynomial numerator after inversion at a chosen root. -/
noncomputable def reciprocalProduct139 (U : Finset F) (a y : F) : F :=
  ∏ u ∈ U.erase a, (1 + (a - u) * y)

/-- The surviving roots after inversion; the index type is explicitly F. -/
noncomputable def reciprocalRoots139 (U : Finset F) (a : F) : Finset F :=
  (U.erase a).image (fun u : F => (u - a)⁻¹)

/-- The nonzero leading scalar of the reciprocal polynomial. -/
noncomputable def reciprocalScalar139 (U : Finset F) (a : F) : F :=
  ∏ u ∈ U.erase a, (a - u)

theorem reciprocalMap_injOn139 (U : Finset F) (a : F) :
    Set.InjOn (fun u : F => (u - a)⁻¹) (U.erase a) := by
  intro u hu v hv huv
  have hh := congrArg (fun z : F => z⁻¹) huv
  have hsub : u - a = v - a := by simpa only [inv_inv] using hh
  exact sub_left_inj.mp hsub

theorem reciprocalRoots_card139 (U : Finset F) (a : F) (ha : a ∈ U) :
    (reciprocalRoots139 U a).card = U.card - 1 := by
  unfold reciprocalRoots139
  exact (Finset.card_image_iff.mpr (reciprocalMap_injOn139 U a)).trans
    (Finset.card_erase_of_mem ha)

theorem reciprocalRoots_zero_notMem139 (U : Finset F) (a : F) :
    (0 : F) ∉ reciprocalRoots139 U a := by
  intro hz
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hz
  have hnonzero : u - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hu).1
  exact (inv_ne_zero hnonzero) heq

theorem reciprocalScalar_ne_zero139 (U : Finset F) (a : F) :
    reciprocalScalar139 U a ≠ 0 := by
  unfold reciprocalScalar139
  apply Finset.prod_ne_zero_iff.mpr
  intro u hu
  exact sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hu).1)

@[simp] theorem reciprocalProduct_zero139 (U : Finset F) (a : F) :
    reciprocalProduct139 U a 0 = 1 := by
  simp only [reciprocalProduct139, mul_zero, add_zero, Finset.prod_const_one]

/-- Exact scalar normalization of the inverted polynomial. -/
theorem reciprocalProduct_roots139 (U : Finset F) (a y : F) :
    reciprocalProduct139 U a y =
      reciprocalScalar139 U a * rootProduct138 (reciprocalRoots139 U a) y := by
  have hterm : ∀ u ∈ U.erase a,
      1 + (a - u) * y = (a - u) * (y - (u - a)⁻¹) := by
    intro u hu
    have hnonzero : u - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hu).1
    rw [← one_div]
    field_simp [hnonzero] <;> ring
  calc
    reciprocalProduct139 U a y =
        ∏ u ∈ U.erase a, (a - u) * (y - (u - a)⁻¹) :=
      Finset.prod_congr rfl hterm
    _ = (∏ u ∈ U.erase a, (a - u)) *
        (∏ u ∈ U.erase a, (y - (u - a)⁻¹)) := Finset.prod_mul_distrib
    _ = reciprocalScalar139 U a * rootProduct138 (reciprocalRoots139 U a) y := by
      unfold reciprocalScalar139 rootProduct138 reciprocalRoots139
      rw [Finset.prod_image (reciprocalMap_injOn139 U a)]

/-- The degree is U.card, not the number of remaining roots. The extra inverse
factor comes from the root at a and must be retained before using parity. -/
theorem rootProduct_reciprocal139 (U : Finset F) (a : F) (ha : a ∈ U)
    (y : F) (hy : y ≠ 0) :
    rootProduct138 U (a + y⁻¹) =
      (y⁻¹) ^ U.card * reciprocalProduct139 U a y := by
  have hterm : ∀ u ∈ U.erase a,
      a + y⁻¹ - u = y⁻¹ * (1 + (a - u) * y) := by
    intro u hu
    rw [← one_div]
    field_simp [hy] <;> ring
  have hcard : (U.erase a).card + 1 = U.card := by
    rw [Finset.card_erase_of_mem ha]
    have hpos : 0 < U.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  calc
    rootProduct138 U (a + y⁻¹) =
        (a + y⁻¹ - a) * (∏ u ∈ U.erase a, (a + y⁻¹ - u)) :=
      (Finset.mul_prod_erase U (fun u : F => a + y⁻¹ - u) ha).symm
    _ = y⁻¹ * (∏ u ∈ U.erase a, y⁻¹ * (1 + (a - u) * y)) := by
      have hfirst : a + y⁻¹ - a = y⁻¹ := by ring
      rw [hfirst]
      exact congrArg (fun z : F => y⁻¹ * z) (Finset.prod_congr rfl hterm)
    _ = y⁻¹ * ((y⁻¹) ^ (U.erase a).card * reciprocalProduct139 U a y) := by
      simp only [reciprocalProduct139, Finset.prod_mul_distrib, Finset.prod_const]
    _ = (y⁻¹) ^ U.card * reciprocalProduct139 U a y := by
      rw [← hcard, pow_succ]
      ring

/-- At y=0 the old product vanishes, while the reciprocal numerator equals one.
This is the exact source of the -1 correction in the complete character sum. -/
theorem reciprocal_character_identity139 (U : Finset F) (a : F) (ha : a ∈ U)
    (heven : Even U.card) (y : F) :
    realQuadraticChar138 (rootProduct138 U (a + y⁻¹)) =
      realQuadraticChar138 (reciprocalProduct139 U a y) -
        (if y = 0 then (1 : ℝ) else 0) := by
  by_cases hy : y = 0
  · subst y
    have hz : rootProduct138 U a = 0 := (rootProduct_zero_iff138 U a).mpr ha
    -- The exported goal was `0 = 1 - if True then 1 else 0`.
    -- Evaluate the residual Boolean branch explicitly; do not rely on a
    -- syntactically matched `if_pos rfl` after the condition has reduced.
    simp only [inv_zero, add_zero, hz, realQuadraticChar_zero138,
      reciprocalProduct_zero139, realQuadraticChar_one138] <;> norm_num
  · rw [rootProduct_reciprocal139 U a ha y hy, realQuadraticChar_mul138,
      realQuadraticChar_even_pow139 y⁻¹ (inv_ne_zero hy) U.card heven, one_mul,
      if_neg hy, sub_zero]

/-- Exact even-to-odd degree transformation, with both sign and pole term. -/
theorem characterSum_even_reciprocal139 (U : Finset F) (a : F) (ha : a ∈ U)
    (heven : Even U.card) :
    (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) =
      realQuadraticChar138 (reciprocalScalar139 U a) *
        (∑ y : F, realQuadraticChar138 (rootProduct138 (reciprocalRoots139 U a) y)) - 1 := by
  have hdelta : (∑ y : F, if y = 0 then (1 : ℝ) else 0) = 1 := by simp
  calc
    (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) =
        ∑ y : F, realQuadraticChar138 (rootProduct138 U (a + y⁻¹)) :=
      (sum_inverse_translate139 (fun x : F => realQuadraticChar138 (rootProduct138 U x)) a).symm
    _ = (∑ y : F, realQuadraticChar138 (reciprocalProduct139 U a y)) - 1 := by
      simp_rw [reciprocal_character_identity139 U a ha heven]
      rw [Finset.sum_sub_distrib, hdelta]
    _ = realQuadraticChar138 (reciprocalScalar139 U a) *
        (∑ y : F, realQuadraticChar138 (rootProduct138 (reciprocalRoots139 U a) y)) - 1 := by
      simp_rw [reciprocalProduct_roots139, realQuadraticChar_mul138]
      rw [← Finset.mul_sum]

/-- Removing the nonzero scalar gives equality of the SHIFTED absolute sums. -/
theorem characterSum_even_centered_abs139 (U : Finset F) (a : F) (ha : a ∈ U)
    (heven : Even U.card) :
    |(∑ x : F, realQuadraticChar138 (rootProduct138 U x)) + 1| =
      |∑ y : F, realQuadraticChar138 (rootProduct138 (reciprocalRoots139 U a) y)| := by
  have h := characterSum_even_reciprocal139 U a ha heven
  have hshift : (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) + 1 =
      realQuadraticChar138 (reciprocalScalar139 U a) *
        (∑ y : F, realQuadraticChar138 (rootProduct138 (reciprocalRoots139 U a) y)) := by
    linarith only [h]
  rw [hshift, abs_mul,
    realQuadraticChar_abs_of_ne_zero138 (reciprocalScalar_ne_zero139 U a), one_mul]

/-- Transfer an arbitrary local bound through inversion. No Weil input occurs. -/
theorem characterSum_even_bound139 (U : Finset F) (a : F) (ha : a ∈ U)
    (heven : Even U.card) (B : ℝ)
    (HB : |∑ y : F, realQuadraticChar138 (rootProduct138 (reciprocalRoots139 U a) y)| ≤ B) :
    |∑ x : F, realQuadraticChar138 (rootProduct138 U x)| ≤ B + 1 := by
  have hshift := characterSum_even_centered_abs139 U a ha heven
  have htri := abs_add_le
    ((∑ x : F, realQuadraticChar138 (rootProduct138 U x)) + 1) (-1 : ℝ)
  have heq : ((∑ x : F, realQuadraticChar138 (rootProduct138 U x)) + 1) + (-1 : ℝ) =
      (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) := by ring
  rw [heq, abs_neg, abs_one, hshift] at htri
  exact le_trans htri (add_le_add HB le_rfl)

/-! ### B. Affine normalization: send any two chosen roots to 0 and 1 -/

noncomputable def affineRoots139 (U : Finset F) (a b : F) : Finset F :=
  U.image (fun u : F => (u - b) / a)

theorem affineRootMap_injOn139 (U : Finset F) (a b : F) (ha : a ≠ 0) :
    Set.InjOn (fun u : F => (u - b) / a) U := by
  intro u hu v hv huv
  exact sub_left_inj.mp ((div_left_inj' ha).mp huv)

theorem affineRoots_card139 (U : Finset F) (a b : F) (ha : a ≠ 0) :
    (affineRoots139 U a b).card = U.card := by
  unfold affineRoots139
  exact Finset.card_image_iff.mpr (affineRootMap_injOn139 U a b ha)

theorem rootProduct_affine139 (U : Finset F) (a b x : F) (ha : a ≠ 0) :
    rootProduct138 U (a * x + b) = a ^ U.card * rootProduct138 (affineRoots139 U a b) x := by
  calc
    rootProduct138 U (a * x + b) = ∏ u ∈ U, a * (x - (u - b) / a) := by
      apply Finset.prod_congr rfl
      intro u hu
      field_simp [ha] <;> ring
    _ = a ^ U.card * (∏ u ∈ U, (x - (u - b) / a)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = a ^ U.card * rootProduct138 (affineRoots139 U a b) x := by
      unfold rootProduct138 affineRoots139
      rw [Finset.prod_image (affineRootMap_injOn139 U a b ha)]

/-- Affine normalization preserves the absolute sum, including odd degree:
the possibly nonsquare scalar is removed only AFTER taking the absolute value. -/
theorem characterSum_affine_abs139 (U : Finset F) (a b : F) (ha : a ≠ 0) :
    |∑ x : F, realQuadraticChar138 (rootProduct138 U x)| =
      |∑ x : F, realQuadraticChar138 (rootProduct138 (affineRoots139 U a b) x)| := by
  have hsum := sum_affine138
    (fun x : F => realQuadraticChar138 (rootProduct138 U x)) a b ha
  rw [← hsum]
  have hpoint : ∀ x : F, rootProduct138 U (a * x + b) =
      a ^ U.card * rootProduct138 (affineRoots139 U a b) x :=
    fun x => rootProduct_affine139 U a b x ha
  simp_rw [hpoint]
  exact characterSum_scalar_abs138 _ (a ^ U.card) (pow_ne_zero _ ha)

theorem affineRoots_zero_mem139 (U : Finset F) (a b : F) (hb : b ∈ U) :
    (0 : F) ∈ affineRoots139 U a b := by
  apply Finset.mem_image.mpr
  refine ⟨b, hb, ?_⟩
  simp only [sub_self, zero_div]

theorem affineRoots_one_mem139 (U : Finset F) (u v : F)
    (hv : v ∈ U) (huv : u ≠ v) :
    (1 : F) ∈ affineRoots139 U (v - u) u := by
  apply Finset.mem_image.mpr
  refine ⟨v, hv, ?_⟩
  exact div_self (sub_ne_zero.mpr (Ne.symm huv))

end FiniteField

/-! ### C. The unproved estimate now needs only odd-cardinality root sets -/

/-- Still an analytic input: the square-root estimate for odd degree >=3.
No estimate is assumed here for any even degree. -/
def OddDegreeDistinctRootWeil139 : Prop :=
  ∀ lam : ℕ, ∀ hp : lam.Prime, lam ≠ 2 →
    letI : Fact lam.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod lam), 3 ≤ U.card → Odd U.card →
      |∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)| ≤
        ((U.card : ℝ) - 1) * Real.sqrt (lam : ℝ)

/-- The linear case is already exact; the retained input is only used for degree>=3. -/
theorem oddDegreeWeil_allOdd139 (HW : OddDegreeDistinctRootWeil139)
    (lam : ℕ) (hp : lam.Prime) (hl2 : lam ≠ 2) :
    letI : Fact lam.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod lam), U.Nonempty → Odd U.card →
      |∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)| ≤
        ((U.card : ℝ) - 1) * Real.sqrt (lam : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  intro U hne hodd
  by_cases h3 : 3 ≤ U.card
  · exact HW lam hp hl2 U h3 hodd
  · have hchar : ringChar (ZMod lam) ≠ 2 := by
      simpa only [ZMod.ringChar_zmod_n] using hl2
    have hR : 1 ≤ Real.sqrt (lam : ℝ) := by
      simpa using Real.sqrt_le_sqrt
        (show (1 : ℝ) ≤ (lam : ℝ) by exact_mod_cast hp.one_le)
    exact rootCharacterSum_lowDegree138 hchar U hne (by omega) _ hR

/-- The stronger even-degree estimate is centered at -1, not zero. -/
theorem evenDegreeWeil_centered139 (HW : OddDegreeDistinctRootWeil139)
    (lam : ℕ) (hp : lam.Prime) (hl2 : lam ≠ 2) :
    letI : Fact lam.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod lam), U.Nonempty → Even U.card →
      |(∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)) + 1| ≤
        ((U.card : ℝ) - 2) * Real.sqrt (lam : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  intro U hne heven
  obtain ⟨a, ha⟩ := hne
  have hpos : 0 < U.card := Finset.card_pos.mpr ⟨a, ha⟩
  have htwo : 2 ≤ U.card := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hc := reciprocalRoots_card139 U a ha
  have hVne : (reciprocalRoots139 U a).Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hVodd : Odd (reciprocalRoots139 U a).card := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k - 1, ?_⟩
    omega
  have hV := oddDegreeWeil_allOdd139 HW lam hp hl2
    (reciprocalRoots139 U a) hVne hVodd
  have hcR : ((reciprocalRoots139 U a).card : ℝ) + 1 = (U.card : ℝ) := by
    exact_mod_cast (show (reciprocalRoots139 U a).card + 1 = U.card by omega)
  rw [characterSum_even_centered_abs139 U a ha heven]
  have hcoef : ((reciprocalRoots139 U a).card : ℝ) - 1 = (U.card : ℝ) - 2 := by
    linarith only [hcR]
  simpa only [hcoef] using hV

/-- Even-degree sums have the improved (d-2)*sqrt(p)+1 bound. -/
theorem evenDegreeWeil_bound139 (HW : OddDegreeDistinctRootWeil139)
    (lam : ℕ) (hp : lam.Prime) (hl2 : lam ≠ 2) :
    letI : Fact lam.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod lam), U.Nonempty → Even U.card →
      |∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)| ≤
        ((U.card : ℝ) - 2) * Real.sqrt (lam : ℝ) + 1 := by
  letI : Fact lam.Prime := ⟨hp⟩
  intro U hne heven
  have h := evenDegreeWeil_centered139 HW lam hp hl2 U hne heven
  have htri := abs_add_le
    ((∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)) + 1) (-1 : ℝ)
  have heq : ((∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)) + 1) + (-1 : ℝ) =
      (∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)) := by ring
  rw [heq, abs_neg, abs_one] at htri
  exact le_trans htri (add_le_add h le_rfl)

/-- All even degrees are supplied internally by inversion. -/
theorem distinctRootWeil_from_oddDegree139 (HW : OddDegreeDistinctRootWeil139) :
    DistinctRootWeil138 := by
  intro lam hp hl2
  letI : Fact lam.Prime := ⟨hp⟩
  intro U hU
  rcases Nat.even_or_odd U.card with heven | hodd
  · have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    have h := evenDegreeWeil_bound139 HW lam hp hl2 U hne heven
    have hR : 1 ≤ Real.sqrt (lam : ℝ) := by
      simpa using Real.sqrt_le_sqrt
        (show (1 : ℝ) ≤ (lam : ℝ) by exact_mod_cast hp.one_le)
    nlinarith only [h, hR]
  · exact HW lam hp hl2 U hU hodd

/-- Unlike a one-way stronger interface, this parity restriction is equivalent. -/
theorem distinctRootWeil_iff_oddDegree139 :
    DistinctRootWeil138 ↔ OddDegreeDistinctRootWeil139 := by
  constructor
  · intro HW lam hp hl2
    letI : Fact lam.Prime := ⟨hp⟩
    intro U hU hodd
    exact HW lam hp hl2 U hU
  · exact distinctRootWeil_from_oddDegree139

/-! ### D. Normalize two roots; no additional analytic hypothesis is added -/

/-- Final retained finite-field input: odd degree >=3 with two roots fixed at
0 and 1. This remains UNPROVED, and is not replaced by an axiom. -/
def NormalizedOddWeil139 : Prop :=
  ∀ lam : ℕ, ∀ hp : lam.Prime, lam ≠ 2 →
    letI : Fact lam.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod lam), 3 ≤ U.card → Odd U.card →
      (0 : ZMod lam) ∈ U → (1 : ZMod lam) ∈ U →
      |∑ z : ZMod lam, realQuadraticChar138 (rootProduct138 U z)| ≤
        ((U.card : ℝ) - 1) * Real.sqrt (lam : ℝ)

/-- The scalar in an affine normalization may be a nonsquare. The absolute-sum
identity handles that sign, and the cardinality remains exactly unchanged. -/
theorem oddDegreeWeil_from_normalized139 (HW : NormalizedOddWeil139) :
    OddDegreeDistinctRootWeil139 := by
  intro lam hp hl2
  letI : Fact lam.Prime := ⟨hp⟩
  intro U hU hodd
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < U.card by omega)
  have hd : (v - u : ZMod lam) ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hc := affineRoots_card139 U (v - u) u hd
  have hcard : 3 ≤ (affineRoots139 U (v - u) u).card := by
    rw [hc]
    exact hU
  have hodd' : Odd (affineRoots139 U (v - u) u).card := by
    rw [hc]
    exact hodd
  have hzero := affineRoots_zero_mem139 U (v - u) u hu
  have hone := affineRoots_one_mem139 U u v hv huv
  have hbound := HW lam hp hl2 (affineRoots139 U (v - u) u) hcard hodd' hzero hone
  rw [hc] at hbound
  rw [characterSum_affine_abs139 U (v - u) u hd]
  exact hbound

/-- Exact logical equivalence between the former distinct-root input and the
normalized odd-degree input, using actual finite-field proof scripts. -/
theorem distinctRootWeil_iff_normalizedOdd139 :
    DistinctRootWeil138 ↔ NormalizedOddWeil139 := by
  constructor
  · intro HW lam hp hl2
    letI : Fact lam.Prime := ⟨hp⟩
    intro U hU hodd hzero hone
    exact HW lam hp hl2 U hU
  · intro HW
    exact distinctRootWeil_from_oddDegree139 (oddDegreeWeil_from_normalized139 HW)

/-- Reconstruct the project's original large-modulus estimate, including common
roots and the scalar removed in Repair 138. -/
theorem largeModulusWeil_from_normalizedOdd139 (HW : NormalizedOddWeil139) :
    LargeModulusLinearProductWeil127 :=
  largeModulusWeil_from_distinctRoots138
    (distinctRootWeil_iff_normalizedOdd139.mpr HW)

structure RemainingNonPNTInputs139 where
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  normalized_odd_weil : NormalizedOddWeil139

theorem RemainingNonPNTInputs139.to138 (H : RemainingNonPNTInputs139) :
    RemainingNonPNTInputs138 where
  sparse_good_prime_count := H.sparse_good_prime_count
  harman_bad_density := H.harman_bad_density
  distinct_root_weil := distinctRootWeil_iff_normalizedOdd139.mpr H.normalized_odd_weil

/-- Explicitly conditional endpoint: quantitative PNT plus the three fields of
H have NOT been constructed by the normalization reductions. -/
theorem candidate_main_from_mediumPNT139 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs139) : MainStatement :=
  candidate_main_from_mediumPNT138 HP H.to138

theorem positive_lower_density_from_mediumPNT139 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs139) : PositiveLowerDensity D6 :=
  positive_lower_density_from_mediumPNT138 HP H.to138

-- Historical audit output (142): #print axioms characterSum_two_roots138
-- Historical audit output (142): #print axioms squareDeletion_sum_identity138
-- Historical audit output (142): #print axioms squareDeletion_sum_bound138
-- Historical audit output (142): #print axioms rootCharacterSum_lowDegree138
-- Historical audit output (142): #print axioms iRoots_card138
-- Historical audit output (142): #print axioms vRoots_card138
-- Historical audit output (142): #print axioms anchorIProduct_roots138
-- Historical audit output (142): #print axioms anchorVProduct_roots138
-- Historical audit output (142): #print axioms firstIRoot_not_vRoots138
-- Historical audit output (142): #print axioms anchorOddRoots_nonempty138
-- Historical audit output (142): #print axioms linearProductWeil_lowDegree138
-- Historical audit output (142): #print axioms sum_inverse_translate139
-- Historical audit output (142): #print axioms realQuadraticChar_even_pow139
-- Historical audit output (142): #print axioms reciprocalRoots_card139
-- Historical audit output (142): #print axioms reciprocalRoots_zero_notMem139
-- Historical audit output (142): #print axioms reciprocalScalar_ne_zero139
-- Historical audit output (142): #print axioms reciprocalProduct_roots139
-- Historical audit output (142): #print axioms rootProduct_reciprocal139
-- Historical audit output (142): #print axioms reciprocal_character_identity139
-- Historical audit output (142): #print axioms characterSum_even_reciprocal139
-- Historical audit output (142): #print axioms characterSum_even_centered_abs139
-- Historical audit output (142): #print axioms characterSum_even_bound139
-- Historical audit output (142): #print axioms affineRoots_card139
-- Historical audit output (142): #print axioms rootProduct_affine139
-- Historical audit output (142): #print axioms characterSum_affine_abs139
-- Historical audit output (142): #print axioms affineRoots_zero_mem139
-- Historical audit output (142): #print axioms affineRoots_one_mem139
-- Historical audit output (142): #print axioms oddDegreeWeil_allOdd139
-- Historical audit output (142): #print axioms evenDegreeWeil_centered139
-- Historical audit output (142): #print axioms evenDegreeWeil_bound139
-- Historical audit output (142): #print axioms distinctRootWeil_from_oddDegree139
-- Historical audit output (142): #print axioms distinctRootWeil_iff_oddDegree139
-- Historical audit output (142): #print axioms oddDegreeWeil_from_normalized139
-- Historical audit output (142): #print axioms distinctRootWeil_iff_normalizedOdd139
-- Historical audit output (142): #print axioms largeModulusWeil_from_normalizedOdd139
-- Historical audit output (142): #print axioms candidate_main_from_mediumPNT139
-- Historical audit output (142): #print axioms positive_lower_density_from_mediumPNT139
-- Historical audit output (142): #check characterSum_even_reciprocal139
-- Historical audit output (142): #check evenDegreeWeil_centered139
-- Historical audit output (142): #check distinctRootWeil_iff_normalizedOdd139
-- Historical audit output (142): #check candidate_main_from_mediumPNT139
-- Historical audit output (142): #print PsiMediumPNT134
-- Historical audit output (142): #print NormalizedOddWeil139
-- Historical audit output (142): #print RemainingNonPNTInputs139
-- Frozen historical output: #eval "REPAIR 139 REPAIRED CHECKPOINT: exact reflection and moment section follows"

end RemainingAnalytic139

/-! ## 140. Exact reflection cancellation and character-transform second moments

The preceding Repair-139 inversion pole is repaired in its original declaration.
This extension adds no analytic assumption. It proves exact cancellation for
reflection-symmetric odd root sets when -1 is a nonsquare, and exact first/second
moments for a variable extra root. It specializes those moments to x(x-1)(x-t).

These are proposed proof scripts, NOT a local Lean compilation. An averaged
second-moment identity is not the missing pointwise Hasse/Weil estimate. The four
analytic inputs to the final endpoint are unchanged.
-/
namespace RemainingAnalytic140

open scoped BigOperators
open RemainingAnalytic61 RemainingAnalytic63 RemainingAnalytic96
open RemainingAnalytic127 RemainingAnalytic134 RemainingAnalytic135
open RemainingAnalytic138 RemainingAnalytic139

set_option maxHeartbeats 4000000

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### A. Reflection gives actual pointwise cancellation, in every odd degree -/

/-- Invariance under x -> b-x; b is twice the center, not the center itself. -/
def RootReflection140 (U : Finset F) (b : F) : Prop :=
  ∀ u : F, u ∈ U ↔ b - u ∈ U

/-- The exact root set in the earlier affine transformation is unchanged. -/
theorem affineRoots_reflection140 (U : Finset F) (b : F)
    (H : RootReflection140 U b) : affineRoots139 U (-1) b = U := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    have heq : (u - b) / (-1 : F) = b - u := by
      field_simp <;> ring
    rw [heq] at huv
    exact huv ▸ (H u).mp hu
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨b - v, (H v).mp hv, ?_⟩
    field_simp <;> ring

/-- Reflection changes a monic degree-d product by the scalar (-1)^d. -/
theorem rootProduct_reflection140 (U : Finset F) (b x : F)
    (H : RootReflection140 U b) :
    rootProduct138 U (b - x) = (-1 : F) ^ U.card * rootProduct138 U x := by
  have h := rootProduct_affine139 U (-1) b x (neg_ne_zero.mpr one_ne_zero)
  have hlin : (-1 : F) * x + b = b - x := by ring
  rw [hlin, affineRoots_reflection140 U b H] at h
  exact h

/-- A field-size congruence supplies the character sign; it is not a Weil input. -/
theorem realQuadraticChar_neg_one_of_card_mod_four140
    (hmod : Fintype.card F % 4 = 3) : realQuadraticChar138 (-1 : F) = -1 := by
  have hns : ¬ IsSquare (-1 : F) := by
    intro hs
    have hnot : Fintype.card F % 4 ≠ 3 := FiniteField.isSquare_neg_one_iff.mp hs
    exact hnot hmod
  have hc : quadraticChar F (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hns
  unfold realQuadraticChar138
  exact_mod_cast hc

/-- Exact zero, not a square-root upper bound, for reflection-symmetric odd roots. -/
theorem characterSum_reflection_zero140 (U : Finset F) (b : F)
    (H : RootReflection140 U b) (hodd : Odd U.card)
    (hminus : realQuadraticChar138 (-1 : F) = -1) :
    (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) = 0 := by
  have hsum := sum_affine138
    (fun x : F => realQuadraticChar138 (rootProduct138 U x))
    (-1) b (neg_ne_zero.mpr one_ne_zero)
  have hpoint : ∀ x : F,
      realQuadraticChar138 (rootProduct138 U ((-1 : F) * x + b)) =
        -realQuadraticChar138 (rootProduct138 U x) := by
    intro x
    have hlin : (-1 : F) * x + b = b - x := by ring
    rw [hlin, rootProduct_reflection140 U b x H, hodd.neg_one_pow,
      realQuadraticChar_mul138, hminus, neg_one_mul]
  have hneg : (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) =
      -(∑ x : F, realQuadraticChar138 (rootProduct138 U x)) := by
    calc
      (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) =
          ∑ x : F, realQuadraticChar138 (rootProduct138 U ((-1 : F) * x + b)) :=
        hsum.symm
      _ = ∑ x : F, -realQuadraticChar138 (rootProduct138 U x) :=
        Finset.sum_congr rfl (fun x hx => hpoint x)
      _ = -(∑ x : F, realQuadraticChar138 (rootProduct138 U x)) :=
        Finset.sum_neg_distrib (fun x : F => realQuadraticChar138 (rootProduct138 U x))
  linarith only [hneg]

/-- A direct sign-reversing involution criterion for an arbitrary polynomial value function. -/
theorem characterSum_oddFunction_zero140 (f : F → F)
    (hf : ∀ x : F, f (-x) = -f x)
    (hminus : realQuadraticChar138 (-1 : F) = -1) :
    (∑ x : F, realQuadraticChar138 (f x)) = 0 := by
  have hsum := sum_affine138 (fun x : F => realQuadraticChar138 (f x))
    (-1) 0 (neg_ne_zero.mpr one_ne_zero)
  have hpoint : ∀ x : F,
      realQuadraticChar138 (f ((-1 : F) * x + 0)) =
        -realQuadraticChar138 (f x) := by
    intro x
    rw [neg_one_mul, add_zero, hf x]
    have hn : -f x = (-1 : F) * f x := by ring
    rw [hn, realQuadraticChar_mul138, hminus, neg_one_mul]
  have heq : (∑ x : F, realQuadraticChar138 (f x)) =
      -(∑ x : F, realQuadraticChar138 (f x)) := by
    calc
      (∑ x : F, realQuadraticChar138 (f x)) =
          ∑ x : F, realQuadraticChar138 (f ((-1 : F) * x + 0)) := hsum.symm
      _ = ∑ x : F, -realQuadraticChar138 (f x) :=
        Finset.sum_congr rfl (fun x hx => hpoint x)
      _ = -(∑ x : F, realQuadraticChar138 (f x)) :=
        Finset.sum_neg_distrib (fun x : F => realQuadraticChar138 (f x))
  linarith only [heq]

/-! ### B. Exact character correlations and an arbitrary-weight second moment -/

/-- Pointwise square of the real-valued character, including its value at zero. -/
theorem realQuadraticChar_sq140 (x : F) :
    (realQuadraticChar138 x) ^ 2 = 1 - (if x = 0 then (1 : ℝ) else 0) := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [if_neg hx, sub_zero]
    have h := realQuadraticChar_square138 hx
    rw [pow_two, realQuadraticChar_mul138] at h
    simpa only [pow_two] using h

/-- There are exactly q-1 nonzero character values. -/
theorem realQuadraticChar_square_sum140 :
    (∑ x : F, (realQuadraticChar138 x) ^ 2) = (Fintype.card F : ℝ) - 1 := by
  simp_rw [realQuadraticChar_sq140]
  rw [Finset.sum_sub_distrib]
  simp

/-- The exact Gram matrix of the translated characters: q-1 on the diagonal,
-1 off it. Both cases are proved, not postulated as an orthogonality package. -/
theorem translatedCharacter_correlation140 (hF : ringChar F ≠ 2) (x y : F) :
    (∑ t : F, realQuadraticChar138 (x - t) * realQuadraticChar138 (y - t)) =
      if x = y then (Fintype.card F : ℝ) - 1 else -1 := by
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    have hsum := sum_affine138 (fun z : F => (realQuadraticChar138 z) ^ 2)
      (-1) x (neg_ne_zero.mpr one_ne_zero)
    calc
      (∑ t : F, realQuadraticChar138 (x - t) * realQuadraticChar138 (x - t)) =
          ∑ t : F, (realQuadraticChar138 ((-1 : F) * t + x)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        have heq : (-1 : F) * t + x = x - t := by ring
        rw [heq, pow_two]
      _ = ∑ z : F, (realQuadraticChar138 z) ^ 2 := hsum
      _ = (Fintype.card F : ℝ) - 1 := realQuadraticChar_square_sum140
  · rw [if_neg hxy]
    calc
      (∑ t : F, realQuadraticChar138 (x - t) * realQuadraticChar138 (y - t)) =
          ∑ t : F, realQuadraticChar138 ((t - x) * (t - y)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [← realQuadraticChar_mul138]
        congr 1
        ring
      _ = -1 := characterSum_two_roots138 hF x y hxy

/-- Convolution with a quadratic character; coefficients are arbitrary real numbers. -/
noncomputable def characterTransform140 (w : F → ℝ) (t : F) : ℝ :=
  ∑ x : F, w x * realQuadraticChar138 (x - t)

/-- The transform has mean zero in odd characteristic. -/
theorem characterTransform_mean140 (hF : ringChar F ≠ 2) (w : F → ℝ) :
    (∑ t : F, characterTransform140 w t) = 0 := by
  unfold characterTransform140
  rw [Finset.sum_comm]
  have hzero : ∀ x : F, (∑ t : F, realQuadraticChar138 (x - t)) = 0 := by
    intro x
    have hsum := sum_affine138 (fun z : F => realQuadraticChar138 z)
      (-1) x (neg_ne_zero.mpr one_ne_zero)
    have heq : (∑ t : F, realQuadraticChar138 (x - t)) =
        ∑ t : F, realQuadraticChar138 ((-1 : F) * t + x) := by
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      ring
    rw [heq, hsum, realQuadraticChar_sum_zero138 hF]
  apply Finset.sum_eq_zero
  intro x hx
  rw [← Finset.mul_sum, hzero x, mul_zero]

/-- Exact second moment: q times coefficient energy minus the squared total mass.
This is an equality, and does not imply a square-root bound at every parameter. -/
theorem characterTransform_secondMoment140 (hF : ringChar F ≠ 2) (w : F → ℝ) :
    (∑ t : F, (characterTransform140 w t) ^ 2) =
      (Fintype.card F : ℝ) * (∑ x : F, (w x) ^ 2) - (∑ x : F, w x) ^ 2 := by
  have hexpand : ∀ t : F, (characterTransform140 w t) ^ 2 =
      ∑ x : F, ∑ y : F, (w x * w y) *
        (realQuadraticChar138 (x - t) * realQuadraticChar138 (y - t)) := by
    intro t
    unfold characterTransform140
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hrow : ∀ x : F,
      (∑ y : F, (w x * w y) *
        (if x = y then (Fintype.card F : ℝ) - 1 else -1)) =
      (Fintype.card F : ℝ) * (w x) ^ 2 - w x * (∑ y : F, w y) := by
    intro x
    have hpoint : ∀ y : F,
        (w x * w y) * (if x = y then (Fintype.card F : ℝ) - 1 else -1) =
        (if y = x then (Fintype.card F : ℝ) * (w x) ^ 2 else 0) - w x * w y := by
      intro y
      by_cases hy : y = x
      · subst y
        simp only [ite_true]
        ring
      · have hxy : x ≠ y := Ne.symm hy
        simp only [if_neg hy, if_neg hxy]
        ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  calc
    (∑ t : F, (characterTransform140 w t) ^ 2) =
        ∑ t : F, ∑ x : F, ∑ y : F, (w x * w y) *
          (realQuadraticChar138 (x - t) * realQuadraticChar138 (y - t)) :=
      Finset.sum_congr rfl (fun t ht => hexpand t)
    _ = ∑ x : F, ∑ t : F, ∑ y : F, (w x * w y) *
          (realQuadraticChar138 (x - t) * realQuadraticChar138 (y - t)) :=
      Finset.sum_comm
    _ = ∑ x : F, ∑ y : F, ∑ t : F, (w x * w y) *
          (realQuadraticChar138 (x - t) * realQuadraticChar138 (y - t)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ x : F, ∑ y : F, (w x * w y) *
          (if x = y then (Fintype.card F : ℝ) - 1 else -1) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.mul_sum, translatedCharacter_correlation140 hF x y]
    _ = ∑ x : F, ((Fintype.card F : ℝ) * (w x) ^ 2 -
          w x * (∑ y : F, w y)) := Finset.sum_congr rfl (fun x hx => hrow x)
    _ = (Fintype.card F : ℝ) * (∑ x : F, (w x) ^ 2) -
          (∑ x : F, w x) ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

/-! ### C. Add one moving root to any distinct-root polynomial -/

/-- The extra root is allowed to coincide with an old root. Those parameters
are included in the complete moments and are not silently dropped. -/
noncomputable def appendedRootSum140 (U : Finset F) (t : F) : ℝ :=
  ∑ x : F, realQuadraticChar138 (rootProduct138 U x * (x - t))

theorem appendedRootSum_eq_transform140 (U : Finset F) (t : F) :
    appendedRootSum140 U t =
      characterTransform140 (fun x : F => realQuadraticChar138 (rootProduct138 U x)) t := by
  unfold appendedRootSum140 characterTransform140
  apply Finset.sum_congr rfl
  intro x hx
  exact realQuadraticChar_mul138 _ _

/-- The zero set of the monic distinct-root product is exactly U. -/
theorem rootCharacter_square_sum140 (U : Finset F) :
    (∑ x : F, (realQuadraticChar138 (rootProduct138 U x)) ^ 2) =
      (Fintype.card F : ℝ) - (U.card : ℝ) := by
  have hpoint : ∀ x : F, (realQuadraticChar138 (rootProduct138 U x)) ^ 2 =
      1 - (if x ∈ U then (1 : ℝ) else 0) := by
    intro x
    rw [realQuadraticChar_sq140]
    by_cases hx : x ∈ U
    · have hz : rootProduct138 U x = 0 := (rootProduct_zero_iff138 U x).mpr hx
      simp only [hz, hx, ite_true]
    · have hz : rootProduct138 U x ≠ 0 :=
        fun hz => hx ((rootProduct_zero_iff138 U x).mp hz)
      simp only [hz, hx, ite_false]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_mem_eq]
  simp

theorem appendedRootSum_mean140 (hF : ringChar F ≠ 2) (U : Finset F) :
    (∑ t : F, appendedRootSum140 U t) = 0 := by
  simp_rw [appendedRootSum_eq_transform140]
  exact characterTransform_mean140 hF _

/-- Exact variable-root second moment for every degree, including all repeated-root parameters. -/
theorem appendedRootSum_secondMoment140 (hF : ringChar F ≠ 2) (U : Finset F) :
    (∑ t : F, (appendedRootSum140 U t) ^ 2) =
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - (U.card : ℝ)) -
        (∑ x : F, realQuadraticChar138 (rootProduct138 U x)) ^ 2 := by
  simp_rw [appendedRootSum_eq_transform140]
  rw [characterTransform_secondMoment140 hF, rootCharacter_square_sum140]

/-! ### D. Exact cubic-family moments and nontrivial pointwise zero cases -/

/-- Actual cubic character sum, with t=0 and t=1 retained until explicitly removed. -/
noncomputable def cubicCharSum140 (t : F) : ℝ :=
  ∑ x : F, realQuadraticChar138 (x * (x - 1) * (x - t))

theorem cubicCharSum_eq_appended140 (t : F) :
    cubicCharSum140 t = appendedRootSum140 ({0, 1} : Finset F) t := by
  simp only [cubicCharSum140, appendedRootSum140, rootProduct138,
    Finset.prod_pair (zero_ne_one : (0 : F) ≠ 1), sub_zero]

/-- Link to the normalized root-set formulation; t must avoid the two fixed roots. -/
theorem cubicCharSum_eq_rootSet140 (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    cubicCharSum140 t =
      ∑ x : F, realQuadraticChar138 (rootProduct138 ({0, 1, t} : Finset F) x) := by
  unfold cubicCharSum140
  apply Finset.sum_congr rfl
  intro x hx
  have hzero : (0 : F) ∉ ({1, t} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨zero_ne_one, Ne.symm ht0⟩
  have hone : (1 : F) ∉ ({t} : Finset F) := by
    simpa only [Finset.mem_singleton] using Ne.symm ht1
  rw [rootProduct138, Finset.prod_insert hzero, Finset.prod_insert hone,
    Finset.prod_singleton, sub_zero]
  congr 1
  ring

theorem cubicCharSum_mean140 (hF : ringChar F ≠ 2) :
    (∑ t : F, cubicCharSum140 t) = 0 := by
  simp_rw [cubicCharSum_eq_appended140]
  exact appendedRootSum_mean140 hF _

/-- The complete cubic-family second moment is q^2-2q-1. -/
theorem cubicCharSum_secondMoment140 (hF : ringChar F ≠ 2) :
    (∑ t : F, (cubicCharSum140 t) ^ 2) =
      (Fintype.card F : ℝ) ^ 2 - 2 * (Fintype.card F : ℝ) - 1 := by
  have hbase : (∑ x : F, realQuadraticChar138 (rootProduct138 ({0, 1} : Finset F) x)) = -1 := by
    simpa only [rootProduct138, Finset.prod_pair (zero_ne_one : (0 : F) ≠ 1), sub_zero]
      using characterSum_x_mul_x_sub_one138 (F := F) hF
  have hc : ({0, 1} : Finset F).card = 2 := by simp
  simp_rw [cubicCharSum_eq_appended140]
  rw [appendedRootSum_secondMoment140 hF, hbase, hc]
  norm_num <;> ring

/-- The first singular parameter has value -chi(-1), not zero. -/
theorem cubicCharSum_zero140 (hF : ringChar F ≠ 2) :
    cubicCharSum140 (0 : F) = -realQuadraticChar138 (-1 : F) := by
  have hpnt : ∀ x : F,
      realQuadraticChar138 (x * (x - 1) * (x - 0)) =
        realQuadraticChar138 (x - 1) -
          (if x = 0 then realQuadraticChar138 (-1 : F) else 0) := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · have heq : x * (x - 1) * (x - 0) = x ^ 2 * (x - 1) := by ring
      rw [heq, realQuadraticChar_mul138, realQuadraticChar_square138 hx,
        one_mul, if_neg hx, sub_zero]
  unfold cubicCharSum140
  simp_rw [hpnt]
  rw [Finset.sum_sub_distrib, characterSum_one_root138 hF (1 : F)]
  simp

/-- The second singular parameter has value -1. -/
theorem cubicCharSum_one140 (hF : ringChar F ≠ 2) :
    cubicCharSum140 (1 : F) = -1 := by
  have hpnt : ∀ x : F,
      realQuadraticChar138 (x * (x - 1) * (x - 1)) =
        realQuadraticChar138 x - (if x = 1 then (1 : ℝ) else 0) := by
    intro x
    by_cases hx : x = 1
    · subst x
      simp
    · have heq : x * (x - 1) * (x - 1) = x * (x - 1) ^ 2 := by ring
      rw [heq, realQuadraticChar_mul138,
        realQuadraticChar_square138 (sub_ne_zero.mpr hx), mul_one, if_neg hx, sub_zero]
  unfold cubicCharSum140
  simp_rw [hpnt]
  rw [Finset.sum_sub_distrib, realQuadraticChar_sum_zero138 hF]
  simp

/-- Exactly the parameters giving three distinct roots; both deleted parameters are explicit. -/
noncomputable def regularCubicParameters140 : Finset F :=
  ((Finset.univ : Finset F).erase 0).erase 1

/-- Removing t=0 and t=1 subtracts two from the complete second moment. -/
theorem cubicCharSum_regular_secondMoment140 (hF : ringChar F ≠ 2) :
    (∑ t ∈ (regularCubicParameters140 : Finset F), (cubicCharSum140 t) ^ 2) =
      (Fintype.card F : ℝ) ^ 2 - 2 * (Fintype.card F : ℝ) - 3 := by
  have hmem1 : (1 : F) ∈ (Finset.univ : Finset F).erase 0 := by simp
  have h0 := Finset.sum_erase_add (Finset.univ : Finset F)
    (fun t : F => (cubicCharSum140 t) ^ 2) (Finset.mem_univ (0 : F))
  have h1 := Finset.sum_erase_add ((Finset.univ : Finset F).erase 0)
    (fun t : F => (cubicCharSum140 t) ^ 2) hmem1
  have hz : (cubicCharSum140 (0 : F)) ^ 2 = 1 := by
    rw [cubicCharSum_zero140 hF, neg_sq, realQuadraticChar_sq140,
      if_neg (neg_ne_zero.mpr one_ne_zero), sub_zero]
  have ho : (cubicCharSum140 (1 : F)) ^ 2 = 1 := by
    rw [cubicCharSum_one140 hF]
    norm_num
  have htotal := cubicCharSum_secondMoment140 (F := F) hF
  unfold regularCubicParameters140
  linarith only [h0, h1, hz, ho, htotal]

/-- This exceptional-parameter estimate follows from the exact moment. It is
NOT the uniform pointwise Weil bound: exceptional parameters are not ruled out. -/
theorem cubicCharSum_exceptional_count140 (hF : ringChar F ≠ 2) (T : ℝ) (hT : 0 < T) :
    let E := (regularCubicParameters140 : Finset F).filter
      (fun t : F => T ^ 2 ≤ (cubicCharSum140 t) ^ 2)
    (E.card : ℝ) ≤
      ((Fintype.card F : ℝ) ^ 2 - 2 * (Fintype.card F : ℝ) - 3) / T ^ 2 := by
  classical
  dsimp only
  let E : Finset F := (regularCubicParameters140 : Finset F).filter
    (fun t : F => T ^ 2 ≤ (cubicCharSum140 t) ^ 2)
  have hsub : E ⊆ (regularCubicParameters140 : Finset F) := Finset.filter_subset _ _
  have hcount : T ^ 2 * (E.card : ℝ) ≤
      (Fintype.card F : ℝ) ^ 2 - 2 * (Fintype.card F : ℝ) - 3 := by
    calc
      T ^ 2 * (E.card : ℝ) = ∑ t ∈ E, T ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ t ∈ E, (cubicCharSum140 t) ^ 2 :=
        Finset.sum_le_sum (fun t ht => (Finset.mem_filter.mp ht).2)
      _ ≤ ∑ t ∈ (regularCubicParameters140 : Finset F), (cubicCharSum140 t) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t ht hnot => sq_nonneg _)
      _ = _ := cubicCharSum_regular_secondMoment140 hF
  apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
  simpa only [mul_comm] using hcount

/-- The t -> 1-t symmetry includes its character sign. -/
theorem cubicCharSum_reflect_parameter140 (t : F) :
    cubicCharSum140 (1 - t) = realQuadraticChar138 (-1 : F) * cubicCharSum140 t := by
  have hsum := sum_affine138
    (fun x : F => realQuadraticChar138 (x * (x - 1) * (x - (1 - t))))
    (-1) 1 (neg_ne_zero.mpr one_ne_zero)
  calc
    cubicCharSum140 (1 - t) = ∑ x : F, realQuadraticChar138
        (((-1 : F) * x + 1) * (((-1 : F) * x + 1) - 1) *
          (((-1 : F) * x + 1) - (1 - t))) := hsum.symm
    _ = ∑ x : F, realQuadraticChar138 (-1 : F) *
        realQuadraticChar138 (x * (x - 1) * (x - t)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have heq : (((-1 : F) * x + 1) * (((-1 : F) * x + 1) - 1) *
          (((-1 : F) * x + 1) - (1 - t))) = (-1 : F) * (x * (x - 1) * (x - t)) := by ring
      rw [heq, realQuadraticChar_mul138]
    _ = realQuadraticChar138 (-1 : F) * cubicCharSum140 t := (Finset.mul_sum _ _ _).symm

/-- The symmetric cubic x(x-1)(x+1) has exactly zero sum when -1 is a nonsquare. -/
theorem cubicCharSum_neg_one_zero140
    (hminus : realQuadraticChar138 (-1 : F) = -1) :
    cubicCharSum140 (-1 : F) = 0 := by
  exact characterSum_oddFunction_zero140
    (fun x : F => x * (x - 1) * (x - (-1))) (fun x => by ring) hminus

/-- A second normalized cubic zero obtained from t -> 1-t. -/
theorem cubicCharSum_two_zero140
    (hminus : realQuadraticChar138 (-1 : F) = -1) :
    cubicCharSum140 (2 : F) = 0 := by
  have h := cubicCharSum_reflect_parameter140 (-1 : F)
  have harg : (1 : F) - (-1) = 2 := by ring
  rw [harg, cubicCharSum_neg_one_zero140 hminus, mul_zero] at h
  exact h

/-- The midpoint case t=1/2, stated without introducing a hidden nonzero denominator. -/
theorem cubicCharSum_midpoint_zero140 (t : F) (ht : 2 * t = 1)
    (hminus : realQuadraticChar138 (-1 : F) = -1) :
    cubicCharSum140 t = 0 := by
  have harg : (1 : F) - t = t := by linear_combination -ht
  have h := cubicCharSum_reflect_parameter140 t
  rw [harg, hminus, neg_one_mul] at h
  linarith only [h]

end FiniteField

/-! ### E. Actual prime-field and two-family specializations -/

theorem prime_character_neg_one140 (lam : ℕ) (hp : lam.Prime) (hmod : lam % 4 = 3) :
    letI : Fact lam.Prime := ⟨hp⟩
    realQuadraticChar138 (-1 : ZMod lam) = -1 := by
  letI : Fact lam.Prime := ⟨hp⟩
  apply realQuadraticChar_neg_one_of_card_mod_four140
  simpa only [ZMod.card] using hmod

/-- No distribution or Weil hypothesis is needed for this infinite family of
prime fields and symmetric odd-degree split polynomials. -/
theorem prime_reflection_sum_zero140 (lam : ℕ) (hp : lam.Prime) (hmod : lam % 4 = 3) :
    letI : Fact lam.Prime := ⟨hp⟩
    ∀ (U : Finset (ZMod lam)) (b : ZMod lam),
      RootReflection140 U b → Odd U.card →
        (∑ x : ZMod lam, realQuadraticChar138 (rootProduct138 U x)) = 0 := by
  letI : Fact lam.Prime := ⟨hp⟩
  intro U b H hodd
  exact characterSum_reflection_zero140 U b H hodd (prime_character_neg_one140 lam hp hmod)

/-- In the original anchor sum, symmetry cancels the odd-root contribution.
The common-root correction is still counted and need not vanish. -/
theorem linearProduct_reflection_bound140 {lam r j t h ell : ℕ} (hp : lam.Prime)
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 0 < ell) (ht : t < h)
    (hsep : 2 * r * max h ell < lam) (hmod : lam % 4 = 3)
    (c b : ZMod lam) (hc : c ≠ 0) :
    letI : Fact lam.Prime := ⟨hp⟩
    Odd (oddRoots138 (iRoots138 lam r ell) (vRoots138 lam j t h)).card →
    RootReflection140 (oddRoots138 (iRoots138 lam r ell) (vRoots138 lam j t h)) b →
      |((linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| ≤
        ((iRoots138 lam r ell ∩ vRoots138 lam j t h).card : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  intro hodd H
  have hgeo := legalPrime_geometry138 hj hjr hh hell ht hsep
  have hr0 := r_nonzero_mod63 hp hj hjr hh hell hsep
  have hj0 := j_nonzero_mod63 hp hj hjr hh hell hsep
  have hz := prime_reflection_sum_zero140 lam hp hmod
    (oddRoots138 (iRoots138 lam r ell) (vRoots138 lam j t h)) b H hodd
  rw [linearProduct_abs_eq_rootPair138 hp hr0 hj0 hgeo.2.2.1 hgeo.2.1 c hc]
  have hcorr := squareDeletion_sum_bound138 (iRoots138 lam r ell) (vRoots138 lam j t h)
  rw [hz, sub_zero] at hcorr
  exact hcorr

/-- Concrete prime-field moments: both singular parameter values have been removed. -/
theorem prime_cubic_regular_secondMoment140 (lam : ℕ) (hp : lam.Prime) (hl2 : lam ≠ 2) :
    letI : Fact lam.Prime := ⟨hp⟩
    (∑ t ∈ (regularCubicParameters140 : Finset (ZMod lam)), (cubicCharSum140 t) ^ 2) =
      (lam : ℝ) ^ 2 - 2 * (lam : ℝ) - 3 := by
  letI : Fact lam.Prime := ⟨hp⟩
  have hchar : ringChar (ZMod lam) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hl2
  simpa only [ZMod.card] using cubicCharSum_regular_secondMoment140 (F := ZMod lam) hchar

/-- The three symmetric normalized cubic parameter values are exact zero cases. -/
theorem prime_cubic_symmetric_zero140 (lam : ℕ) (hp : lam.Prime) (hmod : lam % 4 = 3) :
    letI : Fact lam.Prime := ⟨hp⟩
    cubicCharSum140 (-1 : ZMod lam) = 0 ∧
      cubicCharSum140 (2 : ZMod lam) = 0 ∧
      ∀ t : ZMod lam, 2 * t = 1 → cubicCharSum140 t = 0 := by
  letI : Fact lam.Prime := ⟨hp⟩
  have hm := prime_character_neg_one140 lam hp hmod
  exact ⟨cubicCharSum_neg_one_zero140 hm, cubicCharSum_two_zero140 hm,
    fun t ht => cubicCharSum_midpoint_zero140 t ht hm⟩

/-! ### F. Unchanged analytic obligations and explicit endpoint audit -/

/-- The reflection and moment results do not construct the four analytic inputs. -/
theorem candidate_main_from_mediumPNT140 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs139) : MainStatement :=
  candidate_main_from_mediumPNT139 HP H

theorem positive_lower_density_from_mediumPNT140 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs139) : PositiveLowerDensity D6 :=
  positive_lower_density_from_mediumPNT139 HP H

-- Historical audit output (142): #print axioms reciprocal_character_identity139
-- Historical audit output (142): #print axioms characterSum_even_reciprocal139
-- Historical audit output (142): #print axioms distinctRootWeil_iff_normalizedOdd139
-- Historical audit output (142): #print axioms affineRoots_reflection140
-- Historical audit output (142): #print axioms rootProduct_reflection140
-- Historical audit output (142): #print axioms realQuadraticChar_neg_one_of_card_mod_four140
-- Historical audit output (142): #print axioms characterSum_reflection_zero140
-- Historical audit output (142): #print axioms characterSum_oddFunction_zero140
-- Historical audit output (142): #print axioms realQuadraticChar_sq140
-- Historical audit output (142): #print axioms realQuadraticChar_square_sum140
-- Historical audit output (142): #print axioms translatedCharacter_correlation140
-- Historical audit output (142): #print axioms characterTransform_mean140
-- Historical audit output (142): #print axioms characterTransform_secondMoment140
-- Historical audit output (142): #print axioms rootCharacter_square_sum140
-- Historical audit output (142): #print axioms appendedRootSum_mean140
-- Historical audit output (142): #print axioms appendedRootSum_secondMoment140
-- Historical audit output (142): #print axioms cubicCharSum_eq_rootSet140
-- Historical audit output (142): #print axioms cubicCharSum_mean140
-- Historical audit output (142): #print axioms cubicCharSum_secondMoment140
-- Historical audit output (142): #print axioms cubicCharSum_zero140
-- Historical audit output (142): #print axioms cubicCharSum_one140
-- Historical audit output (142): #print axioms cubicCharSum_regular_secondMoment140
-- Historical audit output (142): #print axioms cubicCharSum_exceptional_count140
-- Historical audit output (142): #print axioms cubicCharSum_reflect_parameter140
-- Historical audit output (142): #print axioms cubicCharSum_neg_one_zero140
-- Historical audit output (142): #print axioms cubicCharSum_two_zero140
-- Historical audit output (142): #print axioms cubicCharSum_midpoint_zero140
-- Historical audit output (142): #print axioms prime_character_neg_one140
-- Historical audit output (142): #print axioms prime_reflection_sum_zero140
-- Historical audit output (142): #print axioms linearProduct_reflection_bound140
-- Historical audit output (142): #print axioms prime_cubic_regular_secondMoment140
-- Historical audit output (142): #print axioms prime_cubic_symmetric_zero140
-- Historical audit output (142): #print axioms candidate_main_from_mediumPNT140
-- Historical audit output (142): #print axioms positive_lower_density_from_mediumPNT140
-- Historical audit output (142): #check characterTransform_secondMoment140
-- Historical audit output (142): #check appendedRootSum_secondMoment140
-- Historical audit output (142): #check linearProduct_reflection_bound140
-- Historical audit output (142): #check prime_cubic_regular_secondMoment140
-- Historical audit output (142): #check candidate_main_from_mediumPNT140
-- Historical audit output (142): #print PsiMediumPNT134
-- Historical audit output (142): #print RemainingNonPNTInputs139
-- Frozen historical output: #eval "REPAIR 140 REPAIRED CHECKPOINT: new four-input section follows"

end RemainingAnalytic140

/-! ## 141. Four-input work: logarithmic sparse range, interval transport,
and geometric finite-field counting

This extension contains proof scripts, NOT a local build certificate. The
three errors in the uploaded Repair-140 log are repaired in their original
bodies above. PNT remains explicit until the separate external integration
module is compiled. No prime-distribution or Weil theorem is inserted as an axiom.
-/
namespace RemainingAnalytic141

open scoped BigOperators
open Filter Asymptotics
open RemainingAnalytic123 RemainingAnalytic127 RemainingAnalytic130
open RemainingAnalytic133 RemainingAnalytic134 RemainingAnalytic135
open RemainingAnalytic138 RemainingAnalytic139 RemainingAnalytic140

set_option maxHeartbeats 4000000

/-! ### A. Quantitative PNT supplies EVERY fixed logarithmic saving -/

def ThetaLogPowerRemainder141 (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |thetaPrefix127 n - (n : ℝ)| * (Real.log (n : ℝ)) ^ k ≤ ε * (n : ℝ)

/-- Exponential decay in a positive power of log absorbs any fixed log power. -/
theorem medium_logPower_eventually_small141
    (k : ℕ) (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) *
        (Real.log x) ^ k < ε := by
  have hroot : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((10 * k : ℕ) : ℝ) c hc).comp hroot
  have hsmall := (tendsto_order.mp hlim).2 ε hε
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hxsmall hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpower : ((Real.log x) ^ ((1 : ℝ) / 10)) ^ ((10 * k : ℕ) : ℝ) =
      (Real.log x) ^ k := by
    rw [← Real.rpow_mul hlog0]
    have hexp : ((1 : ℝ) / 10) * ((10 * k : ℕ) : ℝ) = (k : ℝ) := by
      push_cast
      ring
    rw [hexp, Real.rpow_natCast]
  change ((Real.log x) ^ ((1 : ℝ) / 10)) ^ ((10 * k : ℕ) : ℝ) *
    Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < ε at hxsmall
  rw [hpower] at hxsmall
  simpa only [mul_comm] using hxsmall

/-- The elementary prime-power error also absorbs every fixed logarithmic weight. -/
theorem primePower_logPower_eventually_small141
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (2 * Real.sqrt x * Real.log x) * (Real.log x) ^ k ≤ ε * x := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop ((k + 1 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).bound
      (show 0 < ε / 2 by linarith)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hxsmall hx1
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogNorm : ‖(Real.log x) ^ ((k + 1 : ℕ) : ℝ)‖ = (Real.log x) ^ (k + 1) := by
    rw [Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 (k + 1))]
  have hsqrtNorm : ‖x ^ ((1 : ℝ) / 2)‖ = Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)]
  change ‖(Real.log x) ^ ((k + 1 : ℕ) : ℝ)‖ ≤
    (ε / 2) * ‖x ^ ((1 : ℝ) / 2)‖ at hxsmall
  rw [hlogNorm, hsqrtNorm] at hxsmall
  calc
    (2 * Real.sqrt x * Real.log x) * (Real.log x) ^ k =
        (2 * Real.sqrt x) * (Real.log x) ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ (2 * Real.sqrt x) * ((ε / 2) * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hxsmall (by positivity)
    _ = ε * (Real.sqrt x) ^ 2 := by ring
    _ = ε * x := by rw [Real.sq_sqrt hx0]

/-- Generalized PNT adapter. This constructs all fixed log-power remainders;
the PNT argument itself is still required. -/
theorem thetaLogPower_from_mediumPNT141 (HP : PsiMediumPNT134) (k : ℕ) :
    ThetaLogPowerRemainder141 k := by
  obtain ⟨c, hc, hPNT⟩ := HP
  obtain ⟨C, hC, hbound⟩ := Asymptotics.isBigO_iff'.mp hPNT
  intro ε hε
  have hw := medium_logPower_eventually_small141 k c hc
    (ε / (2 * C)) (by positivity)
  have hg := primePower_logPower_eventually_small141 k (ε / 2) (by linarith)
  have hreal : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| * (Real.log x) ^ k ≤ ε * x := by
    filter_upwards [hbound, hw, hg, eventually_ge_atTop (1 : ℝ)]
      with x hxPNT hxw hxg hx1
    have hx0 : 0 ≤ x := by linarith
    have hL0 : 0 ≤ (Real.log x) ^ k := pow_nonneg (Real.log_nonneg hx1) k
    have hright0 : 0 ≤ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by positivity
    have herr : |Chebyshev.psi x - x| ≤
        C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hright0] using hxPNT
    have hcancel : C * (ε / (2 * C)) = ε / 2 := by
      field_simp [ne_of_gt hC] <;> ring
    have hCw := mul_le_mul_of_nonneg_left hxw.le hC.le
    rw [hcancel] at hCw
    have hmain : |Chebyshev.psi x - x| * (Real.log x) ^ k ≤ (ε / 2) * x := by
      calc
        _ ≤ (C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))) *
              (Real.log x) ^ k := mul_le_mul_of_nonneg_right herr hL0
        _ = x * (C * (Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) *
              (Real.log x) ^ k)) := by ring
        _ ≤ x * (ε / 2) := mul_le_mul_of_nonneg_left hCw hx0
        _ = (ε / 2) * x := by ring
    have hgap : |Chebyshev.psi x - Chebyshev.theta x| * (Real.log x) ^ k ≤ (ε / 2) * x :=
      le_trans (mul_le_mul_of_nonneg_right
        (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1) hL0) hxg
    have htri : |Chebyshev.theta x - x| ≤
        |Chebyshev.psi x - Chebyshev.theta x| + |Chebyshev.psi x - x| := by
      simpa only [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] using
        abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
    have hmul := mul_le_mul_of_nonneg_right htri hL0
    nlinarith only [hmain, hgap, hmul]
  have hnat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually hreal
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnat
  refine ⟨N, ?_⟩
  intro n hn
  rw [thetaPrefix_eq_mathlib134]
  exact hN n hn

/-- Fixed log powers grow more slowly than sqrt X. -/
theorem logPower_le_sqrt_eventually141 (k : ℕ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (Real.log (X : ℝ)) ^ k ≤ Real.sqrt (X : ℝ) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k : ℝ)
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).bound (by norm_num : (0 : ℝ) < 1)
  have he : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ k ≤ Real.sqrt x := by
    filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
    simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hL k), abs_of_nonneg (Real.sqrt_nonneg x), one_mul] using hx
  exact eventually_atTop.mp ((tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually he)

/-- Endpoint logarithms remain comparable on [sqrt X,X]. -/
theorem log_endpoint_lower141 {X n : ℕ} (hX : 1 ≤ X)
    (hn : Real.sqrt (X : ℝ) ≤ (n : ℝ)) :
    Real.log (X : ℝ) / 2 ≤ Real.log (n : ℝ) := by
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hsp : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXp
  have hh := Real.log_le_log hsp hn
  have hid : Real.log (Real.sqrt (X : ℝ)) = Real.log (X : ℝ) / 2 := by
    rw [Real.log_sqrt (le_of_lt hXp)]
  simpa only [hid] using hh

/-- Error-budget arithmetic for endpoints at least sqrt X. -/
theorem logPower_endpoint_error141 {E l L n h : ℝ} (k : ℕ)
    (hE : 0 ≤ E) (hL : 0 < L) (hl : L / 2 ≤ l)
    (hn : n ≤ h * L ^ k)
    (herr : E * l ^ k ≤ (1 / (8 * (2 : ℝ) ^ k)) * n) : E ≤ h / 8 := by
  have hl0 : 0 ≤ l := by linarith
  have hpow : (L / 2) ^ k ≤ l ^ k := pow_le_pow_left₀ (by positivity) hl k
  have hmul := mul_le_mul_of_nonneg_left hpow hE
  have hscale := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ 1 / (8 * (2 : ℝ) ^ k) by positivity)
  have hden : 0 < (2 : ℝ) ^ k := by positivity
  have hLpow : 0 < L ^ k := pow_pos hL k
  have hid : (L / 2) ^ k = L ^ k / (2 : ℝ) ^ k := div_pow L 2 k
  rw [hid] at hmul
  have hcomb : E * (L ^ k / (2 : ℝ) ^ k) ≤
      (1 / (8 * (2 : ℝ) ^ k)) * (h * L ^ k) := le_trans (le_trans hmul herr) hscale
  have hclear := mul_le_mul_of_nonneg_right hcomb (le_of_lt hden)
  have hleft : (E * (L ^ k / (2 : ℝ) ^ k)) * (2 : ℝ) ^ k = E * L ^ k := by
    field_simp [ne_of_gt hden] <;> ring
  have hright : ((1 / (8 * (2 : ℝ) ^ k)) * (h * L ^ k)) * (2 : ℝ) ^ k =
      (h / 8) * L ^ k := by field_simp [ne_of_gt hden] <;> ring
  rw [hleft, hright] at hclear
  exact le_of_mul_le_mul_right hclear hLpow

/-! ### B. A proved logarithmically wide subrange of the SPARSE prime input -/

/-- All primes in (b,c] are eligible sparse primes when c<=2b and a<b. -/
theorem intervalPrimes_subset_sparse141 {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hhalf : c ≤ 2 * b) :
    (Finset.Icc 1 c).filter (fun p => p.Prime ∧ b < p) ⊆ sparseGoodPrimes127 a b c b := by
  intro p hp
  obtain ⟨hpc, hprime, hbp⟩ := Finset.mem_filter.mp hp
  have hcp : p ≤ c := (Finset.mem_Icc.mp hpc).2
  have htop : max b (c / 2) < p := by omega
  have hd := top_interval_prime_data hab hbc hprime ⟨htop, hcp⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hbp.le, le_trans hcp hhalf⟩, hprime, hd⟩

/-- A lower theta mass gives the actual sparse count, with the SAME 640 constant. -/
theorem sparseCount_from_intervalTheta141 {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hb2 : 2 ≤ b) (hhalf : c ≤ 2 * b)
    (hmass : ((c - b : ℕ) : ℝ) / 2 ≤ thetaPrefix127 c - thetaPrefix127 b) :
    ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * b : ℝ)) ≤
      ((sparseGoodPrimes127 a b c b).card : ℝ) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 c).filter (fun p => p.Prime ∧ b < p)
  have hsplit := thetaPrefix_split127 hbc.le
  have hlogs : (∑ p ∈ S, Real.log (p : ℝ)) ≤
      (S.card : ℝ) * Real.log (2 * b : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ S, Real.log (2 * b : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hd := Finset.mem_filter.mp hp
        have hpp : p.Prime := hd.2.1
        have hpmax : (p : ℝ) ≤ (2 * b : ℝ) := by
          exact_mod_cast le_trans (Finset.mem_Icc.mp hd.1).2 hhalf
        exact Real.log_le_log (by exact_mod_cast hpp.pos) hpmax
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≤ ((sparseGoodPrimes127 a b c b).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (intervalPrimes_subset_sparse141 hab hbc hhalf)
  have hlogpos : 0 < Real.log (2 * b : ℝ) := Real.log_pos (by exact_mod_cast
    (show 1 < 2 * b by omega))
  have hscaled := mul_le_mul_of_nonneg_right hcard hlogpos.le
  have hh0 : (0 : ℝ) ≤ ((c - b : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 640) hlogpos)).mpr
  have hsum : thetaPrefix127 c - thetaPrefix127 b = ∑ p ∈ S, Real.log (p : ℝ) := by
    dsimp [S]
    linarith only [hsplit]
  rw [hsum] at hmass
  nlinarith only [hmass, hlogs, hscaled, hh0]

/-- From PNT, every fixed logarithmic-width sparse band is supplied internally.
No sparse prime-count hypothesis occurs in this theorem. -/
theorem sparse_logWide_from_PNT141 (HP : PsiMediumPNT134) (k : ℕ) :
    ∃ N : ℕ, ∀ X a b c : ℕ,
      N ≤ X → a < b → b < c → c ≤ X → c ≤ 2 * b →
      (X : ℝ) ≤ ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ k →
      ∃ P : ℕ, 2 ≤ P ∧
        ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
          ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  obtain ⟨NT, hNT⟩ := thetaLogPower_from_mediumPNT141 HP k
    (1 / (8 * (2 : ℝ) ^ k)) (by positivity)
  obtain ⟨NP, hNP⟩ := logPower_le_sqrt_eventually141 k
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 1
  refine ⟨max (max NP NL) ((max NT 2) ^ 2 + 1), ?_⟩
  intro X a b c hX hab hbc hcX hhalf hwide
  have hXP : NP ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXL : NL ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXbig : (max NT 2) ^ 2 + 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by omega
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hspos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXp
  have hsquare : (Real.sqrt (X : ℝ)) ^ 2 = (X : ℝ) := Real.sq_sqrt hXp.le
  have hNlarge : ((max NT 2 : ℕ) : ℝ) < Real.sqrt (X : ℝ) := by
    have hNX : ((max NT 2 : ℕ) : ℝ) ^ 2 < (X : ℝ) := by
      exact_mod_cast (show (max NT 2) ^ 2 < X by omega)
    have hN0 : (0 : ℝ) ≤ ((max NT 2 : ℕ) : ℝ) := by positivity
    nlinarith
  have hh0 : (0 : ℝ) ≤ ((c - b : ℕ) : ℝ) := by positivity
  have hL1 : 1 ≤ Real.log (X : ℝ) := hNL X hXL
  have hLpos : 0 < Real.log (X : ℝ) := by linarith
  have hwide' := mul_le_mul_of_nonneg_left (hNP X hXP) hh0
  have hgaplarge : Real.sqrt (X : ℝ) ≤ ((c - b : ℕ) : ℝ) := by
    have htotal := le_trans hwide hwide'
    have hprod : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) ≤
        ((c - b : ℕ) : ℝ) * Real.sqrt (X : ℝ) := by
      nlinarith only [htotal, hsquare]
    exact le_of_mul_le_mul_right hprod hspos
  have hgapb : c - b ≤ b := by omega
  have hbs : Real.sqrt (X : ℝ) ≤ (b : ℝ) :=
    le_trans hgaplarge (by exact_mod_cast hgapb)
  have hcs : Real.sqrt (X : ℝ) ≤ (c : ℝ) :=
    le_trans hbs (by exact_mod_cast hbc.le)
  have hbN : NT ≤ b := by
    have hh : (NT : ℝ) < (b : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast le_max_left NT 2) (lt_of_lt_of_le hNlarge hbs)
    exact_mod_cast hh.le
  have hcN : NT ≤ c := le_trans hbN hbc.le
  have hb2 : 2 ≤ b := by
    have hh : (2 : ℝ) < (b : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast le_max_right NT 2) (lt_of_lt_of_le hNlarge hbs)
    exact_mod_cast hh.le
  have hbX : b ≤ X := le_trans hbc.le hcX
  have hbscale : (b : ℝ) ≤ ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ k :=
    le_trans (by exact_mod_cast hbX) hwide
  have hcscale : (c : ℝ) ≤ ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ k :=
    le_trans (by exact_mod_cast hcX) hwide
  have hbErr := logPower_endpoint_error141 k (abs_nonneg _) hLpos
    (log_endpoint_lower141 hX1 hbs) hbscale (hNT b hbN)
  have hcErr := logPower_endpoint_error141 k (abs_nonneg _) hLpos
    (log_endpoint_lower141 hX1 hcs) hcscale (hNT c hcN)
  have hsub : ((c - b : ℕ) : ℝ) = (c : ℝ) - (b : ℝ) := Nat.cast_sub hbc.le
  have hmass : ((c - b : ℕ) : ℝ) / 2 ≤ thetaPrefix127 c - thetaPrefix127 b := by
    have hbupper := le_abs_self (thetaPrefix127 b - (b : ℝ))
    have hclower := neg_abs_le (thetaPrefix127 c - (c : ℝ))
    nlinarith only [hbErr, hcErr, hbupper, hclower, hsub, hh0]
  exact ⟨b, hb2, sparseCount_from_intervalTheta141 hab hbc hb2 hhalf hmass⟩

/-- Only the shorter-than-logarithmic regime is retained as a sparse input.
For k=4 the complementary region is nonempty inside the original sparse branch. -/
def SparseSublogCount141 (k : ℕ) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ X₀ : ℕ, ∀ X a b c : ℕ,
    X₀ ≤ X → a < b → b < c → c ≤ X →
    (X : ℝ) ^ γ ≤ ((c - b : ℕ) : ℝ) →
    (a : ℝ) ≤ 10 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) →
    100 * ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ 2 < (b : ℝ) →
    ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ k < (X : ℝ) →
    ∃ P : ℕ, 2 ≤ P ∧
      ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
        ((sparseGoodPrimes127 a b c P).card : ℝ)

theorem sparseGoodPrimeCount_from_sublog141 (HP : PsiMediumPNT134)
    (k : ℕ) (HS : SparseSublogCount141 k) : SparseGoodPrimeCount127 := by
  intro γ hγ0 hγ1
  obtain ⟨NS, hNS⟩ := HS γ hγ0 hγ1
  obtain ⟨NW, hNW⟩ := sparse_logWide_from_PNT141 HP k
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 1
  refine ⟨max NS (max NW NL), ?_⟩
  intro X a b c hX hab hbc hcX hgap ha hb
  have hXS : NS ≤ X := le_trans (le_max_left _ _) hX
  have hXW : NW ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXL : NL ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  by_cases hshort : ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ k < (X : ℝ)
  · exact hNS X a b c hXS hab hbc hcX hgap ha hb hshort
  · have hL := hNL X hXL
    have hLsq : 1 ≤ (Real.log (X : ℝ)) ^ 2 := by nlinarith only [hL]
    have hh0 : (0 : ℝ) ≤ ((c - b : ℕ) : ℝ) := by positivity
    have hprod := mul_le_mul_of_nonneg_left hLsq hh0
    have hgapb : ((c - b : ℕ) : ℝ) ≤ (b : ℝ) := by nlinarith only [hb, hprod, hh0]
    have hgapbNat : c - b ≤ b := by exact_mod_cast hgapb
    exact hNW X a b c hXW hab hbc hcX (by omega) (le_of_not_gt hshort)

/-- Under the already-required PNT, this restriction is logically lossless. -/
theorem sparseGoodPrimeCount_iff_sublog141 (HP : PsiMediumPNT134) (k : ℕ) :
    SparseGoodPrimeCount127 ↔ SparseSublogCount141 k := by
  constructor
  · intro HS γ hγ0 hγ1
    obtain ⟨N, hN⟩ := HS γ hγ0 hγ1
    refine ⟨N, ?_⟩
    intro X a b c hX hab hbc hcX hgap ha hb hshort
    exact hN X a b c hX hab hbc hcX hgap ha hb
  · exact sparseGoodPrimeCount_from_sublog141 HP k


/-! ### C. Harman: rigorously transport forward existence to backward endpoints

Only existence of a prime is used. A mean-square asymptotic for the number of
primes is NOT assumed. We use forward exponent 21/200, strictly between 1/10
and theta=11/100. The discarded initial block is X^(99/100).
-/

def harmanForwardExponent141 : ℝ := 21 / 200
def harmanCutoffExponent141 : ℝ := 99 / 100

def forwardBadIntervals141 : Set ℕ :=
  {n | ¬ ∃ p : ℕ, p.Prime ∧ n ≤ p ∧
    ((p - n : ℕ) : ℝ) ≤ (n : ℝ) ^ harmanForwardExponent141}

noncomputable def harmanShift141 (X : ℕ) : ℕ :=
  ⌈(X : ℝ) ^ harmanForwardExponent141⌉₊

noncomputable def harmanInitialCutoff141 (X : ℕ) : ℕ :=
  ⌈(X : ℝ) ^ harmanCutoffExponent141⌉₊

/-- Numerical margins used in the forward/backward conversion. -/
theorem harmanTransport_ledger141 :
    0 < harmanForwardExponent141 ∧
    (1 : ℝ) / 10 < harmanForwardExponent141 ∧
    harmanForwardExponent141 < harmanCutoffExponent141 * theta ∧
    harmanCutoffExponent141 * theta ≤ harmanCutoffExponent141 ∧
    harmanCutoffExponent141 < 1 := by
  norm_num [harmanForwardExponent141, harmanCutoffExponent141, theta]

/-- The shift is eventually at most both the discarded cutoff and m^theta
on the retained endpoints. Ceil rounding is included. -/
theorem harmanShift_scale141 :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      harmanShift141 X ≤ harmanInitialCutoff141 X ∧
      ∀ m : ℕ, harmanInitialCutoff141 X < m →
        (harmanShift141 X : ℝ) ≤ (m : ℝ) ^ theta := by
  have hσ : 0 < harmanForwardExponent141 := harmanTransport_ledger141.1
  have hgap : 0 < harmanCutoffExponent141 * theta - harmanForwardExponent141 := by
    norm_num [harmanForwardExponent141, harmanCutoffExponent141, theta]
  obtain ⟨N, hN⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := harmanCutoffExponent141 * theta - harmanForwardExponent141)
    (C := 2) hgap
  refine ⟨max N 1, ?_⟩
  intro X hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1R : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hpow1 : 1 ≤ (X : ℝ) ^ harmanForwardExponent141 := Real.one_le_rpow hX1R hσ.le
  have hpowpos : 0 < (X : ℝ) ^ harmanForwardExponent141 := Real.rpow_pos_of_pos hXp _
  have hceil : (harmanShift141 X : ℝ) < (X : ℝ) ^ harmanForwardExponent141 + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hXp.le _)
  have hprod := mul_lt_mul_of_pos_right (hN X hXN) hpowpos
  have hid : (X : ℝ) ^ (harmanCutoffExponent141 * theta - harmanForwardExponent141) *
      (X : ℝ) ^ harmanForwardExponent141 = (X : ℝ) ^ (harmanCutoffExponent141 * theta) := by
    rw [← Real.rpow_add hXp, sub_add_cancel]
  rw [hid] at hprod
  have hshift : (harmanShift141 X : ℝ) ≤ (X : ℝ) ^ (harmanCutoffExponent141 * theta) := by
    nlinarith only [hceil, hpow1, hprod]
  have hpower_le : (X : ℝ) ^ (harmanCutoffExponent141 * theta) ≤
      (X : ℝ) ^ harmanCutoffExponent141 :=
    Real.rpow_le_rpow_of_exponent_le hX1R
      (by norm_num [harmanCutoffExponent141, theta])
  have hK : (X : ℝ) ^ harmanCutoffExponent141 ≤ (harmanInitialCutoff141 X : ℝ) :=
    Nat.le_ceil _
  constructor
  · exact_mod_cast le_trans hshift (le_trans hpower_le hK)
  · intro m hm
    have hXm : (X : ℝ) ^ harmanCutoffExponent141 ≤ (m : ℝ) :=
      le_trans hK (by exact_mod_cast hm.le)
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hXm
      (by norm_num [theta] : 0 ≤ theta)
    have hpowmul : ((X : ℝ) ^ harmanCutoffExponent141) ^ theta =
        (X : ℝ) ^ (harmanCutoffExponent141 * theta) :=
      (Real.rpow_mul hXp.le _ _).symm
    rw [hpowmul] at hmono
    exact le_trans hshift hmono

/-- A bad backward endpoint beyond the cutoff produces a bad FORWARD starting
point after a fixed translation depending on X, not depending on that endpoint. -/
theorem backwardBad_translates_to_forward141 {X m : ℕ}
    (hshiftK : harmanShift141 X ≤ harmanInitialCutoff141 X)
    (hscale : (harmanShift141 X : ℝ) ≤ (m : ℝ) ^ theta)
    (hmK : harmanInitialCutoff141 X < m) (hmX : m ≤ X)
    (hbad : m ∈ badShortIntervals127) :
    m - harmanShift141 X ∈ forwardBadIntervals141 := by
  have hHm : harmanShift141 X < m := lt_of_le_of_lt hshiftK hmK
  intro hgood
  obtain ⟨p, hp, hnp, hgap⟩ := hgood
  have hnX : m - harmanShift141 X ≤ X := le_trans (Nat.sub_le m _) hmX
  have hσ : 0 ≤ harmanForwardExponent141 := by norm_num [harmanForwardExponent141]
  have hnXR : (((m - harmanShift141 X : ℕ) : ℝ)) ≤ (X : ℝ) := by
    exact_mod_cast hnX
  have hpow : (((m - harmanShift141 X : ℕ) : ℝ)) ^ harmanForwardExponent141 ≤
      (X : ℝ) ^ harmanForwardExponent141 :=
    Real.rpow_le_rpow (by positivity) hnXR hσ
  have hceil : (X : ℝ) ^ harmanForwardExponent141 ≤ (harmanShift141 X : ℝ) := Nat.le_ceil _
  have hpnH : p - (m - harmanShift141 X) ≤ harmanShift141 X := by
    exact_mod_cast le_trans hgap (le_trans hpow hceil)
  have hpm : p ≤ m := by omega
  have hmp : m - p ≤ harmanShift141 X := by omega
  have hgoodback : (shortIntervalPrimes127 m).Nonempty :=
    (shortInterval_nonempty_iff127 m).mpr
      ⟨p, hp, hpm, le_trans (by exact_mod_cast hmp) hscale⟩
  have hempty : shortIntervalPrimes127 m = ∅ := hbad
  rw [hempty] at hgoodback
  obtain ⟨p, hpEmpty⟩ := hgoodback
  exact Finset.notMem_empty p hpEmpty

/-- Finite counting transport. No countable density-subadditivity assertion is used. -/
theorem backwardBad_prefix_bound141 :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      prefixCount badShortIntervals127 X ≤
        harmanInitialCutoff141 X + prefixCount forwardBadIntervals141 X := by
  classical
  obtain ⟨N, hN⟩ := harmanShift_scale141
  refine ⟨N, ?_⟩
  intro X hX
  obtain ⟨hHK, hscale⟩ := hN X hX
  let D : Finset ℕ := (Finset.Icc 1 X).filter (fun m => m ∈ badShortIntervals127)
  let F : Finset ℕ := (Finset.Icc 1 X).filter (fun n => n ∈ forwardBadIntervals141)
  let I : Finset ℕ := Finset.Icc 1 (harmanInitialCutoff141 X)
  have hcover : D ⊆ I ∪ F.image (fun n : ℕ => n + harmanShift141 X) := by
    intro m hm
    obtain ⟨hmI, hbad⟩ := Finset.mem_filter.mp hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
    have hmX : m ≤ X := (Finset.mem_Icc.mp hmI).2
    by_cases hmK : m ≤ harmanInitialCutoff141 X
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hm1, hmK⟩))
    · have hmK' : harmanInitialCutoff141 X < m := lt_of_not_ge hmK
      have hHm : harmanShift141 X < m := lt_of_le_of_lt hHK hmK'
      have hf : m - harmanShift141 X ∈ F := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans (Nat.sub_le m _) hmX⟩,
          backwardBad_translates_to_forward141 hHK (hscale m hmK') hmK' hmX hbad⟩
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨m - harmanShift141 X, hf, by omega⟩))
  have hIcard : I.card = harmanInitialCutoff141 X := by
    dsimp [I]
    simp
  have hcount : D.card ≤ I.card + F.card :=
    le_trans (Finset.card_le_card hcover)
      (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_left (Finset.card_image_le) _))
  change D.card ≤ harmanInitialCutoff141 X + F.card
  simpa only [hIcard] using hcount

/-- Generic complementary-power estimate; the exponent need only be below one. -/
theorem rpow_ratio_eventually_small141 (β : ℝ) (hβ : β < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → (X : ℝ) ^ β / (X : ℝ) < ε := by
  obtain ⟨N, hN⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := 1 - β) (C := 1 / ε) (by linarith)
  refine ⟨max 1 N, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXN : N ≤ X := le_trans (le_max_right _ _) hX
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hpowp : 0 < (X : ℝ) ^ (1 - β) := Real.rpow_pos_of_pos hXp _
  have hid : (X : ℝ) ^ β * (X : ℝ) ^ (1 - β) = (X : ℝ) := by
    rw [← Real.rpow_add hXp]
    have he : β + (1 - β) = 1 := by ring
    rw [he, Real.rpow_one]
  have hratio : (X : ℝ) ^ β / (X : ℝ) = 1 / (X : ℝ) ^ (1 - β) := by
    field_simp [ne_of_gt hXp, ne_of_gt hpowp]
    nlinarith only [hid]
  rw [hratio]
  have hh := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 1 / ε) (hN X hXN)
  simpa only [one_div_one_div] using hh

/-- The ceiling correction in the discarded block has density zero too. -/
theorem harmanInitialCutoff_ratio_small141 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → (harmanInitialCutoff141 X : ℝ) / (X : ℝ) < ε := by
  have hβ : harmanCutoffExponent141 < 1 := by norm_num [harmanCutoffExponent141]
  obtain ⟨N1, hN1⟩ := rpow_ratio_eventually_small141 harmanCutoffExponent141 hβ
    (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 / ε)
  refine ⟨max N1 (max N2 1), ?_⟩
  intro X hX
  have hX1 : N1 ≤ X := le_trans (le_max_left _ _) hX
  have hX2 : N2 ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXpNat : 1 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXlarge : 2 / ε < (X : ℝ) := lt_of_lt_of_le hN2 (by exact_mod_cast hX2)
  have hinv : 1 / (X : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hXp).mpr
    have hh := (div_lt_iff₀ hε).mp hXlarge
    nlinarith only [hh]
  have hceil : (harmanInitialCutoff141 X : ℝ) <
      (X : ℝ) ^ harmanCutoffExponent141 + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hXp.le _)
  have hdivide := (div_lt_div_iff_of_pos_right hXp).mpr hceil
  rw [add_div] at hdivide
  linarith only [hdivide, hN1 X hX1, hinv]

/-- The published-style forward existence statement, at exponent .105,
is sufficient for the actual backward statement at theta=.11. -/
theorem harman_bad_density_from_forward141
    (HF : DensityZero forwardBadIntervals141) : DensityZero badShortIntervals127 := by
  intro ε hε
  obtain ⟨NF, hNF⟩ := HF (ε / 2) (by linarith)
  obtain ⟨NK, hNK⟩ := harmanInitialCutoff_ratio_small141 (ε / 2) (by linarith)
  obtain ⟨NT, hNT⟩ := backwardBad_prefix_bound141
  refine ⟨max (max NF NK) (max NT 1), ?_⟩
  intro X hX
  have hXF : NF ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXK : NK ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXT : NT ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hforward := hNF X hXF
  rw [sub_zero, abs_of_nonneg (proportion_nonneg _ _)] at hforward
  have hcount : (prefixCount badShortIntervals127 X : ℝ) ≤
      (harmanInitialCutoff141 X : ℝ) + (prefixCount forwardBadIntervals141 X : ℝ) := by
    exact_mod_cast hNT X hXT
  have hprop := div_le_div_of_nonneg_right hcount hXp.le
  rw [add_div] at hprop
  rw [sub_zero, abs_of_nonneg (proportion_nonneg _ _)]
  change (prefixCount badShortIntervals127 X : ℝ) / (X : ℝ) < ε
  change (prefixCount forwardBadIntervals141 X : ℝ) / (X : ℝ) < ε / 2 at hforward
  linarith only [hprop, hforward, hNK X hXK]


/-! ### D. Sparse high bands: exact reciprocal-floor statistic, no square-loss input

For p>c-b and p^2>c, a multiple of p in (b,c] is unique and has valuation one.
Consequently an entire high dyadic band has ZERO square-divisor loss. The count
is then an exact sum of floor differences. This does not assert distribution
of primes in those reciprocal intervals.
-/

/-- Two multiples of p in an interval shorter than p must coincide. -/
theorem shortInterval_multiple_unique141 {b c p u v : ℕ}
    (hgap : c - b < p) (hbu : b < u) (huc : u ≤ c)
    (hbv : b < v) (hvc : v ≤ c) (hu : p ∣ u) (hv : p ∣ v) : u = v := by
  rcases lt_trichotomy u v with huv | huv | hvu
  · have hdiv : p ∣ v - u := Nat.dvd_sub hv hu
    have hp : p ≤ v - u := Nat.le_of_dvd (by omega) hdiv
    omega
  · exact huv
  · have hdiv : p ∣ u - v := Nat.dvd_sub hu hv
    have hp : p ≤ u - v := Nat.le_of_dvd (by omega) hdiv
    omega

/-- An interior multiple below p^2 contributes valuation exactly one. -/
theorem falling_factorization_one_of_highBand141 {b c p m : ℕ}
    (hbc : b < c) (hp : p.Prime) (hgap : c - b < p) (hsquare : c < p ^ 2)
    (hbm : b < m) (hmc : m ≤ c) (hpm : p ∣ m) :
    (falling (c - b) c).factorization p = 1 := by
  have hm0 : m ≠ 0 := by omega
  have hnotSq : ¬ p ^ 2 ∣ m := by
    intro hh
    have hle := Nat.le_of_dvd (show 0 < m by omega) hh
    omega
  have hmfac := RemainingAnalytic41.factorization_eq_one_of_dvd_not_sq_dvd
    hp hm0 hpm hnotSq
  have hidx : c - m ∈ Finset.range (c - b) := Finset.mem_range.mpr (by omega)
  have hterms : ∀ i ∈ Finset.range (c - b), c - i ≠ 0 := by
    intro i hi
    have hh := Finset.mem_range.mp hi
    omega
  unfold falling
  rw [Nat.factorization_prod_apply]
  · rw [Finset.sum_eq_single (c - m)]
    · have heq : c - (c - m) = m := by omega
      rw [heq]
      exact hmfac
    · intro i hi hne
      have hir : i < c - b := Finset.mem_range.mp hi
      have hnot : ¬ p ∣ c - i := by
        intro hdiv
        have heq : c - i = m := shortInterval_multiple_unique141 hgap
          (by omega) (Nat.sub_le _ _) hbm hmc hdiv hpm
        have hidxeq : i = c - m := by omega
        exact hne hidxeq
      exact Nat.factorization_eq_zero_of_not_dvd hnot
    · simp only [hidx, not_true_eq_false, false_implies]
  · exact hterms

/-- A prime divides the interval product exactly when its quotient increases. -/
theorem prime_dvd_falling_iff_quotient141 {b c p : ℕ}
    (hbc : b < c) (hp : p.Prime) :
    p ∣ falling (c - b) c ↔ b / p < c / p := by
  constructor
  · intro hdiv
    obtain ⟨i, hi, hpi⟩ :=
      RemainingAnalytic34.exists_factor_dvd_of_prime_dvd_falling hp hdiv
    have him : b < c - i := by omega
    obtain ⟨k, hk⟩ := hpi
    have hbk : b / p < k := by
      by_contra hn
      have hkle : k ≤ b / p := by omega
      have hmul : p * k ≤ b := by
        calc
          p * k ≤ p * (b / p) := Nat.mul_le_mul_left p hkle
          _ = (b / p) * p := Nat.mul_comm _ _
          _ ≤ b := Nat.div_mul_le_self b p
      omega
    have hkc : k ≤ c / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by
      have hmk : k * p = c - i := by simpa only [Nat.mul_comm] using hk.symm
      rw [hmk]
      exact Nat.sub_le _ _)
    exact lt_of_lt_of_le hbk hkc
  · intro hquot
    let m : ℕ := (b / p + 1) * p
    have hbm : b < m := X_lt_succ_natDiv_mul123 hp.one_le
    have hmc : m ≤ c := (Nat.le_div_iff_mul_le hp.pos).mp (by omega)
    have hidx : c - m ∈ Finset.range (c - b) := Finset.mem_range.mpr (by omega)
    have hpm : p ∣ m := by dsimp [m]; exact dvd_mul_left _ _
    unfold falling
    apply dvd_trans hpm
    have heq : c - (c - m) = m := by omega
    rw [← heq]
    exact Finset.dvd_prod_of_mem _ hidx

/-- If there is at most one multiple, the natural quotient difference is 0 or 1. -/
theorem quotient_difference_le_one141 {b c p : ℕ} (hbc : b < c)
    (hp : 0 < p) (hgap : c - b < p) : c / p - b / p ≤ 1 := by
  have hupper : b < (b / p + 1) * p := X_lt_succ_natDiv_mul123 (by omega)
  have hlow : (c / p) * p ≤ c := Nat.div_mul_le_self c p
  by_contra hnot
  have hsteps : b / p + 2 ≤ c / p := by omega
  have hmul := Nat.mul_le_mul_right p hsteps
  have heq : (b / p + 2) * p = (b / p + 1) * p + p := by ring
  rw [heq] at hmul
  omega

/-- In a high band, prime divisibility already gives the full valuation-one condition. -/
theorem highBand_good_iff_quotient141 {a b c p : ℕ}
    (hbc : b < c) (hp : p.Prime) (hap : a < p)
    (hgap : c - b < p) (hsquare : c < p ^ 2) :
    (a < p ∧ p ∣ falling (c - b) c ∧ ¬ p ^ 2 ∣ falling (c - b) c) ↔
      b / p < c / p := by
  constructor
  · intro hh
    exact (prime_dvd_falling_iff_quotient141 hbc hp).mp hh.2.1
  · intro hquot
    have hdiv := (prime_dvd_falling_iff_quotient141 hbc hp).mpr hquot
    obtain ⟨i, hi, hpi⟩ :=
      RemainingAnalytic34.exists_factor_dvd_of_prime_dvd_falling hp hdiv
    have hfac := falling_factorization_one_of_highBand141 hbc hp hgap hsquare
      (by omega : b < c - i) (Nat.sub_le c i) hpi
    have hfall0 : falling (c - b) c ≠ 0 :=
      Nat.ne_of_gt (falling_pos_of_le (Nat.sub_le c b))
    refine ⟨hap, hdiv, ?_⟩
    intro hsq
    have htwo : 2 ≤ (falling (c - b) c).factorization p :=
      (hp.pow_dvd_iff_le_factorization hfall0).mp hsq
    omega

/-- The exact high-band prime count, with all natural division floors retained. -/
theorem sparseGoodCount_eq_floorSum141 {a b c P : ℕ}
    (hbc : b < c) (hP : 2 ≤ P) (haP : a < P)
    (hgapP : c - b < P) (hsquareP : c < P ^ 2) :
    ((sparseGoodPrimes127 a b c P).card : ℝ) =
      ∑ p ∈ (Finset.Icc P (2 * P)).filter Nat.Prime,
        ((c / p - b / p : ℕ) : ℝ) := by
  classical
  let S : Finset ℕ := (Finset.Icc P (2 * P)).filter Nat.Prime
  have hsets : sparseGoodPrimes127 a b c P = S.filter (fun p => b / p < c / p) := by
    ext p
    simp only [sparseGoodPrimes127, S, Finset.mem_filter]
    constructor
    · rintro ⟨hI, hprime, hap, hdiv, hsq⟩
      exact ⟨⟨hI, hprime⟩, (prime_dvd_falling_iff_quotient141 hbc hprime).mp hdiv⟩
    · rintro ⟨⟨hI, hprime⟩, hquot⟩
      have hPp : P ≤ p := (Finset.mem_Icc.mp hI).1
      have hPP : P ^ 2 ≤ p ^ 2 := by
        simpa only [pow_two] using Nat.mul_le_mul hPp hPp
      have hsq : c < p ^ 2 := lt_of_lt_of_le hsquareP hPP
      have hd := (highBand_good_iff_quotient141 hbc hprime (lt_of_lt_of_le haP hPp)
        (lt_of_lt_of_le hgapP hPp) hsq).mpr hquot
      exact ⟨hI, hprime, hd⟩
  rw [hsets]
  calc
    ((S.filter (fun p => b / p < c / p)).card : ℝ) =
        ∑ p ∈ S, if b / p < c / p then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ p ∈ S, ((c / p - b / p : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hpS
      have hd := Finset.mem_filter.mp hpS
      have hprime : p.Prime := hd.2
      have hPp : P ≤ p := (Finset.mem_Icc.mp hd.1).1
      have hone := quotient_difference_le_one141 hbc hprime.pos (lt_of_lt_of_le hgapP hPp)
      by_cases hquot : b / p < c / p
      · have heq : c / p - b / p = 1 := by omega
        simp only [hquot, ite_true, heq, Nat.cast_one]
      · have heq : c / p - b / p = 0 := by omega
        simp only [hquot, ite_false, heq, Nat.cast_zero]

/-- A concrete reciprocal-prime lower estimate constructs the sparse packet
in this range, without a separate square-divisor deletion estimate. -/
theorem sparseHighBand_from_floorMass141 {a b c P : ℕ}
    (hbc : b < c) (hP : 2 ≤ P) (haP : a < P)
    (hgapP : c - b < P) (hsquareP : c < P ^ 2)
    (H : ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
      ∑ p ∈ (Finset.Icc P (2 * P)).filter Nat.Prime, ((c / p - b / p : ℕ) : ℝ)) :
    ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
      ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  rw [sparseGoodCount_eq_floorSum141 hbc hP haP hgapP hsquareP]
  exact H


/-! ### E. Replace unnecessary SHARP Weil by a coarse curve-count theorem

The external Math Inc. theorem riemann_hypothesis_hec has constant 5*degree,
not degree-1. We do NOT claim it proves NormalizedOddWeil139. Instead we retain
its actual statement below, derive a coarse anchor bound, and use larger good
prime thresholds in a NEW endgame route. The previous sharp route is untouched.
-/

section CurveCounting
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Actual number of affine pairs satisfying y^2=f(x), not a renamed character sum. -/
noncomputable def affineCurveCount141 (f : F → F) : ℕ :=
  Fintype.card {p : F × F // p.2 ^ 2 = f p.1}

/-- The affine pairs decompose exactly into their x-coordinate fibers. -/
noncomputable def affineCurveFiberEquiv141 (f : F → F) :
    {p : F × F // p.2 ^ 2 = f p.1} ≃ ((x : F) × {y : F // y ^ 2 = f x}) where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv p := by rcases p with ⟨⟨x, y⟩, h⟩; rfl
  right_inv p := by rcases p with ⟨x, y, h⟩; rfl

theorem squareFiber_card141 (hF : ringChar F ≠ 2) (a : F) :
    (Fintype.card {y : F // y ^ 2 = a} : ℝ) = 1 + realQuadraticChar138 a := by
  have hc := quadraticChar_card_sqrts hF a
  have hcard : Fintype.card {y : F // y ^ 2 = a} =
      ({y : F | y ^ 2 = a}.toFinset).card :=
    (Set.toFinset_card ({y : F | y ^ 2 = a} : Set F)).symm
  rw [hcard]
  have hcast : (({y : F | y ^ 2 = a}.toFinset).card : ℝ) =
      realQuadraticChar138 a + 1 := by
    unfold realQuadraticChar138
    exact_mod_cast hc
  linarith only [hcast]

/-- Exact point-count/character-sum identity in odd characteristic. -/
theorem affineCurveCount_eq_character141 (hF : ringChar F ≠ 2) (f : F → F) :
    (affineCurveCount141 f : ℝ) = (Fintype.card F : ℝ) +
      ∑ x : F, realQuadraticChar138 (f x) := by
  have hc : affineCurveCount141 f = ∑ x : F, Fintype.card {y : F // y ^ 2 = f x} := by
    unfold affineCurveCount141
    rw [Fintype.card_congr (affineCurveFiberEquiv141 f), Fintype.card_sigma]
  rw [hc, Nat.cast_sum]
  simp_rw [squareFiber_card141 hF]
  rw [Finset.sum_add_distrib]
  simp

/-- Quadratic twisting changes the sign of the trace, with no asymptotic error. -/
theorem affineCurveCount_twist_sum141 (hF : ringChar F ≠ 2)
    (f : F → F) (ν : F) (hν : realQuadraticChar138 ν = -1) :
    (affineCurveCount141 f : ℝ) + (affineCurveCount141 (fun x => ν * f x) : ℝ) =
      2 * (Fintype.card F : ℝ) := by
  rw [affineCurveCount_eq_character141 hF, affineCurveCount_eq_character141 hF]
  simp_rw [realQuadraticChar_mul138, hν, neg_one_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- Retaining known zeros improves the trivial bound from q to q-degree. -/
theorem rootCharacter_rootAware_trivial141 (U : Finset F) :
    |∑ x : F, realQuadraticChar138 (rootProduct138 U x)| ≤
      (Fintype.card F : ℝ) - (U.card : ℝ) := by
  have hpoint : ∀ x : F, |realQuadraticChar138 (rootProduct138 U x)| ≤
      1 - (if x ∈ U then (1 : ℝ) else 0) := by
    intro x
    by_cases hx : x ∈ U
    · have hz := (rootProduct_zero_iff138 U x).mpr hx
      simp only [hz, realQuadraticChar_zero138, abs_zero, hx, ite_true, sub_self, le_refl]
    · simpa only [hx, ite_false, sub_zero] using realQuadraticChar_abs138 (rootProduct138 U x)
  calc
    _ ≤ ∑ x : F, |realQuadraticChar138 (rootProduct138 U x)| :=
      RemainingAnalytic117.abs_finset_sum_le_sum_abs117 _ _
    _ ≤ ∑ x : F, (1 - (if x ∈ U then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum (fun x hx => hpoint x)
    _ = _ := by
      have hfilter : (Finset.univ : Finset F).filter (fun x : F => x ∈ U) = U := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.sum_sub_distrib, ← Finset.sum_filter, hfilter]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The actual monic polynomial corresponding to the finite root product. -/
noncomputable def rootPolynomial141 (U : Finset F) : Polynomial F :=
  ∏ u ∈ U, (Polynomial.X - Polynomial.C u)

@[simp] theorem rootPolynomial_eval141 (U : Finset F) (x : F) :
    (rootPolynomial141 U).eval x = rootProduct138 U x := by
  unfold rootPolynomial141 rootProduct138
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro u hu
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem rootPolynomial_natDegree141 (U : Finset F) :
    (rootPolynomial141 U).natDegree = U.card := by
  unfold rootPolynomial141
  exact Polynomial.natDegree_finsetProd_X_sub_C_eq_card U (fun u : F => u)

/-- The degree remains the cardinality even over an extension field. -/
theorem mappedRootPolynomial_natDegree141
    {K : Type*} [Field K] (φ : F →+* K) (U : Finset F) :
    ((rootPolynomial141 U).map φ).natDegree = U.card := by
  have heq : (rootPolynomial141 U).map φ =
      ∏ u ∈ U, (Polynomial.X - Polynomial.C (φ u)) := by
    simp [rootPolynomial141, Polynomial.map_prod]
  rw [heq]
  exact Polynomial.natDegree_finsetProd_X_sub_C_eq_card U (fun u : F => φ u)

/-- Odd degree rules out a polynomial square even over the algebraic closure.
This supplies the actual geometric nonsquare hypothesis of the external theorem. -/
theorem rootPolynomial_odd_not_square_over_closure141
    (U : Finset F) (hodd : Odd U.card) :
    ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = (rootPolynomial141 U).map (algebraMap F (AlgebraicClosure F)) := by
  rintro ⟨g, hg⟩
  have hd := mappedRootPolynomial_natDegree141 (algebraMap F (AlgebraicClosure F)) U
  have hcardpos : 0 < U.card := by obtain ⟨k, hk⟩ := hodd; omega
  have hg0 : g ≠ 0 := by
    intro hz
    have hn := congrArg Polynomial.natDegree hg
    rw [hz, zero_mul, Polynomial.natDegree_zero, hd] at hn
    omega
  have hn := congrArg Polynomial.natDegree hg
  rw [Polynomial.natDegree_mul hg0 hg0, hd] at hn
  obtain ⟨k, hk⟩ := hodd
  omega

end CurveCounting

/-- EXACT coarse sufficient statement matched by the retrieved external theorem.
This is not defined as proved. The optional import file constructs it by calling
riemann_hypothesis_hec, and must be compiled separately with that dependency. -/
def CoarseHyperellipticCount141 : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    letI : Fact p.Prime := ⟨hp⟩
    ∀ f : Polynomial (ZMod p), 3 ≤ f.natDegree →
      (¬ ∃ g : Polynomial (AlgebraicClosure (ZMod p)),
        g * g = f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) →
      6 * f.natDegree < p →
      |(p : ℝ) - (affineCurveCount141 (fun x => f.eval x) : ℝ)| <
        5 * (f.natDegree : ℝ) * Real.sqrt (p : ℝ)

/-- All odd degrees, including the linear and small-field ranges. -/
theorem coarseOddCharacter_bound141 (HC : CoarseHyperellipticCount141)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod p), Odd U.card →
      |∑ x : ZMod p, realQuadraticChar138 (rootProduct138 U x)| ≤
        5 * (U.card : ℝ) * Real.sqrt (p : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro U hodd
  have hchar : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  have hpos : 0 < U.card := by obtain ⟨k, hk⟩ := hodd; omega
  by_cases hd : 3 ≤ U.card
  · by_cases hlarge : 6 * U.card < p
    · have hh := HC p hp (rootPolynomial141 U)
        (by simpa only [rootPolynomial_natDegree141] using hd)
        (rootPolynomial_odd_not_square_over_closure141 U hodd)
        (by simpa only [rootPolynomial_natDegree141] using hlarge)
      have heval : (fun x : ZMod p => (rootPolynomial141 U).eval x) =
          (fun x : ZMod p => rootProduct138 U x) := by
        funext x
        exact rootPolynomial_eval141 U x
      rw [heval, rootPolynomial_natDegree141] at hh
      have he := affineCurveCount_eq_character141 hchar
        (fun x : ZMod p => rootProduct138 U x)
      simp only [ZMod.card] at he
      rw [he] at hh
      have hid : (p : ℝ) - ((p : ℝ) +
          ∑ x : ZMod p, realQuadraticChar138 (rootProduct138 U x)) =
          -(∑ x : ZMod p, realQuadraticChar138 (rootProduct138 U x)) := by ring
      rw [hid, abs_neg] at hh
      exact hh.le
    · have htriv := rootCharacter_rootAware_trivial141 U
      simp only [ZMod.card] at htriv
      have hpD : (p : ℝ) ≤ 6 * (U.card : ℝ) := by exact_mod_cast le_of_not_gt hlarge
      have hdR : (3 : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hd
      have hs0 := Real.sqrt_nonneg (p : ℝ)
      have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ (p : ℝ) by positivity)
      have hsD : Real.sqrt (p : ℝ) ≤ 5 * (U.card : ℝ) := by
        have hd0 : (0 : ℝ) ≤ (U.card : ℝ) := by positivity
        have hd1 : (1 : ℝ) ≤ (U.card : ℝ) := by linarith only [hdR]
        have hdsq : (U.card : ℝ) ≤ (U.card : ℝ) ^ 2 := by
          nlinarith only [mul_nonneg hd0 (sub_nonneg.mpr hd1)]
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith only [hpD, hdsq, hd0]
      have hmul := mul_le_mul_of_nonneg_right hsD hs0
      have hd0 : (0 : ℝ) ≤ (U.card : ℝ) := by positivity
      nlinarith only [htriv, hmul, hs2, hd0]
  · have hcard : U.card = 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [rootCharacterSum_card_one138 hchar U hcard, abs_zero]
    positivity

/-- Inversion gives every even degree, without upgrading the constant to a
sharp Weil bound. The missing-point correction is explicitly absorbed. -/
theorem coarseDistinctCharacter_bound141 (HC : CoarseHyperellipticCount141)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod p), U.Nonempty →
      |∑ x : ZMod p, realQuadraticChar138 (rootProduct138 U x)| ≤
        5 * (U.card : ℝ) * Real.sqrt (p : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro U hne
  rcases Nat.even_or_odd U.card with heven | hodd
  · obtain ⟨a, ha⟩ := hne
    have hpos : 0 < U.card := Finset.card_pos.mpr ⟨a, ha⟩
    have hc := reciprocalRoots_card139 U a ha
    have hVodd : Odd (reciprocalRoots139 U a).card := by
      obtain ⟨k, hk⟩ := heven
      refine ⟨k - 1, ?_⟩
      omega
    have hV := coarseOddCharacter_bound141 HC p hp hp2 (reciprocalRoots139 U a) hVodd
    have htrans := characterSum_even_bound139 U a ha heven _ hV
    have hcard : ((reciprocalRoots139 U a).card : ℝ) + 1 = (U.card : ℝ) := by
      exact_mod_cast (show (reciprocalRoots139 U a).card + 1 = U.card by omega)
    have hs : 1 ≤ Real.sqrt (p : ℝ) := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp.one_le)
    have hcardR := congrArg (fun z : ℝ => 5 * z * Real.sqrt (p : ℝ)) hcard
    nlinarith only [htrans, hcardR, hs]
  · exact coarseOddCharacter_bound141 HC p hp hp2 U hodd

/-- The exact two-family product requires constant 10H with this coarse input,
not the former 2H. Common roots are retained and cost at most their cardinality. -/
theorem linearProduct_coarse_bound141 (HC : CoarseHyperellipticCount141)
    {lam r j t h ell : ℕ} (hp : lam.Prime)
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 0 < ell) (ht : t < h)
    (hnp : h ≠ 1 ∨ ell ≠ 1) (hsep : 2 * r * max h ell < lam)
    (c : ZMod lam) (hc : c ≠ 0) :
    |((RemainingAnalytic96.linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| ≤
      10 * ((max h ell : ℕ) : ℝ) * Real.sqrt (lam : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  have hgeo := legalPrime_geometry138 hj hjr hh hell ht hsep
  have hl2 : lam ≠ 2 := by omega
  have hr0 := RemainingAnalytic63.r_nonzero_mod63 hp hj hjr hh hell hsep
  have hj0 := RemainingAnalytic63.j_nonzero_mod63 hp hj hjr hh hell hsep
  let U := iRoots138 lam r ell
  let V := vRoots138 lam j t h
  have hne : (oddRoots138 U V).Nonempty :=
    anchorOddRoots_nonempty138 hp hj hjr hh hell ht hnp hsep
  have hodd := coarseDistinctCharacter_bound141 HC lam hp hl2 (oddRoots138 U V) hne
  have hcorr := squareDeletion_sum_bound138 U V
  have htri := abs_add_le
    ((∑ x : ZMod lam, realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x)) -
      ∑ x : ZMod lam, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x))
    (∑ x : ZMod lam, realQuadraticChar138 (rootProduct138 (oddRoots138 U V) x))
  rw [sub_add_cancel] at htri
  have hbalance : ((oddRoots138 U V).card : ℝ) + 2 * ((U ∩ V).card : ℝ) =
      (U.card : ℝ) + (V.card : ℝ) := by exact_mod_cast oddRoots_card_balance138 U V
  have hI : U.card = ell - 1 := iRoots_card138 hr0 hell hgeo.2.2.1
  have hV : V.card = h - 1 := vRoots_card138 hj0 ht hgeo.2.1
  have htotal : (U.card : ℝ) + (V.card : ℝ) ≤ 2 * ((max h ell : ℕ) : ℝ) := by
    exact_mod_cast (show U.card + V.card ≤ 2 * max h ell by omega)
  have hs : 1 ≤ Real.sqrt (lam : ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (lam : ℝ) by exact_mod_cast hp.one_le)
  have hC0 : (0 : ℝ) ≤ ((U ∩ V).card : ℝ) := by positivity
  have hCscale := mul_le_mul_of_nonneg_left hs hC0
  have hbalanceR := congrArg (fun z : ℝ => z * Real.sqrt (lam : ℝ)) hbalance
  have htotalR :
      ((U.card : ℝ) + (V.card : ℝ)) * Real.sqrt (lam : ℝ) ≤
        (2 * ((max h ell : ℕ) : ℝ)) * Real.sqrt (lam : ℝ) :=
    mul_le_mul_of_nonneg_right htotal (Real.sqrt_nonneg (lam : ℝ))
  rw [linearProduct_abs_eq_rootPair138 hp hr0 hj0 hgeo.2.2.1 hgeo.2.1 c hc]
  change |∑ x : ZMod lam, realQuadraticChar138 (rootProduct138 U x * rootProduct138 V x)| ≤ _
  nlinarith only [hodd, hcorr, htri, hbalanceR, htotalR, hCscale, hC0]


/-! ### F. Larger auxiliary primes make the COARSE Weil bound sufficient -/

/-- With the coarse character estimate, the same 3/4 residue restriction holds
once lambda>=4096H^2. No claim is made for the older 64H^2 threshold. -/
theorem coarse_squareResidueRestriction141 (HC : CoarseHyperellipticCount141)
    {a r j t h ell lam : ℕ}
    (hj : 0 < j) (hjr : j < r) (hh : 0 < h) (hell : 0 < ell) (ht : t < h)
    (hnp : h ≠ 1 ∨ ell ≠ 1) (hp : lam.Prime) (ha : a < lam)
    (hsep : 2 * r * max h ell < lam) (hsize : 4096 * (max h ell) ^ 2 ≤ lam) :
    4 * RemainingAnalytic37.AnchorSquareResidueCount a r j t h ell lam ≤ 3 * lam := by
  have hlead := RemainingAnalytic65.anchorLeadingCoeffNonzeroLegal_proved65
    a r j t h ell lam hj hjr hh hell ht hp ha hsep
  have hchar := linearProduct_coarse_bound141 HC hp hj hjr hh hell ht hnp hsep
    (RemainingAnalytic61.anchorLeadingCoeff61 a r j lam) hlead
  rw [← RemainingAnalytic96.anchorQuadraticSum_eq_linearProduct96 hp] at hchar
  have hzero := RemainingAnalytic65.anchorZeroBoundLegal_proved65
    a r j t h ell lam hj hjr hh hell ht hp ha hsep
  have hbridge := (RemainingAnalytic60.anchorSquareCountCharacterBridge_from_identity60
    RemainingAnalytic66.anchorQuadraticIndicatorSumIdentity_proved66)
      a r j t h ell lam hp
  have hsizeR : 4096 * (((max h ell : ℕ) : ℝ)) ^ 2 ≤ (lam : ℝ) := by exact_mod_cast hsize
  have hH1 : (1 : ℝ) ≤ ((max h ell : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ max h ell by omega)
  have hH0 : (0 : ℝ) ≤ ((max h ell : ℕ) : ℝ) := by positivity
  have hs0 := Real.sqrt_nonneg (lam : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ (lam : ℝ) by positivity)
  have hsH : 64 * ((max h ell : ℕ) : ℝ) ≤ Real.sqrt (lam : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hsH hs0
  have hHsq : ((max h ell : ℕ) : ℝ) ≤ (((max h ell : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hzR : (RemainingAnalytic59.AnchorZeroCount59 a r j t h ell lam : ℝ) ≤
      2 * ((max h ell : ℕ) : ℝ) := by exact_mod_cast hzero
  have hresult : (4 : ℝ) *
      (RemainingAnalytic37.AnchorSquareResidueCount a r j t h ell lam : ℝ) ≤ 3 * (lam : ℝ) := by
    nlinarith only [hbridge, hchar, hzR, hprod, hs2, hsizeR, hHsq]
  exact_mod_cast hresult

/-- Any fixed H^2 coefficient, not just 64, is eventually dominated by the
auxiliary prime scale under the SAME exponent condition 3alpha+8eta<1. -/
theorem auxiliaryH2_arbitrary_constant141 (α η C : ℝ)
    (hα : 0 < α) (hη : 0 < η) (hcond : 3 * α + 8 * η < 1) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ X r h ell : ℕ, N ≤ X → 1 ≤ r →
      (r : ℝ) ≤ 2 * (X : ℝ) ^ α →
      ((max h ell : ℕ) : ℝ) ≤ 2 * (X : ℝ) ^ η →
      C * (((max h ell : ℕ) : ℝ)) ^ 2 ≤ Real.sqrt ((X / r : ℕ) : ℝ) := by
  have hα1 : α < 1 := by linarith
  have hmargin : 0 < (1 - α) / 2 - 2 * η := by linarith
  obtain ⟨NR, hNR⟩ := RemainingAnalytic56.sqrtRatioPowerLower_proved56 α hα hα1
  obtain ⟨NC, hNC⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := (1 - α) / 2 - 2 * η) (C := 8 * C + 1) hmargin
  refine ⟨max 1 (max NR NC), ?_⟩
  intro X r h ell hX hr hrα hH
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXR : NR ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXC : NC ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hsqrt := hNR X r hXR hr hrα
  have hp2 : 0 < (X : ℝ) ^ (2 * η) := Real.rpow_pos_of_pos hXp _
  have hmul := mul_lt_mul_of_pos_right (hNC X hXC) hp2
  have hid : (X : ℝ) ^ ((1 - α) / 2 - 2 * η) * (X : ℝ) ^ (2 * η) =
      (X : ℝ) ^ ((1 - α) / 2) := by rw [← Real.rpow_add hXp, sub_add_cancel]
  rw [hid] at hmul
  have hpow : ((X : ℝ) ^ η) ^ 2 = (X : ℝ) ^ (2 * η) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hXp.le]
    congr 1
    ring
  have hHsq : (((max h ell : ℕ) : ℝ)) ^ 2 ≤ 4 * (X : ℝ) ^ (2 * η) := by
    calc
      (((max h ell : ℕ) : ℝ)) ^ 2 ≤ (2 * (X : ℝ) ^ η) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hH 2
      _ = 4 * (X : ℝ) ^ (2 * η) := by
        rw [mul_pow, hpow]
        norm_num
  have hscale := mul_le_mul_of_nonneg_left hHsq hC
  nlinarith only [hsqrt, hmul, hscale, hp2]

/-- The three auxiliary conditions with the new coefficient 4096 are supplied
internally. The previous 64-threshold record is not assumed to imply this. -/
theorem coarseAuxiliaryGood141 (α η A0 : ℝ)
    (hα : 0 < α) (hη : 0 < η) (hcond : 3 * α + 8 * η < 1) (hA0 : 0 < A0) :
    ∃ N : ℕ, ∀ X r a h ell lam : ℕ,
      N ≤ X → 1 ≤ r → (r : ℝ) ≤ 2 * (X : ℝ) ^ α →
      0 < h → 0 < ell →
      ((max h ell : ℕ) : ℝ) ≤ 2 * (X : ℝ) ^ η →
      (a = 0 ∨ (a : ℝ) ≤ A0 * ((max h ell : ℕ) : ℝ) * Real.log (X : ℝ)) →
      lam ∈ RemainingAnalytic37.auxiliaryPrimes (X / r) →
      a < lam ∧ 2 * r * max h ell < lam ∧ 4096 * (max h ell) ^ 2 ≤ lam := by
  obtain ⟨N0, hN0⟩ := RemainingAnalytic56.legalAuxiliaryThresholds_proved56
    α η A0 hα hη hcond hA0
  obtain ⟨N1, hN1⟩ := auxiliaryH2_arbitrary_constant141 α η 4096 hα hη hcond (by norm_num)
  refine ⟨max N0 N1, ?_⟩
  intro X r a h ell lam hX hr hrα hh hell hH ha hlam
  have hx0 : N0 ≤ X := le_trans (le_max_left _ _) hX
  have hx1 : N1 ≤ X := le_trans (le_max_right _ _) hX
  have hbase := hN0 X r a h ell hx0 hr hrα hh hell hH ha
  have hsize := hN1 X r h ell hx1 hr hrα hH
  have hpl : Real.sqrt ((X / r : ℕ) : ℝ) < (lam : ℝ) :=
    (Finset.mem_filter.mp hlam).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast lt_trans hbase.1 hpl
  · exact_mod_cast lt_trans hbase.2.1 hpl
  · exact_mod_cast (le_trans hsize hpl.le)

/-- Proposition-5.1 one-tuple bound with a COARSE external curve estimate.
Prime supply, additive large sieve, root reduction, and the enlarged thresholds
are all provided by actual preceding constructions. -/
theorem legalAnchorLargeL_from_coarse141 (HP : PsiMediumPNT134)
    (HC : CoarseHyperellipticCount141) : RemainingAnalytic38.LegalAnchorTupleBoundLargeL := by
  have htheta := thetaLogSqRemainder_from_mediumPNT134 HP
  have hSupply := RemainingAnalytic93.auxiliaryPrimeSupply_from_thetaGap93
    (dyadicThetaGap_from_dense127 (denseTopThetaMass_from_thetaRemainder127 htheta))
  have hEnergy := RemainingAnalytic92.analyticLargeSieveEnergy_from_classical92
    classicalPrimeAdditiveLargeSieve_proved135
  intro α η A0 hα hη hcond hA0
  obtain ⟨cp, hcp, Np, hPrimeSupply⟩ := hSupply
  obtain ⟨Cls, hCls, Nls, hLargeSieve⟩ := hEnergy
  obtain ⟨Ng, hGood⟩ := coarseAuxiliaryGood141 α η A0 hα hη hcond hA0
  let K : ℝ := 3 * Cls / cp
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, Ng, max 2 (max Np Nls), ?_⟩
  intro X r a j t h ell hX hLlarge hr1 hrα hj hjr hh hell ht hnp hH ha
  let L : ℕ := X / r
  let T : Finset ℕ := RemainingAnalytic28.AnchorSquareArgs a r j t h ell L
  let J : ℝ := (RemainingAnalytic28.AnchorSquareArgCount a r j t h ell L : ℝ)
  let E : ℝ := ∑ lam ∈ RemainingAnalytic37.auxiliaryPrimes L,
    RemainingAnalytic37.residueEnergy T lam
  let Q : ℝ := ((RemainingAnalytic37.auxiliaryPrimes L).card : ℝ)
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hLlarge
  have hLp : Np ≤ L :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLlarge)
  have hLls : Nls ≤ L :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLlarge)
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (show 1 < L by omega)
  have hlocal : ∀ lam ∈ RemainingAnalytic37.auxiliaryPrimes L,
      J ^ 2 / 3 ≤ RemainingAnalytic37.residueEnergy T lam := by
    intro lam hlam
    have hp : lam.Prime := (Finset.mem_filter.mp hlam).2.1
    have hgood := hGood X r a h ell lam hX hr1 hrα hh hell hH ha hlam
    have hres := coarse_squareResidueRestriction141 HC hj hjr hh hell ht hnp hp
      hgood.1 hgood.2.1 hgood.2.2
    have himage := RemainingAnalytic37.anchor_residue_image_card_le
      RemainingAnalytic39.squareArgumentReducesMod_proved
      (a := a) (r := r) (j := j) (t := t) (h := h) (ell := ell) (L := L) hp
    exact RemainingAnalytic37.residueEnergy_lower_of_support T lam
      (RemainingAnalytic37.AnchorSquareResidueCount a r j t h ell lam) himage hres
  have hLower : Q * J ^ 2 / 3 ≤ E := by
    have hsum := Finset.sum_le_sum hlocal
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_div_assoc] using hsum
  have hTsub : T ⊆ Finset.Icc 1 L :=
    RemainingAnalytic38.anchorSquareArgs_subset_Icc a r j t h ell L
  have hUpper : E ≤ Cls * (L : ℝ) * J := hLargeSieve L hLls T hTsub
  have hSupply' : cp * Real.sqrt (L : ℝ) / Real.log (L : ℝ) ≤ Q := hPrimeSupply L hLp
  have hJnonneg : 0 ≤ J := by dsimp [J]; positivity
  have hSolve := RemainingAnalytic37.solve_energy_squeeze
    hJnonneg hLreal hcp hCls.le hSupply' hLower hUpper
  simpa only [K, L, J] using hSolve

/-- Larger constant thresholds do not alter any final density exponents. -/
theorem uniformAnchor_from_coarse141 (HP : PsiMediumPNT134)
    (HC : CoarseHyperellipticCount141) : Tasks.UniformAnchorSieve :=
  RemainingAnalytic54.anchorUniform_from_growth_global54
    (factorial_growth_of_log_q (logQGrowth_from_theta130 (thetaLogSqRemainder_from_mediumPNT134 HP)))
    (RemainingAnalytic44.legalAnchorTupleBoundGlobal_from_largeL
      (legalAnchorLargeL_from_coarse141 HP HC))

/-! ### G. Rebuild the corrected final core without the sharp Weil record -/

structure RemainingNonPNTInputs141 where
  sparse_sublog_count : SparseSublogCount141 4
  harman_forward_bad_density : DensityZero forwardBadIntervals141
  coarse_hyperelliptic_count : CoarseHyperellipticCount141

/-- FOUR total external inputs, counting HP. The coarse curve statement is
faithful to a retrieved external theorem, but is NOT silently imported here.
The corrected finite-exception cofactor count remains the only count route. -/
noncomputable def core18_from_remaining141 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs141) : AnalyticCore18 := by
  have HT := thetaLogSqRemainder_from_mediumPNT134 HP
  let hLim := AFiniteDensityLimit_from_theta133 HT
  let hTail := RemainingAnalytic131.AUniformTail_from_theta131 HT
  let hApprox := A_approximation_of_limit_tail hLim hTail
  have hAdensity : HasDensity A hApprox.delta := A_density_of_approximation hApprox
  have hPNT := primeCountRelativePNT_from_theta130 HT
  have hLogQ := logQGrowth_from_theta130 HT
  have hGrowth := factorial_growth_of_log_q hLogQ
  have hB : HasDensity (B alpha) (densityConstant hApprox.delta) :=
    bDensity_from_corrected_count130 hLim hTail hPNT bareCofactorMassLimit_proved130
      (cofactorIntegerCountCorrected_from_growth130 hLogQ) hAdensity
  have hDenseTheta := denseTopThetaMass_from_thetaRemainder127 HT
  have hDense := denseBranch_from_topIntervalMass
    (denseTopIntervalPrimeMass_from_logMass115
      (RemainingAnalytic119.denseTopLogPrimeMass_from_theta119 hDenseTheta))
  have hSparse := sparseWeightedTransfer_from_count127
    (sparseGoodPrimeCount_from_sublog141 HP 4 H.sparse_sublog_count)
  have hBad := harman_bad_density_from_forward141 H.harman_forward_bad_density
  exact {
    deltaA := hApprox.delta
    deltaA_pos := hApprox.delta_pos
    A_density := hAdensity
    B_density := hB
    prime_zero := prime_zero_of_count_decay (primeCountDecay_from_relative130 hPNT)
    short_second := harman_to_secondLargest_proved (harman_from_bad_density127 hBad)
    factorial_growth := hGrowth
    interval_comparison := RemainingAnalytic44.intervalComparison_from_hardened hDense hSparse hGrowth
    uniform_anchor := uniformAnchor_from_coarse141 HP H.coarse_hyperelliptic_count
  }

theorem candidate_main_from_mediumPNT141 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs141) : MainStatement :=
  candidate_main_from_analytic_core18 (core18_from_remaining141 HP H)

theorem positive_lower_density_from_mediumPNT141 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs141) : PositiveLowerDensity D6 :=
  positive_lower_density_from_analytic_core18 (core18_from_remaining141 HP H)

/-! Individual checkpoints: a successful implication is not a constructed input. -/
-- Frozen historical output: #print axioms characterSum_reflection_zero140
-- Frozen historical output: #print axioms characterSum_oddFunction_zero140
-- Frozen historical output: #print axioms rootCharacter_square_sum140
-- Frozen historical output: #print axioms medium_logPower_eventually_small141
-- Frozen historical output: #print axioms primePower_logPower_eventually_small141
-- Frozen historical output: #print axioms thetaLogPower_from_mediumPNT141
-- Frozen historical output: #print axioms logPower_endpoint_error141
-- Frozen historical output: #print axioms sparse_logWide_from_PNT141
-- Frozen historical output: #print axioms sparseGoodPrimeCount_iff_sublog141
-- Frozen historical output: #print axioms harmanShift_scale141
-- Frozen historical output: #print axioms backwardBad_prefix_bound141
-- Frozen historical output: #print axioms harmanInitialCutoff_ratio_small141
-- Frozen historical output: #print axioms harman_bad_density_from_forward141
-- Frozen historical output: #print axioms shortInterval_multiple_unique141
-- Frozen historical output: #print axioms falling_factorization_one_of_highBand141
-- Frozen historical output: #print axioms prime_dvd_falling_iff_quotient141
-- Frozen historical output: #print axioms sparseGoodCount_eq_floorSum141
-- Frozen historical output: #print axioms affineCurveCount_eq_character141
-- Frozen historical output: #print axioms affineCurveCount_twist_sum141
-- Frozen historical output: #print axioms rootCharacter_rootAware_trivial141
-- Frozen historical output: #print axioms rootPolynomial_natDegree141
-- Frozen historical output: #print axioms rootPolynomial_odd_not_square_over_closure141
-- Frozen historical output: #print axioms coarseOddCharacter_bound141
-- Frozen historical output: #print axioms coarseDistinctCharacter_bound141
-- Frozen historical output: #print axioms linearProduct_coarse_bound141
-- Frozen historical output: #print axioms coarse_squareResidueRestriction141
-- Frozen historical output: #print axioms auxiliaryH2_arbitrary_constant141
-- Frozen historical output: #print axioms coarseAuxiliaryGood141
-- Frozen historical output: #print axioms legalAnchorLargeL_from_coarse141
-- Frozen historical output: #print axioms uniformAnchor_from_coarse141
-- Frozen historical output: #print axioms core18_from_remaining141
-- Frozen historical output: #print axioms candidate_main_from_mediumPNT141
-- Frozen historical output: #print axioms positive_lower_density_from_mediumPNT141
-- Frozen historical output: #check sparse_logWide_from_PNT141
-- Frozen historical output: #check harman_bad_density_from_forward141
-- Frozen historical output: #check uniformAnchor_from_coarse141
-- Frozen historical output: #check candidate_main_from_mediumPNT141
-- Frozen historical output: #print PsiMediumPNT134
-- Frozen historical output: #print SparseSublogCount141
-- Frozen historical output: #print forwardBadIntervals141
-- Frozen historical output: #print CoarseHyperellipticCount141
-- Frozen historical output: #print RemainingNonPNTInputs141
-- Frozen historical output: #eval "REPAIR 141 REPAIRED CHECKPOINT: new square-loss formulas follow"

end RemainingAnalytic141

/-! ## 142. Exact prime-square deletion and the sparse reciprocal main term

The eight Repair-141 failures are repaired in their original declarations.
This new section is locally UNCOMPILED. No analytic input is postulated here.

The restriction c < P^2 in Repair 141 is removed from the exact sparse formula.
When p > c-b, its unique multiple in (b,c] has valuation one precisely when it
is not a multiple of p^2. Thus the square loss is an EXACT second floor sum.
PNT supplies the positive reciprocal main term. A signed remainder estimate
is still needed to obtain a uniform sparse prime-count theorem.
-/
namespace RemainingAnalytic142

open scoped BigOperators
open RemainingAnalytic123 RemainingAnalytic127 RemainingAnalytic134
open RemainingAnalytic141

set_option maxHeartbeats 4000000

/-! ### A. Unique multiples and exact prime-square deletion -/

/-- An interval contains a multiple of d exactly when its quotient increases.
This is valid for every positive divisor, not only primes. -/
theorem exists_interval_multiple_iff142 {b c d : ℕ} (hd : 0 < d) :
    (∃ m : ℕ, b < m ∧ m ≤ c ∧ d ∣ m) ↔ b / d < c / d := by
  constructor
  · rintro ⟨m, hbm, hmc, k, hk⟩
    have hbk : b / d < k := by
      by_contra hnot
      have hkle : k ≤ b / d := by omega
      have hmul : d * k ≤ b := by
        calc
          d * k ≤ d * (b / d) := Nat.mul_le_mul_left d hkle
          _ = (b / d) * d := Nat.mul_comm _ _
          _ ≤ b := Nat.div_mul_le_self b d
      omega
    have hkc : k ≤ c / d := (Nat.le_div_iff_mul_le hd).mpr (by
      have hkm : k * d = m := by simpa only [Nat.mul_comm] using hk.symm
      rw [hkm]
      exact hmc)
    exact lt_of_lt_of_le hbk hkc
  · intro hquot
    refine ⟨(b / d + 1) * d, ?_, ?_, dvd_mul_left _ _⟩
    · exact X_lt_succ_natDiv_mul123 (by omega)
    · exact (Nat.le_div_iff_mul_le hd).mp (by omega)

/-- In a short interval, all of a prime's valuation comes from its unique
multiple. Unlike the older high-band lemma, its valuation need not be one. -/
theorem falling_factorization_eq_unique_multiple142 {b c p m : ℕ}
    (hbc : b < c) (hp : p.Prime) (hgap : c - b < p)
    (hbm : b < m) (hmc : m ≤ c) (hpm : p ∣ m) :
    (falling (c - b) c).factorization p = m.factorization p := by
  have hidx : c - m ∈ Finset.range (c - b) := Finset.mem_range.mpr (by omega)
  have hterms : ∀ i ∈ Finset.range (c - b), c - i ≠ 0 := by
    intro i hi
    have hir := Finset.mem_range.mp hi
    omega
  unfold falling
  rw [Nat.factorization_prod_apply]
  · rw [Finset.sum_eq_single (c - m)]
    · have heq : c - (c - m) = m := by omega
      rw [heq]
    · intro i hi hne
      have hir : i < c - b := Finset.mem_range.mp hi
      have hnot : ¬ p ∣ c - i := by
        intro hdiv
        have heq : c - i = m := shortInterval_multiple_unique141 hgap
          (by omega) (Nat.sub_le c i) hbm hmc hdiv hpm
        have hidxeq : i = c - m := by omega
        exact hne hidxeq
      exact Nat.factorization_eq_zero_of_not_dvd hnot
    · simp only [hidx, not_true_eq_false, false_implies]
  · exact hterms

/-- The second floor increment detects the square-divisor loss exactly.
The condition p > c-b is essential; c < p^2 is NOT required. -/
theorem primeSquare_dvd_falling_iff_quotient142 {b c p : ℕ}
    (hbc : b < c) (hp : p.Prime) (hgap : c - b < p) :
    p ^ 2 ∣ falling (c - b) c ↔ b / (p ^ 2) < c / (p ^ 2) := by
  have hpSq : p ∣ p ^ 2 := by
    rw [pow_two]
    exact dvd_mul_right p p
  have hF0 : falling (c - b) c ≠ 0 :=
    Nat.ne_of_gt (falling_pos_of_le (Nat.sub_le c b))
  constructor
  · intro hsq
    have hdiv : p ∣ falling (c - b) c := dvd_trans hpSq hsq
    obtain ⟨i, hi, hpi⟩ :=
      RemainingAnalytic34.exists_factor_dvd_of_prime_dvd_falling hp hdiv
    have hbm : b < c - i := by omega
    have hmc : c - i ≤ c := Nat.sub_le _ _
    have hm0 : c - i ≠ 0 := by omega
    have hfac := falling_factorization_eq_unique_multiple142 hbc hp hgap hbm hmc hpi
    have hv : 2 ≤ (falling (c - b) c).factorization p :=
      (hp.pow_dvd_iff_le_factorization hF0).mp hsq
    rw [hfac] at hv
    have hmSq : p ^ 2 ∣ c - i := (hp.pow_dvd_iff_le_factorization hm0).mpr hv
    exact (exists_interval_multiple_iff142 (pow_pos hp.pos 2)).mp
      ⟨c - i, hbm, hmc, hmSq⟩
  · intro hquot
    obtain ⟨m, hbm, hmc, hmSq⟩ :=
      (exists_interval_multiple_iff142 (pow_pos hp.pos 2)).mpr hquot
    have hpm : p ∣ m := dvd_trans hpSq hmSq
    have hm0 : m ≠ 0 := by omega
    have hfac := falling_factorization_eq_unique_multiple142 hbc hp hgap hbm hmc hpm
    have hv : 2 ≤ m.factorization p := (hp.pow_dvd_iff_le_factorization hm0).mp hmSq
    apply (hp.pow_dvd_iff_le_factorization hF0).mpr
    rw [hfac]
    exact hv

/-- The valuation-one indicator is the first increment minus the square increment.
All subtraction on the right of the equality is in the reals. -/
theorem valuationOne_indicator_eq_floorDifference142 {b c p : ℕ}
    (hbc : b < c) (hp : p.Prime) (hgap : c - b < p) :
    (if p ∣ falling (c - b) c ∧ ¬ p ^ 2 ∣ falling (c - b) c then (1 : ℝ) else 0) =
      ((c / p - b / p : ℕ) : ℝ) -
        ((c / (p ^ 2) - b / (p ^ 2) : ℕ) : ℝ) := by
  have hpSq : p ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hD1 := quotient_difference_le_one141 hbc hp.pos hgap
  have hD2 := quotient_difference_le_one141 hbc (pow_pos hp.pos 2)
    (lt_of_lt_of_le hgap hpSq)
  by_cases hq1 : b / p < c / p
  · have hdiv := (prime_dvd_falling_iff_quotient141 hbc hp).mpr hq1
    have hd1 : c / p - b / p = 1 := by omega
    by_cases hq2 : b / (p ^ 2) < c / (p ^ 2)
    · have hsq := (primeSquare_dvd_falling_iff_quotient142 hbc hp hgap).mpr hq2
      have hd2 : c / (p ^ 2) - b / (p ^ 2) = 1 := by omega
      simp [hdiv, hsq, hd1, hd2]
    · have hsq : ¬ p ^ 2 ∣ falling (c - b) c := by
        intro hh
        exact hq2 ((primeSquare_dvd_falling_iff_quotient142 hbc hp hgap).mp hh)
      have hd2 : c / (p ^ 2) - b / (p ^ 2) = 0 := by omega
      simp [hdiv, hsq, hd1, hd2]
  · have hdiv : ¬ p ∣ falling (c - b) c := by
      intro hh
      exact hq1 ((prime_dvd_falling_iff_quotient141 hbc hp).mp hh)
    have hq2 : ¬ b / (p ^ 2) < c / (p ^ 2) := by
      intro hh
      have hsq := (primeSquare_dvd_falling_iff_quotient142 hbc hp hgap).mpr hh
      apply hdiv
      exact dvd_trans (show p ∣ p ^ 2 by rw [pow_two]; exact dvd_mul_right p p) hsq
    have hd1 : c / p - b / p = 0 := by omega
    have hd2 : c / (p ^ 2) - b / (p ^ 2) = 0 := by omega
    simp [hdiv, hd1, hd2]

def primeBand142 (P : ℕ) : Finset ℕ :=
  (Finset.Icc P (2 * P)).filter Nat.Prime

/-- Exact sparse count with square deletion. This removes c<P^2 entirely from
Repair 141's high-band identity, but still requires a<P and c-b<P. -/
theorem sparseGoodCount_eq_squareCorrectedFloorSum142 {a b c P : ℕ}
    (hbc : b < c) (haP : a < P) (hgapP : c - b < P) :
    ((sparseGoodPrimes127 a b c P).card : ℝ) =
      ∑ p ∈ primeBand142 P,
        (((c / p - b / p : ℕ) : ℝ) -
          ((c / (p ^ 2) - b / (p ^ 2) : ℕ) : ℝ)) := by
  classical
  have hsets : sparseGoodPrimes127 a b c P =
      (primeBand142 P).filter (fun p =>
        p ∣ falling (c - b) c ∧ ¬ p ^ 2 ∣ falling (c - b) c) := by
    ext p
    simp only [sparseGoodPrimes127, primeBand142, Finset.mem_filter]
    constructor
    · rintro ⟨hI, hp, hap, hdiv, hsq⟩
      exact ⟨⟨hI, hp⟩, hdiv, hsq⟩
    · rintro ⟨⟨hI, hp⟩, hdiv, hsq⟩
      exact ⟨hI, hp, lt_of_lt_of_le haP (Finset.mem_Icc.mp hI).1, hdiv, hsq⟩
  rw [hsets]
  calc
    _ = ∑ p ∈ primeBand142 P,
        if p ∣ falling (c - b) c ∧ ¬ p ^ 2 ∣ falling (c - b) c then (1 : ℝ) else 0 := by
          rw [← Finset.sum_filter]
          simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hpS
      have hd := Finset.mem_filter.mp hpS
      exact valuationOne_indicator_eq_floorDifference142 hbc hd.2
        (lt_of_lt_of_le hgapP (Finset.mem_Icc.mp hd.1).1)

/-! ### B. Exact main term and signed fractional remainders -/

/-- For d>0 this is the usual fractional part of n/d, implemented without an
integer-floor coercion: division in n/d inside the cast is NATURAL division. -/
noncomputable def quotientRemainder142 (n d : ℕ) : ℝ :=
  (n : ℝ) / (d : ℝ) - ((n / d : ℕ) : ℝ)

theorem quotientRemainder_bounds142 (n : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ quotientRemainder142 n d ∧ quotientRemainder142 n d < 1 := by
  exact RemainingAnalytic124.natDiv_floor_gap_lt_one124 (X := n) (r := d) hd

/-- Exact quotient increment, with no discarded O(1) term. -/
theorem quotientIncrement_expansion142 {b c : ℕ} (hbc : b ≤ c) (d : ℕ) :
    ((c / d - b / d : ℕ) : ℝ) =
      ((c - b : ℕ) : ℝ) / (d : ℝ) +
        quotientRemainder142 b d - quotientRemainder142 c d := by
  have hmono : b / d ≤ c / d := by
    by_cases hd : d = 0
    · simp only [hd, Nat.div_zero, le_refl]
    · exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd)).mpr
        (le_trans (Nat.div_mul_le_self b d) hbc)
  rw [Nat.cast_sub hmono, Nat.cast_sub hbc]
  unfold quotientRemainder142
  ring

noncomputable def squareAdjustedReciprocalMass142 (P : ℕ) : ℝ :=
  ∑ p ∈ primeBand142 P, (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)

/-- The signed fluctuation remaining after exact prime-square deletion. -/
noncomputable def sparseSignedRemainder142 (b c P : ℕ) : ℝ :=
  ∑ p ∈ primeBand142 P,
    (quotientRemainder142 b p - quotientRemainder142 c p -
      quotientRemainder142 b (p ^ 2) + quotientRemainder142 c (p ^ 2))

/-- Exact decomposition for the ORIGINAL sparse valuation-one count. -/
theorem sparseGoodCount_mainTerm_identity142 {a b c P : ℕ}
    (hbc : b < c) (haP : a < P) (hgapP : c - b < P) :
    ((sparseGoodPrimes127 a b c P).card : ℝ) =
      ((c - b : ℕ) : ℝ) * squareAdjustedReciprocalMass142 P +
        sparseSignedRemainder142 b c P := by
  rw [sparseGoodCount_eq_squareCorrectedFloorSum142 hbc haP hgapP]
  unfold squareAdjustedReciprocalMass142 sparseSignedRemainder142
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [quotientIncrement_expansion142 hbc.le p,
    quotientIncrement_expansion142 hbc.le (p ^ 2), Nat.cast_pow]
  ring

/-- Elementary lower bound for each prime's corrected reciprocal weight. -/
theorem correctedReciprocal_term_lower142 {P p : ℕ}
    (hP : 2 ≤ P) (hPp : P ≤ p) (hp2P : p ≤ 2 * P) :
    1 / (4 * (P : ℝ)) ≤ 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_trans hP hPp)
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpup : (p : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hp2P
  have hi0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hihalf : 1 / (p : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hp2
  have hilo : 1 / (2 * (P : ℝ)) ≤ 1 / (p : ℝ) :=
    one_div_le_one_div_of_le hp0 hpup
  have hisq := mul_le_mul_of_nonneg_right hihalf hi0
  have hid : (1 / (p : ℝ)) * (1 / (p : ℝ)) = 1 / (p : ℝ) ^ 2 := by ring
  rw [hid] at hisq
  have hhalflower : (1 / (2 * (P : ℝ))) / 2 = 1 / (4 * (P : ℝ)) := by ring
  have hhalf := div_le_div_of_nonneg_right hilo (by norm_num : (0 : ℝ) ≤ 2)
  rw [hhalflower] at hhalf
  nlinarith only [hisq, hhalf]

/-- PNT supplies the entire reciprocal MAIN TERM, with an explicit constant.
No sparse count or short-interval theorem is an input to this result. -/
theorem squareAdjustedReciprocalMass_from_PNT142 (HP : PsiMediumPNT134) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ P : ℕ, N ≤ P →
      1 / (8 * Real.log (2 * P : ℝ)) ≤ squareAdjustedReciprocalMass142 P := by
  obtain ⟨NT, hNT⟩ := thetaLogPower_from_mediumPNT141 HP 0 (1 / 8) (by norm_num)
  refine ⟨max NT 2, le_max_right _ _, ?_⟩
  intro P hP
  have hP2 : 2 ≤ P := le_trans (le_max_right _ _) hP
  have hPT : NT ≤ P := le_trans (le_max_left _ _) hP
  have h2PT : NT ≤ 2 * P := by omega
  have hlow := hNT P hPT
  have hupp := hNT (2 * P) h2PT
  simp only [pow_zero, mul_one, Nat.cast_mul, Nat.cast_ofNat] at hlow hupp
  have hgap : (P : ℝ) / 2 ≤ thetaPrefix127 (2 * P) - thetaPrefix127 P := by
    have hneg := neg_abs_le (thetaPrefix127 (2 * P) - (2 * (P : ℝ)))
    have hpos := le_abs_self (thetaPrefix127 P - (P : ℝ))
    have hPR : (0 : ℝ) ≤ (P : ℝ) := by positivity
    nlinarith only [hlow, hupp, hneg, hpos, hPR]
  let S : Finset ℕ := (Finset.Icc 1 (2 * P)).filter (fun p => p.Prime ∧ P < p)
  have hsplit := thetaPrefix_split127 (show P ≤ 2 * P by omega)
  have hSsub : S ⊆ primeBand142 P := by
    intro p hp
    obtain ⟨hI, hprime, hPp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hPp.le, (Finset.mem_Icc.mp hI).2⟩, hprime⟩
  have hlogs : (∑ p ∈ S, Real.log (p : ℝ)) ≤
      (S.card : ℝ) * Real.log (2 * P : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ S, Real.log (2 * P : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hd := Finset.mem_filter.mp hp
        have hprime : p.Prime := hd.2.1
        have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
        have hup : (p : ℝ) ≤ (2 * P : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hd.1).2
        exact Real.log_le_log hpos hup
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hsum : thetaPrefix127 (2 * P) - thetaPrefix127 P =
      ∑ p ∈ S, Real.log (p : ℝ) := by
    dsimp [S]
    linarith only [hsplit]
  rw [hsum] at hgap
  have hcard : (S.card : ℝ) ≤ ((primeBand142 P).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSsub
  have hLpos : 0 < Real.log (2 * P : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < 2 * P by omega))
  have hcardL := mul_le_mul_of_nonneg_right hcard hLpos.le
  have hcount : (P : ℝ) / (2 * Real.log (2 * P : ℝ)) ≤
      ((primeBand142 P).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (2 * P : ℝ))).mpr
    nlinarith only [hgap, hlogs, hcardL]
  have hterms : ((primeBand142 P).card : ℝ) / (4 * (P : ℝ)) ≤
      squareAdjustedReciprocalMass142 P := by
    calc
      _ = ∑ _p ∈ primeBand142 P, 1 / (4 * (P : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        unfold squareAdjustedReciprocalMass142
        apply Finset.sum_le_sum
        intro p hp
        have hI := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
        exact correctedReciprocal_term_lower142 hP2 hI.1 hI.2
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hquot := div_le_div_of_nonneg_right hcount
    (show (0 : ℝ) ≤ 4 * (P : ℝ) by positivity)
  have hid : ((P : ℝ) / (2 * Real.log (2 * P : ℝ))) / (4 * (P : ℝ)) =
      1 / (8 * Real.log (2 * P : ℝ)) := by
    field_simp [ne_of_gt hP0, ne_of_gt hLpos] <;> ring
  rw [hid] at hquot
  exact le_trans hquot hterms

/-- A ONE-SIDED signed-remainder estimate now suffices in every band above
max(a,c-b); there is no c<P^2 condition and no independent square-loss estimate.
The remainder premise is not proved here. -/
theorem sparseCount_from_signedRemainder142 {a b c P : ℕ}
    (hbc : b < c) (hP : 2 ≤ P) (haP : a < P) (hgapP : c - b < P)
    (hmain : 1 / (8 * Real.log (2 * P : ℝ)) ≤ squareAdjustedReciprocalMass142 P)
    (herr : -(((c - b : ℕ) : ℝ) / (16 * Real.log (2 * P : ℝ))) ≤
      sparseSignedRemainder142 b c P) :
    ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
      ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  have hid := sparseGoodCount_mainTerm_identity142 hbc haP hgapP
  have hh0 : (0 : ℝ) ≤ ((c - b : ℕ) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmain hh0
  have hL : 0 < Real.log (2 * P : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < 2 * P by omega))
  have harith : ((c - b : ℕ) : ℝ) * (1 / (8 * Real.log (2 * P : ℝ))) -
        ((c - b : ℕ) : ℝ) / (16 * Real.log (2 * P : ℝ)) =
      ((c - b : ℕ) : ℝ) / (16 * Real.log (2 * P : ℝ)) := by ring
  have hstrong : ((c - b : ℕ) : ℝ) / (16 * Real.log (2 * P : ℝ)) ≤
      ((sparseGoodPrimes127 a b c P).card : ℝ) := by
    linarith only [hid, hmul, herr, harith]
  have hweak : ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
      ((c - b : ℕ) : ℝ) / (16 * Real.log (2 * P : ℝ)) := by
    apply div_le_div_of_nonneg_left hh0 (by positivity)
    linarith
  exact le_trans hweak hstrong

/-- PNT discharges hmain in the preceding theorem uniformly over all large P.
What remains is precisely the displayed signed fluctuation estimate. -/
theorem sparseCount_from_PNT_and_signedRemainder142 (HP : PsiMediumPNT134) :
    ∃ N : ℕ, ∀ a b c P : ℕ,
      N ≤ P → b < c → a < P → c - b < P →
      -(((c - b : ℕ) : ℝ) / (16 * Real.log (2 * P : ℝ))) ≤
        sparseSignedRemainder142 b c P →
      ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
        ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  obtain ⟨N, hN2, hN⟩ := squareAdjustedReciprocalMass_from_PNT142 HP
  refine ⟨N, ?_⟩
  intro a b c P hP hbc haP hgapP herr
  exact sparseCount_from_signedRemainder142 hbc (le_trans hN2 hP)
    haP hgapP (hN P hP) herr

/-! The final theorem retains the original four honest inputs. The new sufficient
remainder criterion is NOT substituted as an equivalent input or silently proved. -/
theorem candidate_main_from_mediumPNT142 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs141) : MainStatement :=
  candidate_main_from_mediumPNT141 HP H

theorem positive_lower_density_from_mediumPNT142 (HP : PsiMediumPNT134)
    (H : RemainingNonPNTInputs141) : PositiveLowerDensity D6 :=
  positive_lower_density_from_mediumPNT141 HP H

-- Frozen historical output: #eval "ERDOS374 REPAIR 142: repaired adapters and exact prime-square deletion"
-- Frozen historical output: #print axioms backwardBad_translates_to_forward141
-- Frozen historical output: #print axioms harman_bad_density_from_forward141
-- Frozen historical output: #print axioms squareFiber_card141
-- Frozen historical output: #print axioms rootPolynomial_eval141
-- Frozen historical output: #print axioms rootPolynomial_natDegree141
-- Frozen historical output: #print axioms mappedRootPolynomial_natDegree141
-- Frozen historical output: #print axioms coarseOddCharacter_bound141
-- Frozen historical output: #print axioms linearProduct_coarse_bound141
-- Frozen historical output: #print axioms coarse_squareResidueRestriction141
-- Frozen historical output: #print axioms auxiliaryH2_arbitrary_constant141
-- Frozen historical output: #print axioms legalAnchorLargeL_from_coarse141
-- Frozen historical output: #print axioms candidate_main_from_mediumPNT141
-- Frozen historical output: #print axioms exists_interval_multiple_iff142
-- Frozen historical output: #print axioms falling_factorization_eq_unique_multiple142
-- Frozen historical output: #print axioms primeSquare_dvd_falling_iff_quotient142
-- Frozen historical output: #print axioms valuationOne_indicator_eq_floorDifference142
-- Frozen historical output: #print axioms sparseGoodCount_eq_squareCorrectedFloorSum142
-- Frozen historical output: #print axioms quotientRemainder_bounds142
-- Frozen historical output: #print axioms quotientIncrement_expansion142
-- Frozen historical output: #print axioms sparseGoodCount_mainTerm_identity142
-- Frozen historical output: #print axioms correctedReciprocal_term_lower142
-- Frozen historical output: #print axioms squareAdjustedReciprocalMass_from_PNT142
-- Frozen historical output: #print axioms sparseCount_from_signedRemainder142
-- Frozen historical output: #print axioms sparseCount_from_PNT_and_signedRemainder142
-- Frozen historical output: #print axioms candidate_main_from_mediumPNT142
-- Frozen historical output: #print axioms positive_lower_density_from_mediumPNT142
-- Frozen historical output: #check sparseGoodCount_eq_squareCorrectedFloorSum142
-- Frozen historical output: #check sparseCount_from_PNT_and_signedRemainder142
-- Frozen historical output: #check candidate_main_from_mediumPNT142
-- Frozen historical output: #print RemainingNonPNTInputs141
-- Frozen historical output: #eval "ERDOS374 REPAIR 142 END: locally UNCOMPILED; four analytic inputs remain"

end RemainingAnalytic142












end RemainingAnalytic115

end Erdos374

end

/-
APACHE-2.0 LICENSE FOR THE ADAPTED ImportedLargeSieve135 PORTION


                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/



/-!
# Smooth periodic cutoffs for the sparse-prime branch

Original proof scripts; NOT compiled in this preparation runtime.
This module has no PNT, Harman, sparse-count, or curve-count hypothesis.
The previous C^3 polynomial bump is NOT silently called C-infinity.
We instead use Mathlib's genuinely smooth transition and prove that taking
fractional parts is harmless because the underlying windows vanish near BOTH
ends of a fundamental interval.

IMPORTANT: `n : ℕ∞` includes the smooth order infinity, not the analytic order
omega (`⊤ : WithTop ℕ∞`). A nonzero compactly supported analytic bump does not exist.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace Erdos374.Smooth144

/-- A genuinely smooth bump, with an exact unit plateau on [-1/2,1/2]. -/
def bump (u : ℝ) : ℝ :=
  Real.smoothTransition ((4 / 3 : ℝ) * (1 - u ^ 2))

theorem bump_bounds (u : ℝ) : 0 ≤ bump u ∧ bump u ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem bump_zero_of_one_le_abs {u : ℝ} (hu : 1 ≤ |u|) : bump u = 0 := by
  have hs : 1 ≤ u ^ 2 := by
    have hh := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hu
    nlinarith only [hh, sq_abs u]
  unfold bump
  exact Real.smoothTransition.zero_of_nonpos (by nlinarith only [hs])

theorem bump_pos_support {u : ℝ} (hu : 0 < bump u) : |u| < 1 := by
  by_contra hn
  have hz := bump_zero_of_one_le_abs (le_of_not_gt hn)
  rw [hz] at hu
  exact (lt_irrefl (0 : ℝ)) hu

theorem bump_eq_one_on_core {u : ℝ} (hu : |u| ≤ (1 : ℝ) / 2) : bump u = 1 := by
  have hs : u ^ 2 ≤ (1 : ℝ) / 4 := by
    have hh := mul_self_le_mul_self (abs_nonneg u) hu
    nlinarith only [hh, sq_abs u]
  unfold bump
  exact Real.smoothTransition.eq_one_iff_one_le.mpr (by nlinarith only [hs])

theorem bump_contDiff {n : ℕ∞} : ContDiff ℝ n bump := by
  have hg : ContDiff ℝ n (fun u : ℝ => (4 / 3 : ℝ) * (1 - u ^ 2)) :=
    contDiff_const.mul (contDiff_const.sub (contDiff_id.pow 2))
  exact Real.smoothTransition.contDiff.comp hg

/-- Periodization by fractional part; the smoothness theorem below includes
an explicit boundary proof rather than treating `Int.fract` as smooth. -/
def periodize (f : ℝ → ℝ) (x : ℝ) : ℝ := f (Int.fract x)

theorem periodize_periodic (f : ℝ → ℝ) : Function.Periodic (periodize f) 1 := by
  intro x
  have hfloor : Int.floor (x + 1) = Int.floor x + 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · push_cast
      linarith only [Int.floor_le x]
    · push_cast
      linarith only [Int.lt_floor_add_one x]
  have hfract : Int.fract (x + 1) = Int.fract x := by
    unfold Int.fract
    rw [hfloor]
    push_cast
    ring
  exact congrArg f hfract

/-- A smooth function that vanishes on a neighborhood of both 0 and 1 has a
smooth fractional-part periodization. This is proved for every smooth order. -/
theorem contDiff_periodize {n : ℕ∞} {f : ℝ → ℝ}
    (hf : ContDiff ℝ n f) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hleft : ∀ u : ℝ, u ≤ ε → f u = 0)
    (hright : ∀ u : ℝ, 1 - ε ≤ u → f u = 0) :
    ContDiff ℝ n (periodize f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let k : ℤ := Int.floor x
  have hklo : (k : ℝ) ≤ x := Int.floor_le x
  have hkhi : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  by_cases hx : x = (k : ℝ)
  · have hnbhd : Set.Ioo ((k : ℝ) - ε) ((k : ℝ) + ε) ∈ nhds x := by
      rw [hx]
      exact Ioo_mem_nhds (by linarith) (by linarith)
    have heq : periodize f =ᶠ[nhds x] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hnbhd] with y hy
      obtain ⟨hylo, hyhi⟩ := hy
      by_cases hyk : (k : ℝ) ≤ y
      · have hfy : Int.floor y = k := by
          apply Int.floor_eq_iff.mpr
          exact ⟨hyk, by linarith only [hyhi, hε1]⟩
        have hfr : Int.fract y = y - (k : ℝ) := by
          simp only [Int.fract, hfy]
        change f (Int.fract y) = 0
        rw [hfr]
        exact hleft _ (by linarith only [hyhi])
      · have hyk' : y < (k : ℝ) := lt_of_not_ge hyk
        have hfy : Int.floor y = k - 1 := by
          apply Int.floor_eq_iff.mpr
          constructor
          · push_cast
            linarith only [hylo, hε1]
          · push_cast
            linarith only [hyk']
        have hfr : Int.fract y = y - ((k : ℝ) - 1) := by
          simp only [Int.fract, hfy, Int.cast_sub, Int.cast_one]
        change f (Int.fract y) = 0
        rw [hfr]
        exact hright _ (by linarith only [hylo])
    exact (contDiff_const : ContDiff ℝ n (fun _ : ℝ => (0 : ℝ))).contDiffAt.congr_of_eventuallyEq heq
  · have hklt : (k : ℝ) < x := lt_of_le_of_ne hklo (Ne.symm hx)
    have hnbhd : Set.Ioo (k : ℝ) ((k : ℝ) + 1) ∈ nhds x :=
      Ioo_mem_nhds hklt hkhi
    have heq : periodize f =ᶠ[nhds x] (fun y : ℝ => f (y - (k : ℝ))) := by
      filter_upwards [hnbhd] with y hy
      have hfy : Int.floor y = k := Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩
      simp only [periodize, Int.fract, hfy]
    have htranslated : ContDiff ℝ n (fun y : ℝ => f (y - (k : ℝ))) :=
      hf.comp (contDiff_id.sub contDiff_const)
    exact htranslated.contDiffAt.congr_of_eventuallyEq heq

/-- The first cutoff is supported strictly before the next integer. -/
def crossingWindow (δ u : ℝ) : ℝ := bump ((u - (1 - 3 * δ)) / δ)

theorem crossingWindow_bounds (δ u : ℝ) :
    0 ≤ crossingWindow δ u ∧ crossingWindow δ u ≤ 1 := bump_bounds _

theorem crossingWindow_contDiff {n : ℕ∞} (δ : ℝ) :
    ContDiff ℝ n (crossingWindow δ) := by
  have hg : ContDiff ℝ n (fun u : ℝ => (u - (1 - 3 * δ)) / δ) :=
    (contDiff_id.sub contDiff_const).div_const δ
  exact bump_contDiff.comp hg

theorem crossingWindow_pos_support {δ u : ℝ} (hδ : 0 < δ)
    (hw : 0 < crossingWindow δ u) : 1 - 4 * δ < u ∧ u < 1 - 2 * δ := by
  have hs := abs_lt.mp (bump_pos_support hw)
  have hl := (lt_div_iff₀ hδ).mp hs.1
  have hr := (div_lt_iff₀ hδ).mp hs.2
  constructor <;> linarith

theorem crossingWindow_core {δ u : ℝ} (hδ : 0 < δ)
    (hu : |u - (1 - 3 * δ)| ≤ δ / 2) : crossingWindow δ u = 1 := by
  apply bump_eq_one_on_core
  rw [abs_div, abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  nlinarith only [hu]

theorem crossingWindow_zero_edges {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) :
    (∀ u : ℝ, u ≤ δ → crossingWindow δ u = 0) ∧
    (∀ u : ℝ, 1 - δ ≤ u → crossingWindow δ u = 0) := by
  constructor
  · intro u hu
    apply le_antisymm _ (crossingWindow_bounds δ u).1
    apply le_of_not_gt
    intro hpos
    have hs := crossingWindow_pos_support hδ hpos
    linarith only [hu, hs.1, hδsmall]
  · intro u hu
    apply le_antisymm _ (crossingWindow_bounds δ u).1
    apply le_of_not_gt
    intro hpos
    have hs := crossingWindow_pos_support hδ hpos
    linarith only [hu, hs.2, hδ]

/-- Broader square-avoidance plateau: support (1/16,15/16), value one on [1/8,7/8].
The upper support endpoint is paired with h/p^2 < 1/16 in the arithmetic adapter. -/
def squareWindow (u : ℝ) : ℝ :=
  Real.smoothTransition (16 * u - 1) * Real.smoothTransition (15 - 16 * u)

theorem squareWindow_bounds (u : ℝ) : 0 ≤ squareWindow u ∧ squareWindow u ≤ 1 := by
  have hA0 := Real.smoothTransition.nonneg (16 * u - 1)
  have hA1 := Real.smoothTransition.le_one (16 * u - 1)
  have hB0 := Real.smoothTransition.nonneg (15 - 16 * u)
  have hB1 := Real.smoothTransition.le_one (15 - 16 * u)
  constructor
  · exact mul_nonneg hA0 hB0
  · change Real.smoothTransition (16 * u - 1) * Real.smoothTransition (15 - 16 * u) ≤ 1
    calc
      _ ≤ Real.smoothTransition (16 * u - 1) * 1 := mul_le_mul_of_nonneg_left hB1 hA0
      _ ≤ 1 := by simpa only [mul_one] using hA1

theorem squareWindow_zero_edges :
    (∀ u : ℝ, u ≤ 1 / 16 → squareWindow u = 0) ∧
    (∀ u : ℝ, 1 - 1 / 16 ≤ u → squareWindow u = 0) := by
  constructor
  · intro u hu
    unfold squareWindow
    rw [Real.smoothTransition.zero_of_nonpos (show 16 * u - 1 ≤ 0 by linarith)]
    exact zero_mul _
  · intro u hu
    unfold squareWindow
    rw [Real.smoothTransition.zero_of_nonpos (show 15 - 16 * u ≤ 0 by linarith)]
    exact mul_zero _

theorem squareWindow_pos_support {u : ℝ} (hu : 0 < squareWindow u) :
    (1 : ℝ) / 16 < u ∧ u < 15 / 16 := by
  constructor
  · by_contra hn
    rw [squareWindow_zero_edges.1 u (le_of_not_gt hn)] at hu
    exact (lt_irrefl (0 : ℝ)) hu
  · by_contra hn
    have hz := squareWindow_zero_edges.2 u (by linarith [le_of_not_gt hn])
    rw [hz] at hu
    exact (lt_irrefl (0 : ℝ)) hu

theorem squareWindow_eq_one_on_core {u : ℝ} (hlo : 1 / 8 ≤ u) (hhi : u ≤ 7 / 8) :
    squareWindow u = 1 := by
  unfold squareWindow
  rw [Real.smoothTransition.eq_one_iff_one_le.mpr (show 1 ≤ 16 * u - 1 by linarith),
    Real.smoothTransition.eq_one_iff_one_le.mpr (show 1 ≤ 15 - 16 * u by linarith)]
  exact one_mul 1

theorem squareWindow_contDiff {n : ℕ∞} : ContDiff ℝ n squareWindow := by
  have hA : ContDiff ℝ n (fun u : ℝ => Real.smoothTransition (16 * u - 1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hB : ContDiff ℝ n (fun u : ℝ => Real.smoothTransition (15 - 16 * u)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact hA.mul hB

def crossingPeriodic (δ : ℝ) : ℝ → ℝ := periodize (crossingWindow δ)
def squarePeriodic : ℝ → ℝ := periodize squareWindow

theorem crossingPeriodic_contDiff {n : ℕ∞} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) : ContDiff ℝ n (crossingPeriodic δ) := by
  have hedges := crossingWindow_zero_edges hδ hδsmall
  exact contDiff_periodize (crossingWindow_contDiff δ) hδ (by linarith)
    hedges.1 hedges.2

theorem squarePeriodic_contDiff {n : ℕ∞} : ContDiff ℝ n squarePeriodic := by
  exact contDiff_periodize squareWindow_contDiff (by norm_num : (0 : ℝ) < 1 / 16)
    (by norm_num) squareWindow_zero_edges.1 squareWindow_zero_edges.2

/-- The actual two-variable smooth periodic function used for reciprocal-prime sampling. -/
def test (δ : ℝ) (squareFreeBand : Bool) (z : ℝ × ℝ) : ℝ :=
  if squareFreeBand then crossingPeriodic δ z.1
  else crossingPeriodic δ z.1 * squarePeriodic z.2

theorem test_bounds (δ : ℝ) (q : Bool) (z : ℝ × ℝ) :
    0 ≤ test δ q z ∧ test δ q z ≤ 1 := by
  have hA := crossingWindow_bounds δ (Int.fract z.1)
  have hB := squareWindow_bounds (Int.fract z.2)
  cases q
  · change 0 ≤ crossingWindow δ (Int.fract z.1) * squareWindow (Int.fract z.2) ∧
      crossingWindow δ (Int.fract z.1) * squareWindow (Int.fract z.2) ≤ 1
    constructor
    · exact mul_nonneg hA.1 hB.1
    · nlinarith only [hA.1, hA.2, hB.1, hB.2,
        mul_le_mul_of_nonneg_left hB.2 hA.1]
  · exact hA

theorem test_contDiff {n : ℕ∞} {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (q : Bool) : ContDiff ℝ n (test δ q) := by
  have hA : ContDiff ℝ n (fun z : ℝ × ℝ => crossingPeriodic δ z.1) :=
    (crossingPeriodic_contDiff hδ hδsmall).comp contDiff_fst
  have hB : ContDiff ℝ n (fun z : ℝ × ℝ => squarePeriodic z.2) :=
    squarePeriodic_contDiff.comp contDiff_snd
  cases q
  · exact hA.mul hB
  · exact hA

theorem test_periodic_fst (δ : ℝ) (q : Bool) (x y : ℝ) :
    test δ q (x + 1, y) = test δ q (x, y) := by
  have hA := periodize_periodic (crossingWindow δ) x
  cases q
  · change periodize (crossingWindow δ) (x + 1) * squarePeriodic y =
      periodize (crossingWindow δ) x * squarePeriodic y
    rw [hA]
  · exact hA

theorem test_periodic_snd (δ : ℝ) (q : Bool) (x y : ℝ) :
    test δ q (x, y + 1) = test δ q (x, y) := by
  have hB := periodize_periodic squareWindow y
  cases q
  · change crossingPeriodic δ x * periodize squareWindow (y + 1) =
      crossingPeriodic δ x * periodize squareWindow y
    rw [hB]
  · rfl

/-- A numerical absorption step for the continuous lower-bound calculation.
The construction of the geometric intervals is proved in the accompanying
mathematical note, NOT assumed to be kernel-checked by this lemma. -/
theorem interval_error_budget {P δ J κ qscale V : ℝ}
    (hP : 2048 ≤ P) (hδ : 0 ≤ δ) (hqscale : 15 / 16 ≤ qscale)
    (hJ : P / 8 ≤ J) (hκ : κ ≤ qscale + 2)
    (hV : δ * (J / 4 - 2 * κ / qscale) ≤ V) :
    δ * P / 40 ≤ V := by
  have hqscalepos : 0 < qscale := by linarith only [hqscale]
  have hratio : 2 * κ / qscale ≤ 94 / 15 := by
    apply (div_le_iff₀ hqscalepos).mpr
    nlinarith only [hκ, hqscale]
  have hbase : P / 40 ≤ J / 4 - 2 * κ / qscale := by
    linarith only [hJ, hratio, hP]
  have hm := mul_le_mul_of_nonneg_left hbase hδ
  calc
    δ * P / 40 = δ * (P / 40) := by ring
    _ ≤ δ * (J / 4 - 2 * κ / qscale) := hm
    _ ≤ V := hV

#print axioms bump_contDiff
#print axioms contDiff_periodize
#print axioms crossingPeriodic_contDiff
#print axioms squarePeriodic_contDiff
#print axioms test_contDiff
#print axioms test_periodic_fst
#print axioms test_periodic_snd
#print axioms interval_error_budget
#check test_contDiff
#eval "SMOOTH CUTOFF 144 END: no prime-distribution theorem asserted"

end Erdos374.Smooth144
end



/-!
# Connect the smooth test to the original sparse valuation-one count

Original proof scripts, UNCOMPILED. This module depends on the frozen core,
not the unverified experimental Repair-143 extension. The prime-distribution
estimate and the continuous integral lower bound are NOT inserted as axioms.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Erdos374.SmoothSparse144
open Erdos374.RemainingAnalytic115.RemainingAnalytic127
open Erdos374.RemainingAnalytic115.RemainingAnalytic141
open Erdos374.RemainingAnalytic115.RemainingAnalytic142
open Erdos374.Smooth144

abbrev width (b c P : ℕ) : ℝ := ((c - b : ℕ) : ℝ) / (8 * (P : ℝ))

def firstWeight (b c P p : ℕ) : ℝ :=
  crossingWindow (width b c P) (quotientRemainder142 b p)

def squareWeight (b p : ℕ) : ℝ := squareWindow (quotientRemainder142 b (p ^ 2))

def weight (b c P p : ℕ) : ℝ :=
  if c < P ^ 2 then firstWeight b c P p
  else firstWeight b c P p * squareWeight b p

def score (b c P : ℕ) : ℝ := ∑ p ∈ primeBand142 P, weight b c P p

theorem weight_bounds (b c P p : ℕ) : 0 ≤ weight b c P p ∧ weight b c P p ≤ 1 := by
  have hA : 0 ≤ firstWeight b c P p ∧ firstWeight b c P p ≤ 1 := crossingWindow_bounds _ _
  have hB : 0 ≤ squareWeight b p ∧ squareWeight b p ≤ 1 := squareWindow_bounds _
  unfold weight
  split_ifs
  · exact hA
  · constructor
    · exact mul_nonneg hA.1 hB.1
    · have hh := mul_le_mul_of_nonneg_left hB.2 hA.1
      nlinarith only [hh, hA.2]

/-- Both quotient facts are obtained from the checked exact floor expansion. -/
theorem quotient_crosses {b c d : ℕ} (hbc : b ≤ c) (hd : 1 ≤ d)
    (hs : 1 ≤ ((c - b : ℕ) : ℝ) / (d : ℝ) + quotientRemainder142 b d) :
    b / d < c / d := by
  have hi := quotientIncrement_expansion142 hbc d
  have hr := (quotientRemainder_bounds142 c hd).2
  have hpos : (0 : ℝ) < ((c / d - b / d : ℕ) : ℝ) := by linarith only [hi, hr, hs]
  have hnat : 0 < c / d - b / d := by exact_mod_cast hpos
  omega

theorem quotient_does_not_cross {b c d : ℕ} (hbc : b ≤ c) (hd : 1 ≤ d)
    (hs : ((c - b : ℕ) : ℝ) / (d : ℝ) + quotientRemainder142 b d < 1) :
    c / d = b / d := by
  have hi := quotientIncrement_expansion142 hbc d
  have hr := (quotientRemainder_bounds142 c hd).1
  have hlt : ((c / d - b / d : ℕ) : ℝ) < 1 := by linarith only [hi, hr, hs]
  have hltN : c / d - b / d < 1 := by exact_mod_cast hlt
  have hmono : b / d ≤ c / d :=
    (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr
      (le_trans (Nat.div_mul_le_self b d) hbc)
  omega

theorem firstWeight_pos_divides {b c P p : ℕ}
    (hbc : b < c) (hP : 1 ≤ P) (hp : p.Prime) (hp2P : p ≤ 2 * P)
    (hw : 0 < firstWeight b c P p) : p ∣ falling (c - b) c := by
  have hhpos : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hδ : 0 < width b c P := by unfold width; positivity
  have hs := crossingWindow_pos_support hδ hw
  have hpup : (p : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hp2P
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hdiv : ((c - b : ℕ) : ℝ) / (2 * (P : ℝ)) ≤ ((c - b : ℕ) : ℝ) / (p : ℝ) :=
    div_le_div_of_nonneg_left hhpos.le hppos hpup
  have hid : 4 * width b c P = ((c - b : ℕ) : ℝ) / (2 * (P : ℝ)) := by unfold width; ring
  have hcross : 1 ≤ ((c - b : ℕ) : ℝ) / (p : ℝ) + quotientRemainder142 b p := by
    linarith only [hs.1, hdiv, hid]
  exact (prime_dvd_falling_iff_quotient141 hbc hp).mpr (quotient_crosses hbc.le hp.one_le hcross)

theorem squareWeight_pos_no_square {b c p : ℕ}
    (hbc : b < c) (hp : p.Prime) (hp16 : 16 ≤ p) (hgap : c - b < p)
    (hw : 0 < squareWeight b p) : ¬ p ^ 2 ∣ falling (c - b) c := by
  have hs := squareWindow_pos_support hw
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp16R : (16 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp16
  have hhR : ((c - b : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hgap
  have hprod := mul_le_mul_of_nonneg_left hp16R hp0.le
  have hsmall : ((c - b : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ) < (1 : ℝ) / 16 := by
    rw [Nat.cast_pow]
    apply (div_lt_iff₀ (pow_pos hp0 2)).mpr
    nlinarith only [hprod, hhR, hp0]
  have hno : c / (p ^ 2) = b / (p ^ 2) :=
    quotient_does_not_cross hbc.le (by nlinarith [hp.two_le])
      (by linarith only [hsmall, hs.2])
  intro hsq
  have hstrict := (primeSquare_dvd_falling_iff_quotient142 hbc hp hgap).mp hsq
  omega

/-- Positive smooth weight still certifies valuation exactly one, not merely divisibility. -/
theorem positive_weight_good {a b c P p : ℕ}
    (hbc : b < c) (hP16 : 16 ≤ P) (haP : a < P) (hgapP : c - b < P)
    (hpmem : p ∈ primeBand142 P) (hw : 0 < weight b c P p) :
    p ∈ sparseGoodPrimes127 a b c P := by
  have hp := (Finset.mem_filter.mp hpmem).2
  have hI := Finset.mem_Icc.mp (Finset.mem_filter.mp hpmem).1
  have hgap : c - b < p := lt_of_lt_of_le hgapP hI.1
  have hA0 : 0 ≤ firstWeight b c P p := (crossingWindow_bounds _ _).1
  have hB0 : 0 ≤ squareWeight b p := (squareWindow_bounds _).1
  have hfirst : 0 < firstWeight b c P p := by
    unfold weight at hw
    split_ifs at hw with hhigh
    · exact hw
    · rcases mul_pos_iff.mp hw with hpos | hneg
      · exact hpos.1
      · linarith only [hA0, hneg.1]
  have hd := firstWeight_pos_divides hbc (by omega) hp hI.2 hfirst
  have hsq : ¬ p ^ 2 ∣ falling (c - b) c := by
    by_cases hhigh : c < P ^ 2
    · have hPP : P ^ 2 ≤ p ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hI.1 hI.1
      have hc0 : c / (p ^ 2) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hhigh hPP)
      intro hh
      have hquot := (primeSquare_dvd_falling_iff_quotient142 hbc hp hgap).mp hh
      rw [hc0] at hquot
      exact (Nat.not_lt_zero _) hquot
    · have hmul : 0 < firstWeight b c P p * squareWeight b p := by simpa only [weight, if_neg hhigh] using hw
      have hsecond : 0 < squareWeight b p := by
        rcases mul_pos_iff.mp hmul with hpos | hneg
        · exact hpos.2
        · linarith only [hB0, hneg.2]
      exact squareWeight_pos_no_square hbc hp (le_trans hP16 hI.1) hgap hsecond
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hI, hp, lt_of_lt_of_le haP hI.1, hd, hsq⟩

theorem score_le_goodCount {a b c P : ℕ}
    (hbc : b < c) (hP16 : 16 ≤ P) (haP : a < P) (hgapP : c - b < P) :
    score b c P ≤ ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  classical
  have hfilter : (primeBand142 P).filter (fun p => p ∈ sparseGoodPrimes127 a b c P) =
      sparseGoodPrimes127 a b c P := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hh => hh.2
    · intro hh
      have hd := Finset.mem_filter.mp hh
      exact ⟨Finset.mem_filter.mpr ⟨hd.1, hd.2.1⟩, hh⟩
  calc
    _ ≤ ∑ p ∈ primeBand142 P, if p ∈ sparseGoodPrimes127 a b c P then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hg : p ∈ sparseGoodPrimes127 a b c P
      · simpa only [hg, ite_true] using (weight_bounds b c P p).2
      · rw [if_neg hg]
        apply le_of_not_gt
        intro hw
        exact hg (positive_weight_good hbc hP16 haP hgapP hp hw)
    _ = _ := by rw [← Finset.sum_filter, hfilter]; simp

theorem quotientRemainder_eq_fract (n : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    quotientRemainder142 n d = Int.fract ((n : ℝ) / (d : ℝ)) := by
  have hf : Int.floor ((n : ℝ) / (d : ℝ)) = ((n / d : ℕ) : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · simpa only [Int.cast_natCast] using
        Erdos374.RemainingAnalytic115.RemainingAnalytic124.natDiv_real_lower124 (X := n) (r := d) hd
    · simpa only [Int.cast_natCast] using
        Erdos374.RemainingAnalytic115.RemainingAnalytic124.natDiv_real_upper124 (X := n) (r := d) hd
  simp only [quotientRemainder142, Int.fract, hf, Int.cast_natCast]

def periodicTest (b c P : ℕ) : (ℝ × ℝ) → ℝ :=
  Smooth144.test (width b c P) (decide (c < P ^ 2))

theorem periodicTest_contDiff {n : ℕ∞} {b c P : ℕ}
    (hbc : b < c) (hgapP : c - b < P) : ContDiff ℝ n (periodicTest b c P) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hh0 : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
  have hδ : 0 < width b c P := by unfold width; positivity
  have hδsmall : width b c P ≤ 1 / 8 := by
    unfold width
    apply (div_le_iff₀ (show (0 : ℝ) < 8 * (P : ℝ) by positivity)).mpr
    have hhP : ((c - b : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast hgapP
    linarith only [hhP]
  exact test_contDiff hδ hδsmall _

theorem weight_eq_periodicTest (b c P : ℕ) {p : ℕ} (hp : p.Prime) :
    weight b c P p = periodicTest b c P ((b : ℝ) / (p : ℝ), (b : ℝ) / (p : ℝ) ^ 2) := by
  have hp2 : 1 ≤ p ^ 2 := by nlinarith [hp.two_le]
  by_cases hhigh : c < P ^ 2 <;>
    simp [weight, firstWeight, squareWeight, periodicTest, Smooth144.test,
      crossingPeriodic, squarePeriodic, periodize, hhigh,
      quotientRemainder_eq_fract b hp.one_le, quotientRemainder_eq_fract b hp2, Nat.cast_pow]

def referenceIntegral (b c P : ℕ) : ℝ :=
  ∫ t in (P : ℝ)..(2 * (P : ℝ)), periodicTest b c P ((b : ℝ) / t, (b : ℝ) / t ^ 2) / Real.log t

/-- Exact error-budget assembly; the two analytic inequalities are NOT proved
by the construction of the smooth test. The note proves the first on paper. -/
theorem count_of_integral_and_sampling {a b c P : ℕ}
    (hbc : b < c) (hP16 : 16 ≤ P) (haP : a < P) (hgapP : c - b < P)
    (hmain : ((c - b : ℕ) : ℝ) / (320 * Real.log (2 * P : ℝ)) ≤ referenceIntegral b c P)
    (herr : |score b c P - referenceIntegral b c P| ≤ ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ))) :
    ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤ ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  have hlow := neg_abs_le (score b c P - referenceIntegral b c P)
  have harith : ((c - b : ℕ) : ℝ) / (320 * Real.log (2 * P : ℝ)) =
      2 * (((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ))) := by ring
  have hscore : ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤ score b c P := by
    linarith only [hmain, herr, hlow, harith]
  exact le_trans hscore (score_le_goodCount hbc hP16 haP hgapP)

#print axioms positive_weight_good
#print axioms score_le_goodCount
#print axioms periodicTest_contDiff
#print axioms weight_eq_periodicTest
#print axioms count_of_integral_and_sampling
#eval "SMOOTH SPARSE 144 END: PNT, Harman, sparse sampling and curve inputs not constructed here"

end Erdos374.SmoothSparse144
end



/-!
# Mathlib-native Vaughan decomposition and coefficient support

Original integration code for Working Update 145. NOT LOCALLY COMPILED.
This file uses the actual Mathlib identities mu * zeta = 1 and zeta * Lambda = log.
All multiplication of ArithmeticFunction objects below is DIRICHLET CONVOLUTION.
No prime distribution, short-interval theorem, RH, or project analytic hypothesis
is an input. The identities are a finite ingredient of the missing sampling proof,
not a replacement for the exponential-sum estimates needed after decomposition.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators

namespace Erdos374.Vaughan145

abbrev muR : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
abbrev zetaR : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
abbrev lam : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt

/-- Retain the terms at indices at most U; the index zero remains zero. -/
def low (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

def high (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := f - low U f

@[simp] theorem low_apply (U n : ℕ) (f : ArithmeticFunction ℝ) :
    low U f n = if n ≤ U then f n else 0 := rfl

/-- Evaluation of subtraction, obtained from the existing additive operations. -/
theorem arithmetic_sub_apply148 (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    ← sub_eq_add_neg]

@[simp] theorem high_apply (U n : ℕ) (f : ArithmeticFunction ℝ) :
    high U f n = if U < n then f n else 0 := by
  rw [high, arithmetic_sub_apply148, low_apply]
  by_cases hn : n ≤ U
  · simp only [hn, not_lt.mpr hn, ite_true, ite_false, sub_self]
  · simp only [hn, lt_of_not_ge hn, ite_true, ite_false, sub_zero]

theorem high_zero_of_le {U n : ℕ} (f : ArithmeticFunction ℝ) (hn : n ≤ U) :
    high U f n = 0 := by simp [not_lt.mpr hn]

theorem low_zero_of_lt {U n : ℕ} (f : ArithmeticFunction ℝ) (hn : U < n) :
    low U f n = 0 := by simp [not_le.mpr hn]

theorem low_add_high (U : ℕ) (f : ArithmeticFunction ℝ) : low U f + high U f = f := by
  unfold high
  abel

/-- Pure algebra, valid in any commutative ring. The inverse condition is explicit. -/
theorem algebraic_identity {R : Type*} [CommRing R]
    (m z ell a b : R) (hmz : m * z = 1) :
    ell = a * (z * ell) + b - (a * b) * z + (m - a) * (z * (ell - b)) := by
  calc
    ell = (m * z) * ell + b - (m * z) * b := by rw [hmz]; ring
    _ = a * (z * ell) + b - (a * b) * z + (m - a) * (z * (ell - b)) := by ring

/-- Small-small coefficient of the second Type-I term. -/
def alpha (U V : ℕ) : ArithmeticFunction ℝ := low U muR * low V lam

/-- Divisor sum of the large von Mangoldt terms, the second Type-II coefficient. -/
def beta (V : ℕ) : ArithmeticFunction ℝ := zetaR * high V lam

/-- Vaughan's exact identity for the actual Mathlib von Mangoldt function. -/
theorem vaughan_identity (U V : ℕ) :
    lam = low U muR * ArithmeticFunction.log + low V lam - alpha U V * zetaR +
      high U muR * beta V := by
  have hmu : muR * zetaR = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hlog : zetaR * lam = ArithmeticFunction.log :=
    ArithmeticFunction.zeta_mul_vonMangoldt
  have h := algebraic_identity muR zetaR lam (low U muR) (low V lam) hmu
  rw [hlog] at h
  exact h

theorem low_moebius_abs_le_one (U n : ℕ) : |low U muR n| ≤ 1 := by
  by_cases hn : n ≤ U
  · rw [low_apply, if_pos hn]
    change |(ArithmeticFunction.moebius n : ℝ)| ≤ 1
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  · simp [hn]

theorem high_moebius_abs_le_one (U n : ℕ) : |high U muR n| ≤ 1 := by
  by_cases hn : U < n
  · rw [high_apply, if_pos hn]
    change |(ArithmeticFunction.moebius n : ℝ)| ≤ 1
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  · simp [hn]

/-- beta is the actual divisor sum, not an arbitrary coefficient bounded by log. -/
theorem beta_eq_divisor_sum (V n : ℕ) :
    beta V n = ∑ d ∈ n.divisors, if V < d then lam d else 0 := by
  unfold beta
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  simp only [high_apply]

theorem beta_bounds (V n : ℕ) : 0 ≤ beta V n ∧ beta V n ≤ Real.log (n : ℝ) := by
  rw [beta_eq_divisor_sum]
  have hp : ∀ d : ℕ, 0 ≤ lam d := fun _ => ArithmeticFunction.vonMangoldt_nonneg
  constructor
  · apply Finset.sum_nonneg
    intro d hd
    split_ifs
    · exact hp d
    · exact le_rfl
  · calc
      (∑ d ∈ n.divisors, if V < d then lam d else 0) ≤ ∑ d ∈ n.divisors, lam d := by
        apply Finset.sum_le_sum
        intro d hd
        split_ifs
        · exact le_rfl
        · exact hp d
      _ = Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_sum

theorem beta_zero_of_le {V n : ℕ} (hn : n ≤ V) : beta V n = 0 := by
  rw [beta_eq_divisor_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hdV : d ≤ V := le_trans (Nat.divisor_le hd) hn
  simp only [not_lt.mpr hdV, ite_false]

/-- The small-small coefficient has finite support at n <= U*V. -/
theorem alpha_zero_above_product {U V n : ℕ} (hn : U * V < n) : alpha U V n = 0 := by
  unfold alpha
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hmul : d.1 * d.2 = n := (Nat.mem_divisorsAntidiagonal.mp hd).1
  by_cases hU : d.1 ≤ U
  · by_cases hV : d.2 ≤ V
    · have hh := Nat.mul_le_mul hU hV
      rw [hmul] at hh
      exact False.elim ((not_le.mpr hn) hh)
    · rw [low_zero_of_lt lam (lt_of_not_ge hV), mul_zero]
  · rw [low_zero_of_lt muR (lt_of_not_ge hU), zero_mul]

/-- The large-large coefficient has no contribution below the product cutoff. -/
theorem typeII_zero_below_product {U V n : ℕ} (hn : n ≤ U * V) :
    (high U muR * beta V) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hmul : d.1 * d.2 = n := (Nat.mem_divisorsAntidiagonal.mp hd).1
  by_cases hU : d.1 ≤ U
  · rw [high_zero_of_le muR hU, zero_mul]
  · by_cases hV : d.2 ≤ V
    · rw [beta_zero_of_le hV, mul_zero]
    · have hl := Nat.mul_le_mul (Nat.succ_le_of_lt (lt_of_not_ge hU))
        (Nat.succ_le_of_lt (lt_of_not_ge hV))
      rw [hmul] at hl
      have hfalse : False := by nlinarith only [hl, hn, Nat.zero_le U, Nat.zero_le V]
      exact hfalse.elim

/-- General complex phase weights, with no modulus or periodicity assumption. -/
def phaseSum (S : Finset ℕ) (w : ℕ → ℂ) (f : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ S, (f n : ℂ) * w n

theorem phaseSum_add (S : Finset ℕ) (w : ℕ → ℂ) (f g : ArithmeticFunction ℝ) :
    phaseSum S w (f + g) = phaseSum S w f + phaseSum S w g := by
  simp only [phaseSum, ArithmeticFunction.add_apply, Complex.ofReal_add,
    add_mul, Finset.sum_add_distrib]

theorem phaseSum_sub (S : Finset ℕ) (w : ℕ → ℂ) (f g : ArithmeticFunction ℝ) :
    phaseSum S w (f - g) = phaseSum S w f - phaseSum S w g := by
  simp only [phaseSum, arithmetic_sub_apply148, Complex.ofReal_sub,
    sub_mul, Finset.sum_sub_distrib]

/-- Exact four-term weighted decomposition; this is not a cancellation estimate. -/
theorem phaseSum_vaughan (U V : ℕ) (S : Finset ℕ) (w : ℕ → ℂ) :
    phaseSum S w lam =
      phaseSum S w (low U muR * ArithmeticFunction.log) + phaseSum S w (low V lam) -
      phaseSum S w (alpha U V * zetaR) + phaseSum S w (high U muR * beta V) := by
  have h := congrArg (phaseSum S w) (vaughan_identity U V)
  simpa only [phaseSum_add, phaseSum_sub] using h

/-- Above V the short von Mangoldt term vanishes exactly. -/
theorem phaseSum_vaughan_above (U V : ℕ) (S : Finset ℕ) (w : ℕ → ℂ)
    (hS : ∀ n ∈ S, V < n) :
    phaseSum S w lam =
      phaseSum S w (low U muR * ArithmeticFunction.log) -
      phaseSum S w (alpha U V * zetaR) + phaseSum S w (high U muR * beta V) := by
  have hzero : phaseSum S w (low V lam) = 0 := by
    unfold phaseSum
    apply Finset.sum_eq_zero
    intro n hn
    rw [low_zero_of_lt lam (hS n hn)]
    simp
  rw [phaseSum_vaughan, hzero, add_zero]

#print axioms vaughan_identity
#print axioms beta_bounds
#print axioms alpha_zero_above_product
#print axioms typeII_zero_below_product
#print axioms phaseSum_vaughan_above
#eval "VAUGHAN 145 END: finite identities only; no prime-sampling bound proved"

end Erdos374.Vaughan145
end



/-!
# Explicit scalar calculus for Working Update 148

These proofs repair function/instance elaboration in the uploaded 147 log.
They are new, locally UNCOMPILED scripts. All conclusions are ordinary real
HasDerivAt statements, with all nonzero denominator conditions retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Erdos374.ScalarCalculus148

/-- Real reciprocal differentiation with the function and derivative typed first. -/
theorem const_div_hasDerivAt (B : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => B / y) (-B / x ^ 2) x := by
  have hraw : HasDerivAt (fun y : ℝ => B / y)
      ((0 * x - B * 1) / x ^ 2) x := by
    with_unfolding_all
      exact (hasDerivAt_const x B).fun_div (hasDerivAt_id' x) hx
  simpa only [zero_mul, mul_one, zero_sub] using hraw

/-- An exact positive-power reciprocal derivative. Arithmetic is confined to
    the derivative value, never sent to a function-equality or instance goal. -/
theorem const_div_pow_hasDerivAt (a x : ℝ) (n : ℕ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => a / y ^ (n + 1))
      (-((n + 1 : ℕ) : ℝ) * a / x ^ (n + 2)) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * x ^ n) x := by
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (n + 1) x
  have hraw : HasDerivAt (fun y : ℝ => a / y ^ (n + 1))
      ((0 * x ^ (n + 1) - a * (((n + 1 : ℕ) : ℝ) * x ^ n)) /
        (x ^ (n + 1)) ^ 2) x := by
    with_unfolding_all
      exact (hasDerivAt_const x a).fun_div hpow (pow_ne_zero (n + 1) hx)
  apply hraw.congr_deriv
  simp only [zero_mul, zero_sub, pow_succ]
  field_simp [hx, pow_ne_zero n hx] <;> ring

/-- The other scalar factor used in the integration-by-parts calculation. -/
theorem neg_square_div_hasDerivAt (B x : ℝ) :
    HasDerivAt (fun y : ℝ => -(y ^ 2 / B)) (-2 * x / B) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa only [show (2 : ℕ) - 1 = 1 by decide, Nat.cast_ofNat, pow_one]
      using hasDerivAt_pow 2 x
  have hraw : HasDerivAt (fun y : ℝ => -(y ^ 2 / B)) (-(2 * x / B)) x := by
    with_unfolding_all exact (hpow.div_const B).neg
  apply hraw.congr_deriv
  ring

#print axioms const_div_hasDerivAt
#print axioms const_div_pow_hasDerivAt
#print axioms neg_square_div_hasDerivAt
#eval "SCALAR CALCULUS 148 END: local repairs, no analytic inputs"

end Erdos374.ScalarCalculus148



/-!
# Positive periodic averaging and the high-band reference integral

Original proof scripts for Working Update 145; NOT LOCALLY COMPILED.
The imported project module uses the original factorial/valuation definitions.
No prime-distribution hypothesis occurs in the theorems of this module.
The low-band two-coordinate integral still needs its finite interval cover;
these results do not assert the missing prime-sampling estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.PeriodicAveraging145

/-- A nonnegative continuous periodic function loses at most ONE period on any
interval. The complete periods start at a, not at the next integer. -/
theorem periodic_integral_lower {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (hf0 : ∀ x : ℝ, 0 ≤ f x)
    {δ a b : ℝ} (hδ : 0 ≤ δ) (hm : δ ≤ ∫ x in (0 : ℝ)..1, f x)
    (hab : a ≤ b) : δ * (b - a - 1) ≤ ∫ x in a..b, f x := by
  let n : ℕ := ⌊b - a⌋₊
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnle : (n : ℝ) ≤ b - a := Nat.floor_le (by linarith only [hab])
  have hnhi : b - a < (n : ℝ) + 1 := Nat.lt_floor_add_one (b - a)
  have hblock : (∫ x in a..a + (n : ℝ), f x) =
      (n : ℝ) * (∫ x in (0 : ℝ)..1, f x) := by
    have hh := hp.intervalIntegral_add_zsmul_eq (n : ℤ) a
      (fun s t => hf.intervalIntegrable s t)
    rw [hp.intervalIntegral_add_eq a 0] at hh
    simpa only [zsmul_eq_mul, Int.cast_natCast, zero_add, mul_one] using hh
  have hrem : 0 ≤ ∫ x in a + (n : ℝ)..b, f x :=
    intervalIntegral.integral_nonneg_of_forall (by linarith only [hnle]) hf0
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a (a + (n : ℝ)))
    (hf.intervalIntegrable (a + (n : ℝ)) b)
  have hlen : δ * (b - a - 1) ≤ δ * (n : ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith only [hnhi]) hδ
  have hmean := mul_le_mul_of_nonneg_left hm hn0
  calc
    δ * (b - a - 1) ≤ δ * (n : ℝ) := hlen
    _ = (n : ℝ) * δ := mul_comm _ _
    _ ≤ (n : ℝ) * (∫ x in (0 : ℝ)..1, f x) := hmean
    _ = ∫ x in a..a + (n : ℝ), f x := hblock.symm
    _ ≤ ∫ x in a..b, f x := by linarith only [hrem, hadd]

/-- The smooth crossing window has a unit plateau of length delta, inside a
fundamental interval. Its mean is therefore at least delta. -/
theorem crossing_mean_lower {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) :
    δ ≤ ∫ x in (0 : ℝ)..1, Smooth144.crossingPeriodic δ x := by
  let a : ℝ := 1 - 3 * δ - δ / 2
  let b : ℝ := 1 - 3 * δ + δ / 2
  have ha0 : 0 ≤ a := by dsimp [a]; linarith only [hδsmall]
  have hab : a ≤ b := by dsimp [a, b]; linarith only [hδ]
  have hb1 : b < 1 := by dsimp [b]; linarith only [hδ]
  have hf : Continuous (Smooth144.crossingPeriodic δ) :=
    (Smooth144.crossingPeriodic_contDiff (n := 0) hδ hδsmall).continuous
  have hf0 : ∀ x : ℝ, 0 ≤ Smooth144.crossingPeriodic δ x := fun x =>
    (Smooth144.crossingWindow_bounds δ (Int.fract x)).1
  have hone : ∀ x ∈ Icc a b, Smooth144.crossingPeriodic δ x = 1 := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans ha0 hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hb1
    have hfloor : Int.floor x = 0 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · simpa only [Int.cast_zero] using hx0
      · simpa only [Int.cast_zero, zero_add] using hx1
    have hfract : Int.fract x = x := by simp only [Int.fract, hfloor, Int.cast_zero, sub_zero]
    change Smooth144.crossingWindow δ (Int.fract x) = 1
    rw [hfract]
    apply Smooth144.crossingWindow_core hδ
    apply abs_le.mpr
    dsimp [a, b] at hx
    constructor <;> linarith only [hx.1, hx.2]
  have hsmallIntegral : (∫ x in a..b, Smooth144.crossingPeriodic δ x) = δ := by
    calc
      _ = ∫ _x in a..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hab] at hx
        exact hone x hx
      _ = δ := by simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]; dsimp [a, b]; ring
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) ha0 hab hb1.le
    (Filter.Eventually.of_forall hf0) (hf.intervalIntegrable 0 1)
  rw [hsmallIntegral] at hmono
  exact hmono

/-- The project window inherits the one-period loss bound, uniformly in its width. -/
theorem crossing_interval_lower {δ a b : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (hab : a ≤ b) : δ * (b - a - 1) ≤ ∫ x in a..b, Smooth144.crossingPeriodic δ x := by
  exact periodic_integral_lower
    (Smooth144.crossingPeriodic_contDiff (n := 0) hδ hδsmall).continuous
    (Smooth144.periodize_periodic (Smooth144.crossingWindow δ))
    (fun x => (Smooth144.crossingWindow_bounds δ (Int.fract x)).1)
    hδ.le (crossing_mean_lower hδ hδsmall) hab

/-- The Jacobian identity for v -> B/v includes the reversed endpoint order. -/
theorem reciprocal_jacobian_identity {f : ℝ → ℝ} (hf : Continuous f)
    {B s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    (∫ v in s..t, f (B / v) * (B / v ^ 2)) = ∫ u in B / t..B / s, f u := by
  have hx0 : ∀ x ∈ Set.uIcc s t, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hst] at hx
    exact ne_of_gt (lt_of_lt_of_le hs hx.1)
  have hd : ∀ x ∈ Set.uIcc s t,
      HasDerivAt (fun v : ℝ => B / v) (-B / x ^ 2) x := by
    intro x hx
    exact ScalarCalculus148.const_div_hasDerivAt B (hx0 x hx)
  have hc : ContinuousOn (fun x : ℝ => -B / x ^ 2) (Set.uIcc s t) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hx0 x hx))
  have hh := intervalIntegral.integral_comp_mul_deriv hd hc hf
  simp only [Function.comp_apply, neg_div, mul_neg, intervalIntegral.integral_neg] at hh
  rw [intervalIntegral.integral_symm (B / t) (B / s)] at hh
  exact neg_injective hh

/-- Quantitative reciprocal averaging. The endpoint error is P^2/B, improving
on the two-period error in the previous informal note. -/
theorem reciprocal_interval_lower {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (hf0 : ∀ x : ℝ, 0 ≤ f x)
    {δ P B s t : ℝ} (hδ : 0 ≤ δ) (hm : δ ≤ ∫ x in (0 : ℝ)..1, f x)
    (hP : 0 < P) (hB : 0 < B) (hPs : P ≤ s) (hst : s ≤ t) (htP : t ≤ 2 * P) :
    δ * ((t - s) / 4 - P ^ 2 / B) ≤ ∫ v in s..t, f (B / v) := by
  have hs : 0 < s := lt_of_lt_of_le hP hPs
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hP2 : 0 < P ^ 2 := pow_pos hP 2
  have hrec : ContinuousOn (fun v : ℝ => B / v) (Icc s t) :=
    continuousOn_const.div continuousOn_id
      (fun v hv => ne_of_gt (lt_of_lt_of_le hs hv.1))
  have hfc : ContinuousOn (fun v : ℝ => f (B / v)) (Icc s t) := hf.comp_continuousOn hrec
  have hjac : ContinuousOn (fun v : ℝ => B / v ^ 2) (Icc s t) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun v hv => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hs hv.1)))
  have hweighted := intervalIntegral.integral_mono_on (μ := volume) hst
    ((hfc.mul hjac).intervalIntegrable_of_Icc hst)
    ((continuousOn_const.mul hfc).intervalIntegrable_of_Icc hst)
    (show ∀ v ∈ Icc s t, f (B / v) * (B / v ^ 2) ≤ (B / P ^ 2) * f (B / v) by
      intro v hv
      have hPv : P ≤ v := le_trans hPs hv.1
      have hpow : P ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hP.le hPv 2
      have hdiv : B / v ^ 2 ≤ B / P ^ 2 := div_le_div_of_nonneg_left hB.le hP2 hpow
      have hh := mul_le_mul_of_nonneg_left hdiv (hf0 (B / v))
      simpa only [mul_comm (f (B / v)) (B / P ^ 2)] using hh)
  simp only [Pi.mul_apply] at hweighted
  rw [reciprocal_jacobian_identity hf hs hst, intervalIntegral.integral_const_mul] at hweighted
  have hurange : B / t ≤ B / s := div_le_div_of_nonneg_left hB.le hs hst
  have hmean := periodic_integral_lower hf hp hf0 hδ hm hurange
  have hbudget : δ * (B / s - B / t - 1) ≤ (B / P ^ 2) * (∫ v in s..t, f (B / v)) :=
    le_trans hmean hweighted
  have hstprod : s * t ≤ 4 * P ^ 2 := by
    have hh := mul_le_mul (le_trans hst htP) htP ht.le (show 0 ≤ 2 * P by positivity)
    nlinarith only [hh]
  have hdiff : B * (t - s) / (4 * P ^ 2) ≤ B / s - B / t := by
    have hid : B / s - B / t = B * (t - s) / (s * t) := by
      field_simp [ne_of_gt hs, ne_of_gt ht] <;> ring
    rw [hid]
    exact div_le_div_of_nonneg_left (mul_nonneg hB.le (sub_nonneg.mpr hst))
      (mul_pos hs ht) hstprod
  have hlower := mul_le_mul_of_nonneg_left (sub_le_sub_right hdiff 1) hδ
  have hid : (B / P ^ 2) * (δ * ((t - s) / 4 - P ^ 2 / B)) =
      δ * (B * (t - s) / (4 * P ^ 2) - 1) := by
    field_simp [ne_of_gt hP, ne_of_gt hB] <;> ring
  rw [← hid] at hlower
  exact le_of_mul_le_mul_left (le_trans hlower hbudget) (div_pos hB hP2)

/-- A positive logarithmic weight can be replaced from below by its value at 2P. -/
theorem logarithmic_weight_lower {g : ℝ → ℝ} {P : ℝ} (hP : 1 < P)
    (hg : ContinuousOn g (Icc P (2 * P))) (hg0 : ∀ v ∈ Icc P (2 * P), 0 ≤ g v) :
    (∫ v in P..2 * P, g v) / Real.log (2 * P) ≤ ∫ v in P..2 * P, g v / Real.log v := by
  have hP0 : 0 < P := lt_trans (by norm_num) hP
  have hab : P ≤ 2 * P := by linarith only [hP0]
  have hlog : ContinuousOn Real.log (Icc P (2 * P)) := by
    intro v hv
    exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le hP0 hv.1))).continuousWithinAt
  have hlogpos : ∀ v ∈ Icc P (2 * P), 0 < Real.log v := by
    intro v hv
    exact Real.log_pos (lt_of_lt_of_le hP hv.1)
  have hquot := hg.div hlog (fun v hv => ne_of_gt (hlogpos v hv))
  have hfixed := hg.div_const (Real.log (2 * P))
  have hcmp := intervalIntegral.integral_mono_on (μ := volume) hab
    (hfixed.intervalIntegrable_of_Icc hab) (hquot.intervalIntegrable_of_Icc hab)
    (show ∀ v ∈ Icc P (2 * P), g v / Real.log (2 * P) ≤ g v / Real.log v by
      intro v hv
      exact div_le_div_of_nonneg_left (hg0 v hv) (hlogpos v hv)
        (Real.log_le_log (lt_of_lt_of_le hP0 hv.1) hv.2))
  simpa only [Pi.div_apply, intervalIntegral.integral_div] using hcmp

/-- The one-coordinate reciprocal integral has a positive lower bound without
any prime-sampling input. -/
theorem reciprocal_log_integral_lower {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (hf0 : ∀ x : ℝ, 0 ≤ f x)
    {δ P B : ℝ} (hδ : 0 ≤ δ) (hm : δ ≤ ∫ x in (0 : ℝ)..1, f x)
    (hP : 1 < P) (hB : 0 < B) (hscale : 16 * P ≤ B) :
    δ * P / (8 * Real.log (2 * P)) ≤ ∫ v in P..2 * P, f (B / v) / Real.log v := by
  have hP0 : 0 < P := lt_trans (by norm_num) hP
  have hrec := reciprocal_interval_lower hf hp hf0 hδ hm hP0 hB
    le_rfl (show P ≤ 2 * P by linarith only [hP0]) le_rfl
  have hsmall : P ^ 2 / B ≤ P / 16 := by
    apply (div_le_iff₀ hB).mpr
    have hh := mul_le_mul_of_nonneg_left hscale hP0.le
    nlinarith only [hh]
  have hscaleδ := mul_le_mul_of_nonneg_left hsmall hδ
  have hJ : δ * P / 8 ≤ ∫ v in P..2 * P, f (B / v) := by
    have hδP : 0 ≤ δ * P := mul_nonneg hδ hP0.le
    nlinarith only [hrec, hscaleδ, hδP]
  have hg : ContinuousOn (fun v : ℝ => f (B / v)) (Icc P (2 * P)) :=
    hf.comp_continuousOn (continuousOn_const.div continuousOn_id
      (fun v hv => ne_of_gt (lt_of_lt_of_le hP0 hv.1)))
  have hLpos : 0 < Real.log (2 * P) := Real.log_pos (by linarith only [hP])
  have hdivide := div_le_div_of_nonneg_right hJ hLpos.le
  have hlog := logarithmic_weight_lower hP hg (fun v _hv => hf0 (B / v))
  calc
    δ * P / (8 * Real.log (2 * P)) = (δ * P / 8) / Real.log (2 * P) := by ring
    _ ≤ (∫ v in P..2 * P, f (B / v)) / Real.log (2 * P) := hdivide
    _ ≤ _ := hlog

/-- Actual reference-integral lower bound in the square-free high-band branch.
No PNT, Harman, curve theorem, or sampling bound is assumed. The bound is stronger
than the project's 1/320 target, but covers only c < P^2. -/
theorem highBand_referenceIntegral_lower {b c P : ℕ}
    (hP : 2 ≤ P) (hbc : b < c) (hgap : c - b < P)
    (hscale : 16 * P ≤ b) (hhigh : c < P ^ 2) :
    ((c - b : ℕ) : ℝ) / (64 * Real.log (2 * (P : ℝ))) ≤
      SmoothSparse144.referenceIntegral b c P := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hP1 : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
  have hB0 : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (show 0 < b by nlinarith only [hscale, hP])
  have hδ : 0 < SmoothSparse144.width b c P := by
    unfold SmoothSparse144.width
    have hh : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
    positivity
  have hδsmall : SmoothSparse144.width b c P ≤ 1 / 8 := by
    unfold SmoothSparse144.width
    apply (div_le_iff₀ (show (0 : ℝ) < 8 * (P : ℝ) by positivity)).mpr
    have hh : ((c - b : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast hgap
    linarith only [hh]
  have hf := (Smooth144.crossingPeriodic_contDiff (n := 0) hδ hδsmall).continuous
  have hp := Smooth144.periodize_periodic (Smooth144.crossingWindow (SmoothSparse144.width b c P))
  have hmain := reciprocal_log_integral_lower hf hp
    (fun x => (Smooth144.crossingWindow_bounds (SmoothSparse144.width b c P) (Int.fract x)).1)
    hδ.le (crossing_mean_lower hδ hδsmall) hP1 hB0 (by exact_mod_cast hscale)
  have hid : SmoothSparse144.width b c P * (P : ℝ) / (8 * Real.log (2 * (P : ℝ))) =
      ((c - b : ℕ) : ℝ) / (64 * Real.log (2 * (P : ℝ))) := by
    unfold SmoothSparse144.width
    have hL : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by linarith only [hP1])
    field_simp [ne_of_gt hP0, ne_of_gt hL] <;> ring
  rw [hid] at hmain
  simpa [SmoothSparse144.referenceIntegral, SmoothSparse144.periodicTest,
    Smooth144.test, hhigh] using hmain

#print axioms periodic_integral_lower
#print axioms crossing_mean_lower
#print axioms crossing_interval_lower
#print axioms reciprocal_jacobian_identity
#print axioms reciprocal_interval_lower
#print axioms logarithmic_weight_lower
#print axioms reciprocal_log_integral_lower
#print axioms highBand_referenceIntegral_lower
#eval "PERIODIC AVERAGING 145 END: high-band continuous bound; sampling and low-band cover remain"

end Erdos374.PeriodicAveraging145
end



/-!
# Periodic primitives and two reciprocal coordinates

Working Update 146. Original proof scripts, NOT COMPILED in this runtime.
No prime-distribution assumption occurs in this file. The primitive is constructed
from the actual periodic function; its bound is not supplied as an external field.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.PeriodicPrimitive146

def mean (f : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, f x

def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x, f t) - mean f * x

theorem mean_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) hf0

/-- The final fractional period contributes at most one whole mean. -/
theorem periodic_integral_upper {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (hf0 : ∀ x, 0 ≤ f x)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x) ≤ mean f * (b - a + 1) := by
  let n : ℕ := ⌊b - a⌋₊ + 1
  have hfloor : (⌊b - a⌋₊ : ℝ) ≤ b - a := Nat.floor_le (sub_nonneg.mpr hab)
  have hlast : b - a < (⌊b - a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (b - a)
  have hbn : b ≤ a + (n : ℝ) := by
    dsimp [n]
    push_cast
    linarith only [hlast]
  have hn : (n : ℝ) ≤ b - a + 1 := by
    dsimp [n]
    push_cast
    linarith only [hfloor]
  have hblock : (∫ x in a..a + (n : ℝ), f x) = (n : ℝ) * mean f := by
    have hh := hp.intervalIntegral_add_zsmul_eq (n : ℤ) a
      (fun s t => hf.intervalIntegrable s t)
    rw [hp.intervalIntegral_add_eq a 0] at hh
    simpa only [mean, zsmul_eq_mul, Int.cast_natCast, zero_add, mul_one] using hh
  have hrem : 0 ≤ ∫ x in b..a + (n : ℝ), f x :=
    intervalIntegral.integral_nonneg_of_forall hbn hf0
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a b) (hf.intervalIntegrable b (a + (n : ℝ)))
  have hmu := mean_nonneg hf0
  calc
    (∫ x in a..b, f x) ≤ ∫ x in a..a + (n : ℝ), f x := by linarith only [hadd, hrem]
    _ = (n : ℝ) * mean f := hblock
    _ ≤ (b - a + 1) * mean f := mul_le_mul_of_nonneg_right hn hmu
    _ = mean f * (b - a + 1) := mul_comm _ _

/-- Apply periodic UPPER averaging to 1-g, not a wasteful lower estimate to g. -/
theorem dense_periodic_integral_lower {g : ℝ → ℝ} (hg : Continuous g)
    (hp : Function.Periodic g 1) (hg1 : ∀ x, g x ≤ 1)
    (hm : (3 : ℝ) / 4 ≤ mean g) {a b : ℝ} (hab : a ≤ b) :
    (3 : ℝ) / 4 * (b - a) - 1 / 4 ≤ ∫ x in a..b, g x := by
  have hc : Continuous (fun x : ℝ => 1 - g x) := continuous_const.sub hg
  have hcp : Function.Periodic (fun x : ℝ => 1 - g x) 1 := by
    intro x
    exact congrArg (fun z : ℝ => 1 - z) (hp x)
  have hc0 : ∀ x : ℝ, 0 ≤ 1 - g x := fun x => sub_nonneg.mpr (hg1 x)
  have hmean : mean (fun x => 1 - g x) = 1 - mean g := by
    unfold mean
    rw [intervalIntegral.integral_sub (μ := volume) intervalIntegrable_const (hg.intervalIntegrable 0 1)]
    simp
  have hupper := periodic_integral_upper hc hcp hc0 hab
  rw [hmean, intervalIntegral.integral_sub (μ := volume) intervalIntegrable_const (hg.intervalIntegrable a b)] at hupper
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hupper
  have hmupper : (1 - mean g) * (b - a + 1) ≤ (1 / 4 : ℝ) * (b - a + 1) :=
    mul_le_mul_of_nonneg_right (by linarith only [hm]) (by linarith only [hab])
  linarith only [hupper, hmupper]

theorem primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x - mean f) x := by
  have hi := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hm : HasDerivAt (fun y : ℝ => mean f * y) (mean f) x :=
    hasDerivAt_const_mul (x := x) (mean f)
  exact hi.sub hm

theorem primitive_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (primitive f) :=
  continuous_iff_continuousAt.mpr (fun x => (primitive_hasDerivAt hf x).continuousAt)

/-- The centered primitive has amplitude at most the mean, not at most sup(f).
Only nonnegative arguments are needed for the reciprocal-coordinate application. -/
theorem primitive_abs_le_mean {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (hf0 : ∀ x, 0 ≤ f x)
    {x : ℝ} (hx : 0 ≤ x) : |primitive f x| ≤ mean f := by
  let n : ℕ := ⌊x⌋₊
  have hnlo : (n : ℝ) ≤ x := Nat.floor_le hx
  have hnhi : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hmu : 0 ≤ mean f := mean_nonneg hf0
  have hblock : (∫ t in (0 : ℝ)..(n : ℝ), f t) = (n : ℝ) * mean f := by
    have hh := hp.intervalIntegral_add_zsmul_eq (n : ℤ) 0
      (fun s t => hf.intervalIntegrable s t)
    simpa only [mean, zsmul_eq_mul, Int.cast_natCast, zero_add, mul_one] using hh
  have hone : (∫ t in (n : ℝ)..(n : ℝ) + 1, f t) = mean f := by
    simpa only [mean, zero_add] using hp.intervalIntegral_add_eq (n : ℝ) 0
  have hpart0 : 0 ≤ ∫ t in (n : ℝ)..x, f t :=
    intervalIntegral.integral_nonneg_of_forall hnlo hf0
  have hlast0 : 0 ≤ ∫ t in x..(n : ℝ) + 1, f t :=
    intervalIntegral.integral_nonneg_of_forall hnhi.le hf0
  have hparts := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (n : ℝ) x) (hf.intervalIntegrable x ((n : ℝ) + 1))
  rw [hone] at hparts
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 (n : ℝ)) (hf.intervalIntegrable (n : ℝ) x)
  rw [hblock] at hsum
  have hfrac0 : 0 ≤ mean f * (x - (n : ℝ)) :=
    mul_nonneg hmu (sub_nonneg.mpr hnlo)
  have hfrac1 : mean f * (x - (n : ℝ)) ≤ mean f := by
    have hh := mul_le_mul_of_nonneg_left (show x - (n : ℝ) ≤ 1 by linarith only [hnhi]) hmu
    simpa only [mul_one] using hh
  apply abs_le.mpr
  unfold primitive
  constructor <;> nlinarith only [hpart0, hlast0, hparts, hsum, hfrac0, hfrac1]

/-- A scalar integral bound with both signs retained. -/
theorem abs_integral_le_constant {f : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hK : ∀ x ∈ Icc a b, |f x| ≤ K) :
    |∫ x in a..b, f x| ≤ K * (b - a) := by
  have hu := intervalIntegral.integral_mono_on (μ := volume) hab hf intervalIntegrable_const
    (show ∀ x ∈ Icc a b, f x ≤ K from fun x hx => (abs_le.mp (hK x hx)).2)
  have hl := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const hf
    (show ∀ x ∈ Icc a b, -K ≤ f x from fun x hx => (abs_le.mp (hK x hx)).1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hu hl
  apply abs_le.mpr
  constructor <;> nlinarith only [hu, hl]

/-- C1 periodic functions have a single GLOBAL derivative bound. -/
theorem periodic_derivative_bounded {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hp : Function.Periodic g 1) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv g x| ≤ C := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hper : Function.Periodic (deriv g) 1 := by
    intro x
    have hh : HasDerivAt (fun y : ℝ => g (y + 1)) (deriv g (x + 1)) x := by
      have hraw : HasDerivAt (fun y : ℝ => g (y + 1))
          (deriv g (x + 1) * 1) x := by
        with_unfolding_all
          exact (hd (x + 1)).hasDerivAt.comp x ((hasDerivAt_id' x).add_const 1)
      simpa only [mul_one] using hraw
    have heq : (fun y : ℝ => g (y + 1)) = g := funext hp
    rw [heq] at hh
    exact hh.unique (hd x).hasDerivAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn (deriv g) (Icc (0 : ℝ) 1))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  have hfr : Int.fract x ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hshift := (hper.zsmul (Int.floor x)) (Int.fract x)
  simp only [zsmul_eq_mul, mul_one] at hshift
  have hx : Int.fract x + (Int.floor x : ℝ) = x := by
    unfold Int.fract
    ring
  rw [hx] at hshift
  have hbound := hC (Int.fract x) hfr
  rw [Real.norm_eq_abs, ← hshift] at hbound
  exact le_trans hbound (le_max_left _ _)

/-- Derivative of the reciprocal-square coordinate, with no missing sign. -/
theorem reciprocal_square_hasDerivAt (B : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun v : ℝ => B / v ^ 2) (-2 * B / x ^ 3) x := by
  simpa only [show (1 : ℕ) + 1 = 2 by decide,
    show (1 : ℕ) + 2 = 3 by decide, Nat.cast_ofNat] using
    ScalarCalculus148.const_div_pow_hasDerivAt B x 1 hx

/-- Integration by parts at the fast reciprocal coordinate. The error is
proportional to the first window's MEAN and independent of its derivatives.
The second coordinate is never assumed independent of the first. -/
theorem reciprocal_product_lower {f g : ℝ → ℝ}
    (hf : Continuous f) (hfp : Function.Periodic f 1) (hf0 : ∀ x, 0 ≤ f x)
    (hg : ContDiff ℝ 1 g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    {C P B : ℝ} (hC : 0 ≤ C) (hderiv : ∀ x, |deriv g x| ≤ C)
    (hP : 0 < P) (hB : 0 < B) :
    mean f * ((∫ v in P..2 * P, g (B / v ^ 2)) - 9 * P ^ 2 / B - 2 * C) ≤
      ∫ v in P..2 * P, f (B / v) * g (B / v ^ 2) := by
  let mu : ℝ := mean f
  let F : ℝ → ℝ := primitive f
  let u : ℝ → ℝ := fun v => F (B / v)
  let a : ℝ → ℝ := fun v => -(v ^ 2 / B) * g (B / v ^ 2)
  let up : ℝ → ℝ := fun v => (f (B / v) - mu) * (-B / v ^ 2)
  let ap : ℝ → ℝ := fun v => (-2 * v / B) * g (B / v ^ 2) +
    (2 / v) * deriv g (B / v ^ 2)
  let D : ℝ := 4 * P / B + 2 * C / P
  have hmu : 0 ≤ mu := mean_nonneg hf0
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hPP : P ≤ 2 * P := by linarith only [hP]
  have hPne : P ≠ 0 := ne_of_gt hP
  have hBne : B ≠ 0 := ne_of_gt hB
  have hxn : ∀ v ∈ Icc P (2 * P), v ≠ 0 := fun v hv =>
    ne_of_gt (lt_of_lt_of_le hP hv.1)
  have hxnU : ∀ v ∈ uIcc P (2 * P), v ≠ 0 := by
    simpa only [uIcc_of_le hPP] using hxn
  have hdg : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdcg : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hrec : ContinuousOn (fun v : ℝ => B / v) (Icc P (2 * P)) :=
    continuousOn_const.div continuousOn_id hxn
  have hrec2 : ContinuousOn (fun v : ℝ => B / v ^ 2) (Icc P (2 * P)) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun v hv => pow_ne_zero 2 (hxn v hv))
  have hfc : ContinuousOn (fun v => f (B / v)) (Icc P (2 * P)) := hf.comp_continuousOn hrec
  have hgc : ContinuousOn (fun v => g (B / v ^ 2)) (Icc P (2 * P)) := hg.continuous.comp_continuousOn hrec2
  have huc : ContinuousOn u (Icc P (2 * P)) :=
    (primitive_continuous hf).comp_continuousOn hrec
  have hac : ContinuousOn a (Icc P (2 * P)) :=
    ((continuousOn_id.pow 2).div_const B).neg.mul hgc
  have hupc : ContinuousOn up (Icc P (2 * P)) := by
    exact (hfc.sub continuousOn_const).mul
      (continuousOn_const.div (continuousOn_id.pow 2) (fun v hv => pow_ne_zero 2 (hxn v hv)))
  have hapc : ContinuousOn ap (Icc P (2 * P)) := by
    exact (((continuousOn_const.mul continuousOn_id).div_const B).mul hgc).add
      ((continuousOn_const.div continuousOn_id hxn).mul (hdcg.comp_continuousOn hrec2))
  have hu : ∀ v ∈ uIcc P (2 * P), HasDerivAt u (up v) v := by
    intro v hv
    have hr : HasDerivAt (fun x : ℝ => B / x) (-B / v ^ 2) v :=
      ScalarCalculus148.const_div_hasDerivAt B (hxnU v hv)
    with_unfolding_all exact (primitive_hasDerivAt hf (B / v)).comp v hr
  have ha : ∀ v ∈ uIcc P (2 * P), HasDerivAt a (ap v) v := by
    intro v hv
    have hs : HasDerivAt (fun x : ℝ => -(x ^ 2 / B)) (-2 * v / B) v :=
      ScalarCalculus148.neg_square_div_hasDerivAt B v
    have hgcomp : HasDerivAt (fun x : ℝ => g (B / x ^ 2))
        (deriv g (B / v ^ 2) * (-2 * B / v ^ 3)) v := by
      with_unfolding_all
        exact (hdg (B / v ^ 2)).hasDerivAt.comp v
          (reciprocal_square_hasDerivAt B (hxnU v hv))
    have hh : HasDerivAt a
        ((-2 * v / B) * g (B / v ^ 2) +
          (-(v ^ 2 / B)) * (deriv g (B / v ^ 2) * (-2 * B / v ^ 3))) v := by
      with_unfolding_all exact hs.fun_mul hgcomp
    apply hh.congr_deriv
    dsimp [ap]
    field_simp [hBne, hxnU v hv] <;> ring
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub hu ha
    (hupc.intervalIntegrable_of_Icc hPP) (hapc.intervalIntegrable_of_Icc hPP)
  have hproduct : (∫ v in P..2 * P, up v * a v) =
      (∫ v in P..2 * P, (f (B / v) - mu) * g (B / v ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp [up, a]
    field_simp [hBne, hxnU v hv] <;> ring
  have hsplit := intervalIntegral.integral_add (μ := volume)
    ((hupc.mul hac).intervalIntegrable_of_Icc hPP)
    ((huc.mul hapc).intervalIntegrable_of_Icc hPP)
  simp only [Pi.mul_apply] at hsplit
  rw [hsplit, hproduct] at hparts
  have hcenter : (∫ v in P..2 * P, (f (B / v) - mu) * g (B / v ^ 2)) =
      (∫ v in P..2 * P, f (B / v) * g (B / v ^ 2)) -
        mu * (∫ v in P..2 * P, g (B / v ^ 2)) := by
    simp_rw [sub_mul]
    have hsub := intervalIntegral.integral_sub (μ := volume)
      ((hfc.mul hgc).intervalIntegrable_of_Icc hPP)
      (((continuousOn_const : ContinuousOn (fun _ : ℝ => mu) (Icc P (2 * P))).mul hgc).intervalIntegrable_of_Icc hPP)
    simp only [Pi.mul_apply] at hsub
    rw [hsub, intervalIntegral.integral_const_mul]
  rw [hcenter] at hparts
  have huBound : ∀ v ∈ Icc P (2 * P), |u v| ≤ mu := by
    intro v hv
    exact primitive_abs_le_mean hf hfp hf0 (div_nonneg hB.le (le_trans hP.le hv.1))
  have haBound : ∀ v ∈ Icc P (2 * P), |a v| ≤ v ^ 2 / B := by
    intro v hv
    dsimp [a]
    rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg (sq_nonneg v) hB.le),
      abs_of_nonneg (hg0 _)]
    have hh := mul_le_mul_of_nonneg_left (hg1 (B / v ^ 2))
      (div_nonneg (sq_nonneg v) hB.le)
    simpa only [mul_one] using hh
  have hapBound : ∀ v ∈ Icc P (2 * P), |ap v| ≤ D := by
    intro v hv
    have hvpos : 0 < v := lt_of_lt_of_le hP hv.1
    have hfirst : |(-2 * v / B) * g (B / v ^ 2)| ≤ 4 * P / B := by
      rw [abs_mul, abs_div, abs_mul, abs_of_pos hvpos, abs_of_pos hB,
        abs_of_nonneg (hg0 _)]
      rw [show |(-2 : ℝ)| = 2 by norm_num]
      have hgmul := mul_le_mul_of_nonneg_left (hg1 (B / v ^ 2))
        (show 0 ≤ 2 * v / B by positivity)
      have hvup := div_le_div_of_nonneg_right
        (show 2 * v ≤ 4 * P by linarith only [hv.2]) hB.le
      nlinarith only [hgmul, hvup]
    have hsecond : |(2 / v) * deriv g (B / v ^ 2)| ≤ 2 * C / P := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ (2 : ℝ) / v by positivity)]
      have hm := mul_le_mul_of_nonneg_left (hderiv (B / v ^ 2))
        (show 0 ≤ (2 : ℝ) / v by positivity)
      have hvup : (2 : ℝ) / v ≤ 2 / P := div_le_div_of_nonneg_left (by norm_num) hP hv.1
      have hcm := mul_le_mul_of_nonneg_right hvup hC
      calc
        _ ≤ (2 / P) * C := le_trans hm hcm
        _ = 2 * C / P := by ring
    exact le_trans (abs_add_le _ _) (add_le_add hfirst hsecond)
  have hintBound : |∫ v in P..2 * P, u v * ap v| ≤ mu * D * P := by
    have hh := abs_integral_le_constant hPP ((huc.mul hapc).intervalIntegrable_of_Icc hPP)
      (show ∀ v ∈ Icc P (2 * P), |u v * ap v| ≤ mu * D by
        intro v hv
        rw [abs_mul]
        exact mul_le_mul (huBound v hv) (hapBound v hv) (abs_nonneg _) hmu)
    convert hh using 1 <;> ring
  have hleft : |u P * a P| ≤ mu * P ^ 2 / B := by
    rw [abs_mul]
    have hh := mul_le_mul (huBound P ⟨le_rfl, hPP⟩) (haBound P ⟨le_rfl, hPP⟩)
      (abs_nonneg _) hmu
    simpa only [mul_div_assoc] using hh
  have hright : |u (2 * P) * a (2 * P)| ≤ mu * (4 * P ^ 2) / B := by
    rw [abs_mul]
    have hh := mul_le_mul (huBound (2 * P) ⟨hPP, le_rfl⟩)
      (haBound (2 * P) ⟨hPP, le_rfl⟩) (abs_nonneg _) hmu
    convert hh using 1 <;> ring
  have hIupper := le_trans (le_abs_self (∫ v in P..2 * P, u v * ap v)) hintBound
  have hleftUpper := le_trans (le_abs_self (u P * a P)) hleft
  have hrightLower : -(mu * (4 * P ^ 2) / B) ≤ u (2 * P) * a (2 * P) := by
    exact le_trans (neg_le_neg hright) (neg_abs_le _)
  have hDidentity : mu * D * P = mu * (4 * P ^ 2 / B + 2 * C) := by
    dsimp [D]
    field_simp [hPne] <;> ring
  rw [hDidentity] at hIupper
  have hbudget :
      mu * (∫ v in P..2 * P, g (B / v ^ 2)) -
        mu * (4 * P ^ 2) / B - mu * P ^ 2 / B -
        mu * (4 * P ^ 2 / B + 2 * C) ≤
      ∫ v in P..2 * P, f (B / v) * g (B / v ^ 2) := by
    linarith only [hparts, hIupper, hleftUpper, hrightLower]
  change mu * ((∫ v in P..2 * P, g (B / v ^ 2)) - 9 * P ^ 2 / B - 2 * C) ≤ _
  calc
    _ = mu * (∫ v in P..2 * P, g (B / v ^ 2)) -
        mu * (4 * P ^ 2) / B - mu * P ^ 2 / B -
        mu * (4 * P ^ 2 / B + 2 * C) := by ring
    _ ≤ _ := hbudget

#print axioms periodic_integral_upper
#print axioms dense_periodic_integral_lower
#print axioms primitive_hasDerivAt
#print axioms primitive_abs_le_mean
#print axioms periodic_derivative_bounded
#print axioms reciprocal_product_lower
#eval "PERIODIC PRIMITIVE 146 END: deterministic integration only; locally UNCOMPILED"

end Erdos374.PeriodicPrimitive146
end



/-!
# Uniform mass in the square-avoiding coordinate, without an interval cover

Working Update 146. Original, locally UNCOMPILED proof scripts.
The periodic complement has mean at most 1/4. Averaging that complement and
using v -> B/v^2 replaces all four small-scale cases and the many-cell case.
The final bound uses the constructed bounded primitive of the other coordinate.
No prime distribution, PNT, curve estimate, or independence hypothesis occurs.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.SquareMass146
open PeriodicPrimitive146

/-- The fixed square-avoidance window has a unit plateau of length 3/4. -/
theorem square_mean_lower : (3 : ℝ) / 4 ≤ mean Smooth144.squarePeriodic := by
  have hg : Continuous Smooth144.squarePeriodic :=
    (Smooth144.squarePeriodic_contDiff (n := 0)).continuous
  have hg0 : ∀ x : ℝ, 0 ≤ Smooth144.squarePeriodic x :=
    fun x => (Smooth144.squareWindow_bounds (Int.fract x)).1
  have hone : ∀ x ∈ Icc ((1 : ℝ) / 8) (7 / 8), Smooth144.squarePeriodic x = 1 := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith only [hx.1]
    have hx1 : x < 1 := by linarith only [hx.2]
    have hfloor : Int.floor x = 0 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · simpa only [Int.cast_zero] using hx0
      · simpa only [Int.cast_zero, zero_add] using hx1
    have hfract : Int.fract x = x := by simp only [Int.fract, hfloor, Int.cast_zero, sub_zero]
    change Smooth144.squareWindow (Int.fract x) = 1
    rw [hfract]
    exact Smooth144.squareWindow_eq_one_on_core hx.1 hx.2
  have hplateau : (∫ x in ((1 : ℝ) / 8)..(7 / 8), Smooth144.squarePeriodic x) = 3 / 4 := by
    calc
      _ = ∫ _x in ((1 : ℝ) / 8)..(7 / 8), (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (1 : ℝ) / 8 ≤ 7 / 8)] at hx
        exact hone x hx
      _ = _ := by norm_num
  have hh := intervalIntegral.integral_mono_interval (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 ≤ 7 / 8)
    (by norm_num : (7 : ℝ) / 8 ≤ 1) (Filter.Eventually.of_forall hg0)
    (hg.intervalIntegrable 0 1)
  rw [hplateau] at hh
  exact hh

/-- The reciprocal-square substitution includes its negative derivative and
reverses the endpoints. -/
theorem square_jacobian_identity {g : ℝ → ℝ} (hg : Continuous g)
    {P B : ℝ} (hP : 0 < P) :
    (∫ v in P..2 * P, g (B / v ^ 2) * (2 * B / v ^ 3)) =
      ∫ y in B / (2 * P) ^ 2..B / P ^ 2, g y := by
  have hPP : P ≤ 2 * P := by linarith only [hP]
  have hxn : ∀ v ∈ uIcc P (2 * P), v ≠ 0 := by
    intro v hv
    rw [uIcc_of_le hPP] at hv
    exact ne_of_gt (lt_of_lt_of_le hP hv.1)
  have hd : ∀ v ∈ uIcc P (2 * P),
      HasDerivAt (fun x : ℝ => B / x ^ 2) (-(2 * B / v ^ 3)) v := by
    intro v hv
    convert reciprocal_square_hasDerivAt B (hxn v hv) using 1 <;> ring
  have hc : ContinuousOn (fun v : ℝ => -(2 * B / v ^ 3)) (uIcc P (2 * P)) :=
    (continuousOn_const.div (continuousOn_id.pow 3) (fun v hv => pow_ne_zero 3 (hxn v hv))).neg
  have hh := intervalIntegral.integral_comp_mul_deriv hd hc hg
  simp only [Function.comp_apply, mul_neg, intervalIntegral.integral_neg] at hh
  rw [intervalIntegral.integral_symm (B / (2 * P) ^ 2) (B / P ^ 2)] at hh
  exact neg_injective hh

/-- A single bound valid for every B/P^2 >= 15/16, with no finite cell cover. -/
theorem square_coordinate_mass {g : ℝ → ℝ} (hg : Continuous g)
    (hp : Function.Periodic g 1) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hm : (3 : ℝ) / 4 ≤ mean g)
    {P B : ℝ} (hP : 0 < P) (hB : 0 < B) (hscale : 15 * P ^ 2 ≤ 16 * B) :
    P / 8 ≤ ∫ v in P..2 * P, g (B / v ^ 2) := by
  have hPne : P ≠ 0 := ne_of_gt hP
  have hPP : P ≤ 2 * P := by linarith only [hP]
  have hxn : ∀ v ∈ Icc P (2 * P), v ≠ 0 :=
    fun v hv => ne_of_gt (lt_of_lt_of_le hP hv.1)
  have hrec : ContinuousOn (fun v : ℝ => B / v ^ 2) (Icc P (2 * P)) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun v hv => pow_ne_zero 2 (hxn v hv))
  have hgc := hg.comp_continuousOn hrec
  have hjac : ContinuousOn (fun v : ℝ => 2 * B / v ^ 3) (Icc P (2 * P)) :=
    continuousOn_const.div (continuousOn_id.pow 3) (fun v hv => pow_ne_zero 3 (hxn v hv))
  have hweighted := intervalIntegral.integral_mono_on (μ := volume) hPP
    ((hgc.mul hjac).intervalIntegrable_of_Icc hPP)
    ((continuousOn_const.mul hgc).intervalIntegrable_of_Icc hPP)
    (show ∀ v ∈ Icc P (2 * P),
      g (B / v ^ 2) * (2 * B / v ^ 3) ≤ (2 * B / P ^ 3) * g (B / v ^ 2) by
      intro v hv
      have hpows : P ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ hP.le hv.1 3
      have hdiv := div_le_div_of_nonneg_left (show 0 ≤ 2 * B by positivity)
        (pow_pos hP 3) hpows
      have hh := mul_le_mul_of_nonneg_left hdiv (hg0 (B / v ^ 2))
      simpa only [mul_comm (g (B / v ^ 2)) (2 * B / P ^ 3)] using hh)
  simp only [Pi.mul_apply, Function.comp_apply] at hweighted
  rw [square_jacobian_identity hg hP, intervalIntegral.integral_const_mul] at hweighted
  have hends : B / (2 * P) ^ 2 ≤ B / P ^ 2 := by
    apply div_le_div_of_nonneg_left hB.le (pow_pos hP 2)
    nlinarith only [sq_nonneg P]
  have hperiod := dense_periodic_integral_lower hg hp hg1 hm hends
  have hnum : 0 ≤ 5 * B - 4 * P ^ 2 := by nlinarith only [hscale, sq_nonneg P]
  have hden : 0 < 16 * P ^ 2 := by positivity
  have hid :
      (((3 : ℝ) / 4 * (B / P ^ 2 - B / (2 * P) ^ 2) - 1 / 4) -
        (2 * B / P ^ 3) * (P / 8)) * (16 * P ^ 2) = 5 * B - 4 * P ^ 2 := by
    field_simp [hPne] <;> ring
  have htarget : (2 * B / P ^ 3) * (P / 8) ≤
      (3 : ℝ) / 4 * (B / P ^ 2 - B / (2 * P) ^ 2) - 1 / 4 := by
    by_contra hn
    have hneg : ((3 : ℝ) / 4 * (B / P ^ 2 - B / (2 * P) ^ 2) - 1 / 4) -
        (2 * B / P ^ 3) * (P / 8) < 0 := sub_neg.mpr (lt_of_not_ge hn)
    have hpneg := mul_neg_of_neg_of_pos hneg hden
    rw [hid] at hpneg
    exact (not_lt_of_ge hnum) hpneg
  exact le_of_mul_le_mul_left (le_trans htarget (le_trans hperiod hweighted))
    (show 0 < 2 * B / P ^ 3 by positivity)

/-- Two correlated reciprocal coordinates have a positive main term once P is
larger than a fixed derivative constant of the SECOND window. The first
window may shrink: its derivatives do not enter this estimate. -/
theorem two_coordinate_lower {f g : ℝ → ℝ}
    (hf : Continuous f) (hfp : Function.Periodic f 1) (hf0 : ∀ x, 0 ≤ f x)
    (hg : ContDiff ℝ 1 g) (hgp : Function.Periodic g 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) (hgm : (3 : ℝ) / 4 ≤ mean g)
    {δ C P B : ℝ} (hδ : 0 ≤ δ) (hfm : δ ≤ mean f)
    (hC : 0 ≤ C) (hderiv : ∀ x, |deriv g x| ≤ C)
    (hP : 0 < P) (hB : 0 < B) (hscale : 15 * P ^ 2 ≤ 16 * B)
    (hlarge : 16 * (10 + 2 * C) ≤ P) :
    δ * P / 16 ≤ ∫ v in P..2 * P, f (B / v) * g (B / v ^ 2) := by
  have hmass := square_coordinate_mass hg.continuous hgp hg0 hg1 hgm hP hB hscale
  have hprod := reciprocal_product_lower hf hfp hf0 hg hg0 hg1 hC hderiv hP hB
  have hratio : 9 * P ^ 2 / B ≤ 10 := by
    apply (div_le_iff₀ hB).mpr
    nlinarith only [hscale, sq_nonneg P]
  have hbase : P / 16 ≤ (∫ v in P..2 * P, g (B / v ^ 2)) - 9 * P ^ 2 / B - 2 * C := by
    linarith only [hmass, hratio, hlarge]
  have hmu : 0 ≤ mean f := mean_nonneg hf0
  have h1 := mul_le_mul_of_nonneg_right hfm (show 0 ≤ P / 16 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hbase hmu
  calc
    δ * P / 16 = δ * (P / 16) := by ring
    _ ≤ mean f * (P / 16) := h1
    _ ≤ mean f * ((∫ v in P..2 * P, g (B / v ^ 2)) - 9 * P ^ 2 / B - 2 * C) := h2
    _ ≤ _ := hprod

/-- The derivative constant is CONSTRUCTED from the fixed smooth periodic window. -/
theorem square_derivative_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Smooth144.squarePeriodic x| ≤ C := by
  exact periodic_derivative_bounded (Smooth144.squarePeriodic_contDiff (n := 1))
    (Smooth144.periodize_periodic Smooth144.squareWindow)

#print axioms square_mean_lower
#print axioms square_jacobian_identity
#print axioms square_coordinate_mass
#print axioms two_coordinate_lower
#print axioms square_derivative_bounded
#eval "SQUARE MASS 146 END: no cell cover, no independence assumption; locally UNCOMPILED"

end Erdos374.SquareMass146
end



/-!
# The actual continuous sparse reference integral, in BOTH branches

Working Update 146. Original proof scripts, locally UNCOMPILED.
The high-band result from 145 is retained. The other branch uses the new
periodic-primitive proof, not an unconstructed finite interval cover.
A single fixed threshold is constructed from the fixed square-window derivative.
This does not prove the prime-sampling error, Harman, PNT or the curve-count theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.FullReference146
open PeriodicPrimitive146 SquareMass146 PeriodicAveraging145
open Erdos374.RemainingAnalytic115.RemainingAnalytic127

/-- A fixed threshold for the full continuous bound. It has NO external analytic
arguments and covers c >= P^2 as well as c < P^2. -/
theorem referenceIntegral_lower :
    ∃ N : ℕ, 16 ≤ N ∧ ∀ b c P : ℕ,
      N ≤ P → b < c → c - b < P → 16 * P ≤ b →
      ((c - b : ℕ) : ℝ) / (128 * Real.log (2 * (P : ℝ))) ≤
        SmoothSparse144.referenceIntegral b c P := by
  obtain ⟨C, hC0, hC⟩ := square_derivative_bounded
  let N : ℕ := max 16 ⌈16 * (10 + 2 * C)⌉₊
  refine ⟨N, le_max_left _ _, ?_⟩
  intro b c P hNP hbc hgap hscale
  have hP16 : 16 ≤ P := le_trans (le_max_left _ _) hNP
  have hP2 : 2 ≤ P := by omega
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hP1 : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
  have hL : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by linarith only [hP1])
  have hh0 : (0 : ℝ) ≤ ((c - b : ℕ) : ℝ) := by positivity
  by_cases hhigh : c < P ^ 2
  · have hmain := highBand_referenceIntegral_lower hP2 hbc hgap hscale hhigh
    have hweak : ((c - b : ℕ) : ℝ) / (128 * Real.log (2 * (P : ℝ))) ≤
        ((c - b : ℕ) : ℝ) / (64 * Real.log (2 * (P : ℝ))) := by
      apply div_le_div_of_nonneg_left hh0 (by positivity)
      linarith only [hL]
    exact le_trans hweak hmain
  · have hlow : P ^ 2 ≤ c := le_of_not_gt hhigh
    have hb0 : (0 : ℝ) < (b : ℝ) := by
      exact_mod_cast (show 0 < b by nlinarith only [hscale, hP16])
    have hsum : b + (c - b) = c := Nat.add_sub_of_le hbc.le
    have hPprod : 16 * P ≤ P ^ 2 := by
      have hh := Nat.mul_le_mul_left P hP16
      simpa only [pow_two, Nat.mul_comm] using hh
    have hqscaleN : 15 * P ^ 2 ≤ 16 * b := by
      nlinarith only [hlow, hsum, hgap, hPprod]
    have hqscale : 15 * (P : ℝ) ^ 2 ≤ 16 * (b : ℝ) := by exact_mod_cast hqscaleN
    have hceil : 16 * (10 + 2 * C) ≤ (⌈16 * (10 + 2 * C)⌉₊ : ℝ) := Nat.le_ceil _
    have hlarge : 16 * (10 + 2 * C) ≤ (P : ℝ) := by
      have hceilP : ⌈16 * (10 + 2 * C)⌉₊ ≤ P := le_trans (le_max_right _ _) hNP
      exact le_trans hceil (by exact_mod_cast hceilP)
    let δ : ℝ := SmoothSparse144.width b c P
    have hδ : 0 < δ := by
      dsimp [δ, SmoothSparse144.width]
      have hhpos : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
      positivity
    have hδsmall : δ ≤ 1 / 8 := by
      dsimp [δ, SmoothSparse144.width]
      apply (div_le_iff₀ (show (0 : ℝ) < 8 * (P : ℝ) by positivity)).mpr
      have hhP : ((c - b : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast hgap
      linarith only [hhP]
    have hf : Continuous (Smooth144.crossingPeriodic δ) :=
      (Smooth144.crossingPeriodic_contDiff (n := 0) hδ hδsmall).continuous
    have hfp := Smooth144.periodize_periodic (Smooth144.crossingWindow δ)
    have hf0 : ∀ x, 0 ≤ Smooth144.crossingPeriodic δ x :=
      fun x => (Smooth144.crossingWindow_bounds δ (Int.fract x)).1
    have hfm : δ ≤ mean (Smooth144.crossingPeriodic δ) := crossing_mean_lower hδ hδsmall
    have hg : ContDiff ℝ 1 Smooth144.squarePeriodic := Smooth144.squarePeriodic_contDiff (n := 1)
    have hgp := Smooth144.periodize_periodic Smooth144.squareWindow
    have hg0 : ∀ x, 0 ≤ Smooth144.squarePeriodic x :=
      fun x => (Smooth144.squareWindow_bounds (Int.fract x)).1
    have hg1 : ∀ x, Smooth144.squarePeriodic x ≤ 1 :=
      fun x => (Smooth144.squareWindow_bounds (Int.fract x)).2
    have hprod := two_coordinate_lower hf hfp hf0 hg hgp hg0 hg1 square_mean_lower
      hδ.le hfm hC0 hC hP0 hb0 hqscale hlarge
    have hrec1 : ContinuousOn (fun v : ℝ => (b : ℝ) / v) (Icc (P : ℝ) (2 * (P : ℝ))) :=
      continuousOn_const.div continuousOn_id
        (fun v hv => ne_of_gt (lt_of_lt_of_le hP0 hv.1))
    have hrec2 : ContinuousOn (fun v : ℝ => (b : ℝ) / v ^ 2) (Icc (P : ℝ) (2 * (P : ℝ))) :=
      continuousOn_const.div (continuousOn_id.pow 2)
        (fun v hv => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hP0 hv.1)))
    have hprodcont : ContinuousOn (fun v : ℝ =>
        Smooth144.crossingPeriodic δ ((b : ℝ) / v) *
          Smooth144.squarePeriodic ((b : ℝ) / v ^ 2)) (Icc (P : ℝ) (2 * (P : ℝ))) :=
      (hf.comp_continuousOn hrec1).mul (hg.continuous.comp_continuousOn hrec2)
    have hprod0 : ∀ v ∈ Icc (P : ℝ) (2 * (P : ℝ)),
        0 ≤ Smooth144.crossingPeriodic δ ((b : ℝ) / v) *
          Smooth144.squarePeriodic ((b : ℝ) / v ^ 2) :=
      fun v _hv => mul_nonneg (hf0 _) (hg0 _)
    have hlog := logarithmic_weight_lower hP1 hprodcont hprod0
    have hdivide := div_le_div_of_nonneg_right hprod hL.le
    have hid : (δ * (P : ℝ) / 16) / Real.log (2 * (P : ℝ)) =
        ((c - b : ℕ) : ℝ) / (128 * Real.log (2 * (P : ℝ))) := by
      dsimp [δ, SmoothSparse144.width]
      field_simp [ne_of_gt hP0, ne_of_gt hL] <;> ring
    rw [hid] at hdivide
    have hresult := le_trans hdivide hlog
    simpa [SmoothSparse144.referenceIntegral, SmoothSparse144.periodicTest,
      Smooth144.test, hhigh, δ] using hresult

/-- The old main-term budget is supplied by the stronger 1/128 continuous bound. -/
theorem referenceIntegral_lower320 :
    ∃ N : ℕ, 16 ≤ N ∧ ∀ b c P : ℕ,
      N ≤ P → b < c → c - b < P → 16 * P ≤ b →
      ((c - b : ℕ) : ℝ) / (320 * Real.log (2 * (P : ℝ))) ≤
        SmoothSparse144.referenceIntegral b c P := by
  obtain ⟨N, hN16, hN⟩ := referenceIntegral_lower
  refine ⟨N, hN16, ?_⟩
  intro b c P hP hbc hgap hscale
  have hmain := hN b c P hP hbc hgap hscale
  have hP16 : 16 ≤ P := le_trans hN16 hP
  have hlog : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by
    exact_mod_cast (show 1 < 2 * P by omega))
  have hweak : ((c - b : ℕ) : ℝ) / (320 * Real.log (2 * (P : ℝ))) ≤
      ((c - b : ℕ) : ℝ) / (128 * Real.log (2 * (P : ℝ))) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith only [hlog]
  exact le_trans hweak hmain

/-- The continuous lower bound is no longer an independent premise here.
The actual prime-sampling error remains an EXPLICIT, unproved premise. -/
theorem sparseCount_from_sampling :
    ∃ N : ℕ, 16 ≤ N ∧ ∀ a b c P : ℕ,
      N ≤ P → b < c → a < P → c - b < P → 16 * P ≤ b →
      |SmoothSparse144.score b c P - SmoothSparse144.referenceIntegral b c P| ≤
        ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ))) →
      ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ))) ≤
        ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  obtain ⟨N, hN16, hN⟩ := referenceIntegral_lower320
  refine ⟨N, hN16, ?_⟩
  intro a b c P hP hbc haP hgap hscale herr
  exact SmoothSparse144.count_of_integral_and_sampling hbc (le_trans hN16 hP)
    haP hgap (hN b c P hP hbc hgap hscale) herr

#print axioms referenceIntegral_lower
#print axioms referenceIntegral_lower320
#print axioms sparseCount_from_sampling
#check referenceIntegral_lower
#check sparseCount_from_sampling
#eval "FULL REFERENCE 146 END: continuous main term constructed; PRIME SAMPLING STILL A PREMISE"

end Erdos374.FullReference146
end

#print axioms Erdos374.RemainingAnalytic115.RemainingAnalytic141.candidate_main_from_mediumPNT141
#check Erdos374.RemainingAnalytic115.RemainingAnalytic141.candidate_main_from_mediumPNT141
#print Erdos374.RemainingAnalytic115.RemainingAnalytic141.RemainingNonPNTInputs141
#eval "ERDOS374 WORKING UPDATE 146 END — FOUR ANALYTIC INPUTS STILL REQUIRED"



/-!
# Uniform derivative bounds for the ACTUAL shrinking sparse test

Working 147. NEW PROOF SCRIPTS: NOT COMPILED in the preparation runtime.
No prime distribution, PNT, curve-count or Harman hypothesis is used here.

The conclusion uses Mathlib's iterated Frechet derivatives and their operator
norms, not a formal list of expressions called derivatives. Boundary points in
fractional-part periodization are treated by local equality to zero.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace Erdos374.UniformC3_147
open Erdos374.Smooth144

/-- All iterated derivatives commute with this periodization, INCLUDING integers.
The two zero-neighborhood hypotheses are essential at the seam. -/
theorem iteratedDeriv_periodize {f : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hleft : ∀ u : ℝ, u ≤ ε → f u = 0)
    (hright : ∀ u : ℝ, 1 - ε ≤ u → f u = 0)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (periodize f) x = iteratedDeriv n f (Int.fract x) := by
  let k : ℤ := Int.floor x
  have hklo : (k : ℝ) ≤ x := Int.floor_le x
  have hkhi : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  by_cases hx : x = (k : ℝ)
  · have hnbhd : Ioo ((k : ℝ) - ε) ((k : ℝ) + ε) ∈ nhds x := by
      rw [hx]
      exact Ioo_mem_nhds (by linarith) (by linarith)
    have heq : periodize f =ᶠ[nhds x] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hnbhd] with y hy
      by_cases hyk : (k : ℝ) ≤ y
      · have hfy : Int.floor y = k := by
          apply Int.floor_eq_iff.mpr
          exact ⟨hyk, by linarith only [hy.2, hε1]⟩
        change f (Int.fract y) = 0
        have hfr : Int.fract y = y - (k : ℝ) := by simp only [Int.fract, hfy]
        rw [hfr]
        exact hleft _ (by linarith only [hy.2])
      · have hyk' : y < (k : ℝ) := lt_of_not_ge hyk
        have hfy : Int.floor y = k - 1 := by
          apply Int.floor_eq_iff.mpr
          constructor
          · push_cast
            linarith only [hy.1, hε1]
          · push_cast
            linarith only [hyk']
        change f (Int.fract y) = 0
        have hfr : Int.fract y = y - ((k : ℝ) - 1) := by
          simp only [Int.fract, hfy, Int.cast_sub, Int.cast_one]
        rw [hfr]
        exact hright _ (by linarith only [hy.1])
    have hbase : f =ᶠ[nhds (0 : ℝ)] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with y hy
      exact hleft y hy.2.le
    have hfract : Int.fract x = 0 := by
      change x - (Int.floor x : ℝ) = 0
      exact sub_eq_zero.mpr hx
    rw [hfract, Filter.EventuallyEq.iteratedDeriv_eq n heq,
      Filter.EventuallyEq.iteratedDeriv_eq n hbase]
    simp [iteratedDeriv_const]
  · have hklt : (k : ℝ) < x := lt_of_le_of_ne hklo (Ne.symm hx)
    have hnbhd : Ioo (k : ℝ) ((k : ℝ) + 1) ∈ nhds x := Ioo_mem_nhds hklt hkhi
    have heq : periodize f =ᶠ[nhds x] (fun y : ℝ => f (y - (k : ℝ))) := by
      filter_upwards [hnbhd] with y hy
      have hfy : Int.floor y = k := Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩
      simp only [periodize, Int.fract, hfy]
    rw [Filter.EventuallyEq.iteratedDeriv_eq n heq,
      iteratedDeriv_comp_sub_const n f (k : ℝ)]
    rfl

/-- The fixed bump, before dilation, is compactly supported. -/
theorem bump_compactSupport : HasCompactSupport bump := by
  apply HasCompactSupport.intro (K := Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  apply bump_zero_of_one_le_abs
  by_contra hnot
  have habs : |x| < 1 := lt_of_not_ge hnot
  have hbounds := abs_lt.mp habs
  exact hx ⟨hbounds.1.le, hbounds.2.le⟩

/-- The unperiodized square window is also a fixed compactly supported function. -/
theorem squareWindow_compactSupport : HasCompactSupport squareWindow := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  by_cases hx0 : x < 0
  · exact squareWindow_zero_edges.1 x (by linarith)
  · have hx1 : 1 < x := by
      by_contra hnot
      exact hx ⟨le_of_not_gt hx0, le_of_not_gt hnot⟩
    exact squareWindow_zero_edges.2 x (by linarith)

/-- These two constants are constructed once, before the width is chosen. -/
theorem fixed_cutoff_bounds (m : ℕ) :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧
      (∀ n ≤ m, ∀ x : ℝ, |iteratedDeriv n bump x| ≤ A) ∧
      (∀ n ≤ m, ∀ x : ℝ, |iteratedDeriv n squareWindow x| ≤ B) := by
  obtain ⟨A, hA0, hA⟩ := bump_compactSupport.exists_bound_iteratedFDeriv
    (show ContDiff ℝ (⊤ : ℕ∞) bump from bump_contDiff) m
  obtain ⟨B, hB0, hB⟩ := squareWindow_compactSupport.exists_bound_iteratedFDeriv
    (show ContDiff ℝ (⊤ : ℕ∞) squareWindow from squareWindow_contDiff) m
  refine ⟨max 1 A, max 1 B, le_max_left _ _, le_max_left _ _, ?_, ?_⟩
  · intro n hn x
    have hh := hA n hn x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hh
    exact le_trans hh (le_max_right _ _)
  · intro n hn x
    have hh := hB n hn x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hh
    exact le_trans hh (le_max_right _ _)

/-- Exact dilation and translation formula, with the scalar outside the derivative. -/
theorem iteratedDeriv_scaled {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f)
    (width center x : ℝ) :
    iteratedDeriv n (fun y : ℝ => f ((y - center) / width)) x =
      (width⁻¹) ^ n * iteratedDeriv n f ((x - center) / width) := by
  have heq : (fun y : ℝ => f ((y - center) / width)) =
      (fun y : ℝ => (fun z : ℝ => f (width⁻¹ * z)) (y - center)) := by
    funext y
    congr 1
    ring
  rw [heq, iteratedDeriv_comp_sub_const n (fun z : ℝ => f (width⁻¹ * z)) center,
    iteratedDeriv_comp_const_mul hf (width⁻¹)]
  simp only [div_eq_mul_inv, mul_comm]

/-- The periodized first window has derivative growth delta^(-n), uniformly in x. -/
theorem crossing_derivative_bound {A δ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (hA : ∀ x : ℝ, |iteratedDeriv n bump x| ≤ A) (x : ℝ) :
    |iteratedDeriv n (crossingPeriodic δ) x| ≤ A * (δ⁻¹) ^ n := by
  have hedges := crossingWindow_zero_edges hδ hδsmall
  change |iteratedDeriv n (periodize (crossingWindow δ)) x| ≤ _
  rw [iteratedDeriv_periodize hδ (by linarith) hedges.1 hedges.2 n x]
  change |iteratedDeriv n (fun y : ℝ => bump ((y - (1 - 3 * δ)) / δ))
    (Int.fract x)| ≤ _
  rw [iteratedDeriv_scaled (show ContDiff ℝ n bump from bump_contDiff)]
  rw [abs_mul, abs_pow, abs_inv, abs_of_pos hδ]
  have hm := mul_le_mul_of_nonneg_left (hA ((Int.fract x - (1 - 3 * δ)) / δ))
    (show 0 ≤ (δ⁻¹) ^ n by positivity)
  simpa only [mul_comm] using hm

/-- Periodizing the fixed second window does not enlarge any derivative bound. -/
theorem square_derivative_bound {B : ℝ} {n : ℕ}
    (hB : ∀ x : ℝ, |iteratedDeriv n squareWindow x| ≤ B) (x : ℝ) :
    |iteratedDeriv n squarePeriodic x| ≤ B := by
  change |iteratedDeriv n (periodize squareWindow) x| ≤ _
  rw [iteratedDeriv_periodize (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num)
    squareWindow_zero_edges.1 squareWindow_zero_edges.2 n x]
  exact hB _

/-- A contraction into R cannot enlarge the operator norm of a scalar derivative. -/
theorem norm_iteratedFDeriv_comp_contraction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (n : ℕ) (hn : n ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ |iteratedDeriv n f (L x)| := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hn)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ∏ _i : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        (∏ _i : Fin n, ‖L‖) = ‖L‖ ^ n := by simp
        _ ≤ (1 : ℝ) ^ n := pow_le_pow_left₀ (norm_nonneg L) hL n
        _ = 1 := one_pow n
    _ = _ := by rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]

/-- A concrete bound through order three for both choices of the square test.
The constant is independent of delta, of the Boolean branch and of the point. -/
theorem test_derivatives_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 →
      ∀ q : Bool, ∀ n : ℕ, n ≤ 3 → ∀ z : ℝ × ℝ,
        ‖iteratedFDeriv ℝ n (test δ q) z‖ ≤ C * (δ⁻¹) ^ 3 := by
  obtain ⟨A, B, hA1, hB1, hA, hB⟩ := fixed_cutoff_bounds 3
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA1
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
  have hAp : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hA1
  have hBp : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hB1
  refine ⟨8 * A * B, by positivity, ?_⟩
  intro δ hδ hδsmall q n hn z
  have hinv : 1 ≤ δ⁻¹ := by
    have hδ1 : δ ≤ 1 := by linarith
    simpa using (one_div_le_one_div_of_le hδ hδ1)
  have hpow (i : ℕ) (hi : i ≤ 3) : (δ⁻¹) ^ i ≤ (δ⁻¹) ^ 3 := by
    exact pow_le_pow_right₀ hinv hi
  have hfirst (i : ℕ) (hi : i ≤ 3) :
      ‖iteratedFDeriv ℝ i (fun w : ℝ × ℝ => crossingPeriodic δ w.1) z‖ ≤
        A * (δ⁻¹) ^ 3 := by
    have hproj := norm_iteratedFDeriv_comp_contraction
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
      (show ContDiff ℝ 3 (crossingPeriodic δ) from crossingPeriodic_contDiff hδ hδsmall)
      i hi z
    have hscalar := crossing_derivative_bound hδ hδsmall (hA i hi) z.1
    have hscale := mul_le_mul_of_nonneg_left (hpow i hi) hA0
    exact le_trans hproj (le_trans hscalar hscale)
  have hsecond (i : ℕ) (hi : i ≤ 3) :
      ‖iteratedFDeriv ℝ i (fun w : ℝ × ℝ => squarePeriodic w.2) z‖ ≤ B := by
    have hproj := norm_iteratedFDeriv_comp_contraction
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
      (show ContDiff ℝ 3 squarePeriodic from squarePeriodic_contDiff) i hi z
    exact le_trans hproj (square_derivative_bound (hB i hi) z.2)
  cases q
  · change ‖iteratedFDeriv ℝ n (fun w : ℝ × ℝ =>
        crossingPeriodic δ w.1 * squarePeriodic w.2) z‖ ≤ _
    have hf : ContDiff ℝ 3 (fun w : ℝ × ℝ => crossingPeriodic δ w.1) :=
      (crossingPeriodic_contDiff hδ hδsmall).comp contDiff_fst
    have hg : ContDiff ℝ 3 (fun w : ℝ × ℝ => squarePeriodic w.2) :=
      squarePeriodic_contDiff.comp contDiff_snd
    have hprod := norm_iteratedFDeriv_mul_le hf hg z (n := n) (by exact_mod_cast hn)
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun w : ℝ × ℝ => crossingPeriodic δ w.1) z‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun w : ℝ × ℝ => squarePeriodic w.2) z‖) ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (A * (δ⁻¹) ^ 3) * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hi3 : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
      have hni3 : n - i ≤ 3 := by omega
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hfirst i hi3) (by positivity)
      · exact hsecond (n - i) hni3
      · exact norm_nonneg _
      · positivity
    have hlast : (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (A * (δ⁻¹) ^ 3) * B) ≤ 8 * A * B * (δ⁻¹) ^ 3 := by
      have hcoeff : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) ≤ 8 := by
        interval_cases n <;> norm_num [Finset.sum_range_succ]
      have hQ : 0 ≤ (A * (δ⁻¹) ^ 3) * B := by positivity
      calc
        _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) *
            ((A * (δ⁻¹) ^ 3) * B) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ 8 * ((A * (δ⁻¹) ^ 3) * B) := mul_le_mul_of_nonneg_right hcoeff hQ
        _ = _ := by ring
    exact le_trans hprod (le_trans hsum hlast)
  · change ‖iteratedFDeriv ℝ n (fun w : ℝ × ℝ => crossingPeriodic δ w.1) z‖ ≤ _
    have hscale : A * (δ⁻¹) ^ 3 ≤ 8 * A * B * (δ⁻¹) ^ 3 := by
      have hAB := mul_le_mul_of_nonneg_left hB1 (show 0 ≤ A * (δ⁻¹) ^ 3 by positivity)
      nlinarith only [hAB, show 0 ≤ A * (δ⁻¹) ^ 3 by positivity]
    exact le_trans (hfirst n hn) hscale

/-- A genuine C3 size: sum of the suprema of the first FOUR operator norms,
including order zero. Bounds below prove that these suprema are finite. -/
def c3Size (f : (ℝ × ℝ) → ℝ) : ℝ :=
  ∑ n ∈ Finset.range 4, sSup (Set.range (fun z : ℝ × ℝ => ‖iteratedFDeriv ℝ n f z‖))

/-- Pointwise uniform derivative bounds give a bound for the actual C3 size. -/
theorem c3Size_le {f : (ℝ × ℝ) → ℝ} {K : ℝ}
    (hK : ∀ n : ℕ, n ≤ 3 → ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ n f z‖ ≤ K) :
    c3Size f ≤ 4 * K := by
  calc
    _ ≤ ∑ _n ∈ Finset.range 4, K := by
      apply Finset.sum_le_sum
      intro n hn
      apply csSup_le (Set.range_nonempty _)
      rintro r ⟨z, rfl⟩
      exact hK n (by have := Finset.mem_range.mp hn; omega) z
    _ = _ := by simp

/-- The fixed coefficient is chosen BEFORE the varying width and branch. -/
theorem test_c3Size_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 → ∀ q : Bool,
      c3Size (test δ q) ≤ K / δ ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := test_derivatives_uniform
  refine ⟨4 * C, by positivity, ?_⟩
  intro δ hδ hδsmall q
  have hh := c3Size_le (hbound δ hδ hδsmall q)
  simpa only [inv_pow, div_eq_mul_inv, mul_assoc] using hh

#print axioms iteratedDeriv_periodize
#print axioms fixed_cutoff_bounds
#print axioms crossing_derivative_bound
#print axioms norm_iteratedFDeriv_comp_contraction
#print axioms test_derivatives_uniform
#print axioms test_c3Size_uniform
#check test_c3Size_uniform
#eval "UNIFORM C3 147 END: no prime sampling or other analytic input used"

end Erdos374.UniformC3_147
end



/-!
# Exact reciprocal-phase derivatives and their cancellation geometry

Working 147. Original proof scripts; NOT COMPILED.
These are deterministic derivative theorems for phi(t)=u/t+v/t^2. They do not
assert a prime-sampling estimate or an exponential-sum bound.
The exact order-r derivative has at most one zero on the positive axis when
u is nonzero. Two consecutive normalized derivatives cannot both be small
relative to |u|+|v|/t. This exposes the critical-point excisions needed in the
remaining Vinogradov/Type-I/Type-II argument without assuming cancellation.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace Erdos374.ReciprocalPhase147

def phase (u v t : ℝ) : ℝ := u / t + v / t ^ 2

/-- Dilation preserves the same two-term reciprocal phase family. -/
theorem phase_product (u v m t : ℝ) (hm : m ≠ 0) (ht : t ≠ 0) :
    phase u v (m * t) = phase (u / m) (v / m ^ 2) t := by
  unfold phase
  field_simp [hm, ht] <;> ring

/-- The off-diagonal difference arising in a bilinear Cauchy step still has
exactly the same phase geometry; no exponential-sum estimate is asserted. -/
theorem phase_product_difference (u v m n t : ℝ)
    (hm : m ≠ 0) (hn : n ≠ 0) (ht : t ≠ 0) :
    phase u v (m * t) - phase u v (n * t) =
      phase (u * (1 / m - 1 / n)) (v * (1 / m ^ 2 - 1 / n ^ 2)) t := by
  rw [phase_product u v m t hm ht, phase_product u v n t hn ht]
  unfold phase
  ring

def derivativeFormula (r : ℕ) (u v t : ℝ) : ℝ :=
  (-1 : ℝ) ^ r * (r.factorial : ℝ) *
    (u / t ^ (r + 1) + ((r + 1 : ℕ) : ℝ) * v / t ^ (r + 2))

/-- A reusable exact derivative of a reciprocal positive power. -/
theorem hasDerivAt_reciprocalPower (a t : ℝ) (n : ℕ) (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => a / x ^ (n + 1))
      (-((n + 1 : ℕ) : ℝ) * a / t ^ (n + 2)) t := by
  exact ScalarCalculus148.const_div_pow_hasDerivAt a t n ht

/-- Successive explicit formulas really are derivatives, not formal placeholders. -/
theorem derivativeFormula_hasDerivAt (r : ℕ) (u v t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (derivativeFormula r u v) (derivativeFormula (r + 1) u v t) t := by
  have h1 := hasDerivAt_reciprocalPower u t r ht
  have h2 := hasDerivAt_reciprocalPower (((r + 1 : ℕ) : ℝ) * v) t (r + 1) ht
  have hd := (h1.add h2).const_mul ((-1 : ℝ) ^ r * (r.factorial : ℝ))
  apply hd.congr_deriv
  simp only [derivativeFormula, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  ring

/-- The exact formula for ALL orders, on the punctured real line. -/
theorem iteratedDeriv_phase (r : ℕ) (u v : ℝ) {t : ℝ} (ht : t ≠ 0) :
    iteratedDeriv r (phase u v) t = derivativeFormula r u v t := by
  induction r generalizing t with
  | zero => simp [phase, derivativeFormula]
  | succ r ih =>
    have hne : ∀ᶠ x : ℝ in nhds t, x ≠ 0 := eventually_ne_nhds ht
    have heq : iteratedDeriv r (phase u v) =ᶠ[nhds t] derivativeFormula r u v := by
      filter_upwards [hne] with x hx
      exact ih hx
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact (derivativeFormula_hasDerivAt r u v t ht).deriv

/-- The variable part after removing the nonzero factorial/sign/power factors. -/
def normalized (r : ℕ) (u v t : ℝ) : ℝ := u + ((r + 1 : ℕ) : ℝ) * v / t

theorem derivativeFormula_factor (r : ℕ) (u v t : ℝ) (ht : t ≠ 0) :
    derivativeFormula r u v t =
      ((-1 : ℝ) ^ r * (r.factorial : ℝ) / t ^ (r + 1)) * normalized r u v t := by
  unfold derivativeFormula normalized
  simp only [pow_succ]
  field_simp [ht, pow_ne_zero r ht] <;> ring

/-- Every derivative's possible zero is governed by one affine equation. -/
theorem derivative_zero_iff (r : ℕ) (u v : ℝ) {t : ℝ} (ht : t ≠ 0) :
    iteratedDeriv r (phase u v) t = 0 ↔ u * t + ((r + 1 : ℕ) : ℝ) * v = 0 := by
  rw [iteratedDeriv_phase r u v ht, derivativeFormula_factor r u v t ht]
  have hc : ((-1 : ℝ) ^ r * (r.factorial : ℝ) / t ^ (r + 1)) ≠ 0 := by
    apply div_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero r (by norm_num)
      · exact_mod_cast Nat.factorial_ne_zero r
    · exact pow_ne_zero (r + 1) ht
  rw [mul_eq_zero, or_iff_right hc]
  unfold normalized
  have hid : u + ((r + 1 : ℕ) : ℝ) * v / t =
      (u * t + ((r + 1 : ℕ) : ℝ) * v) / t := by
    field_simp [ht] <;> ring
  rw [hid, div_eq_zero_iff]
  simp only [ht, or_false]

/-- When the reciprocal coefficient is nonzero, the order-r zero is explicit. -/
theorem derivative_zero_location (r : ℕ) {u v t : ℝ} (hu : u ≠ 0) (ht : t ≠ 0) :
    iteratedDeriv r (phase u v) t = 0 ↔ t = -(((r + 1 : ℕ) : ℝ) * v) / u := by
  rw [derivative_zero_iff r u v ht, eq_div_iff hu]
  constructor <;> intro h <;> nlinarith only [h]

/-- There is at most one zero of each derivative on the positive axis. -/
theorem derivative_zero_unique (r : ℕ) {u v s t : ℝ}
    (hu : u ≠ 0) (hs : 0 < s) (ht : 0 < t)
    (hds : iteratedDeriv r (phase u v) s = 0)
    (hdt : iteratedDeriv r (phase u v) t = 0) : s = t := by
  have h1 := (derivative_zero_location r hu (ne_of_gt hs)).mp hds
  have h2 := (derivative_zero_location r hu (ne_of_gt ht)).mp hdt
  exact h1.trans h2.symm

/-- Two adjacent normalized derivatives recover BOTH reciprocal coefficients. -/
theorem normalized_recovery (r : ℕ) (u v t : ℝ) :
    normalized (r + 1) u v t - normalized r u v t = v / t ∧
    (((r + 2 : ℕ) : ℝ) * normalized r u v t -
      ((r + 1 : ℕ) : ℝ) * normalized (r + 1) u v t) = u := by
  unfold normalized
  push_cast
  constructor <;> ring

/-- A quantitative noncancellation bound; this is NOT an exponential-sum estimate. -/
theorem adjacent_normalized_nondegeneracy (r : ℕ) (u v : ℝ) {t : ℝ} (ht : 0 < t) :
    |u| + |v| / t ≤ (2 * (r : ℝ) + 5) *
      max |normalized r u v t| |normalized (r + 1) u v t| := by
  let A := normalized r u v t
  let B := normalized (r + 1) u v t
  let M := max |A| |B|
  have hA : |A| ≤ M := le_max_left _ _
  have hB : |B| ≤ M := le_max_right _ _
  have hM : 0 ≤ M := le_trans (abs_nonneg A) hA
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hrec := normalized_recovery r u v t
  have hv : |v| / t ≤ 2 * M := by
    have hh : |B - A| ≤ |B| + |A| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le B (-A)
    have heq : B - A = v / t := hrec.1
    rw [heq, abs_div, abs_of_pos ht] at hh
    nlinarith only [hh, hA, hB]
  have hu : |u| ≤ (2 * (r : ℝ) + 3) * M := by
    have hh : |((r + 2 : ℕ) : ℝ) * A - ((r + 1 : ℕ) : ℝ) * B| ≤
        |((r + 2 : ℕ) : ℝ) * A| + |((r + 1 : ℕ) : ℝ) * B| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (((r + 2 : ℕ) : ℝ) * A) (-(((r + 1 : ℕ) : ℝ) * B))
    have heq : (((r + 2 : ℕ) : ℝ) * A) - (((r + 1 : ℕ) : ℝ) * B) = u := hrec.2
    rw [heq, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((r + 2 : ℕ) : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ))] at hh
    have h1 := mul_le_mul_of_nonneg_left hA (show (0 : ℝ) ≤ ((r + 2 : ℕ) : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) by positivity)
    push_cast at hh h1 h2
    nlinarith only [hh, h1, h2]
  change |u| + |v| / t ≤ (2 * (r : ℝ) + 5) * M
  nlinarith only [hu, hv]

/-- Excision away from the explicit critical point gives an actual derivative bound. -/
theorem derivative_lower_away_from_zero (r : ℕ) {u v t η : ℝ}
    (hu : u ≠ 0) (ht : 0 < t) (hη : 0 ≤ η)
    (hdist : η * t ≤ |t - (-(((r + 1 : ℕ) : ℝ) * v) / u)|) :
    (r.factorial : ℝ) * |u| * η / t ^ (r + 1) ≤
      |iteratedDeriv r (phase u v) t| := by
  have hlin : normalized r u v t =
      (u / t) * (t - (-(((r + 1 : ℕ) : ℝ) * v) / u)) := by
    unfold normalized
    field_simp [hu, ne_of_gt ht] <;> ring
  have hn : |u| * η ≤ |normalized r u v t| := by
    rw [hlin, abs_mul, abs_div, abs_of_pos ht]
    have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ |u| / t by positivity)
    have hid : (|u| / t) * (η * t) = |u| * η := by field_simp [ne_of_gt ht] <;> ring
    rw [hid] at hm
    exact hm
  rw [iteratedDeriv_phase r u v (ne_of_gt ht), derivativeFormula_factor r u v t (ne_of_gt ht)]
  rw [abs_mul, abs_div, abs_mul, abs_pow, abs_of_pos (pow_pos ht (r + 1))]
  simp only [abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (r.factorial : ℝ) by positivity)]
  have hm := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ (r.factorial : ℝ) / t ^ (r + 1) by positivity)
  convert hm using 1 <;> ring

#print axioms phase_product
#print axioms phase_product_difference
#print axioms hasDerivAt_reciprocalPower
#print axioms derivativeFormula_hasDerivAt
#print axioms iteratedDeriv_phase
#print axioms derivative_zero_location
#print axioms derivative_zero_unique
#print axioms adjacent_normalized_nondegeneracy
#print axioms derivative_lower_away_from_zero
#check iteratedDeriv_phase
#check derivative_lower_away_from_zero
#eval "RECIPROCAL PHASE 147 END: exact derivatives and zero geometry, NOT prime cancellation"

end Erdos374.ReciprocalPhase147
end



/-!
# Close the sparse branch from one precise reciprocal-prime sampling statement

Working 147. NEW SCRIPTS ARE UNCOMPILED.
The analytic sampler below is an EXPLICIT HYPOTHESIS, not an axiom or a theorem
claimed to be proved here. The module supplies the entire deterministic adapter:
the fixed band, all thresholds, the actual C3 norm, half-open endpoint handling,
the continuous lower bound, and the original sparse-count conclusion.

The source target is Proposition 1.13(ii) of Matomaki--Radziwill--Shao--Tao--
Teravainen, QJM 73 (2022), specialized to epsilon=1/4, A=6, j=2, M=N=b.
- real-valued tests are embedded in the source's complex-valued class;
- norm conventions differ at most by a fixed finite-dimensional constant;
- our interval is (P,2P], not silently identified with [P,2P].
None of those source observations is an imported Lean proof of the sampler.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.SamplingClosure147
open UniformC3_147
open Erdos374.RemainingAnalytic115.RemainingAnalytic127
open Erdos374.RemainingAnalytic115.RemainingAnalytic134
open Erdos374.RemainingAnalytic115.RemainingAnalytic141
open Erdos374.RemainingAnalytic115.RemainingAnalytic142

/-- The half-open prime band used by this sampler. -/
def openPrimeBand (P : ℕ) : Finset ℕ := (Finset.Ioc P (2 * P)).filter Nat.Prime

def openScore (b c P : ℕ) : ℝ :=
  ∑ p ∈ openPrimeBand P, SmoothSparse144.weight b c P p

/-- Reinsert a possible prime at the left endpoint using nonnegativity only. -/
theorem openScore_le_score (b c P : ℕ) :
    openScore b c P ≤ SmoothSparse144.score b c P := by
  unfold openScore SmoothSparse144.score
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo.le, hhi⟩, hprime⟩
  · intro p _hp _hnot
    exact (SmoothSparse144.weight_bounds b c P p).1

theorem openScore_eq_periodicSum (b c P : ℕ) :
    openScore b c P = ∑ p ∈ openPrimeBand P,
      SmoothSparse144.periodicTest b c P ((b : ℝ) / (p : ℝ), (b : ℝ) / (p : ℝ) ^ 2) := by
  unfold openScore
  apply Finset.sum_congr rfl
  intro p hp
  exact SmoothSparse144.weight_eq_periodicTest b c P (Finset.mem_filter.mp hp).2

/-- ONE fixed-logarithmic-saving specialization of the published-type estimate.
UNCONSTRUCTED. The constant precedes P, b and the varying smooth function W.
A definition of this proposition does not prove it. -/
def ReciprocalPrimeSampling : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ P b : ℕ,
    P₀ ≤ P → 2 ≤ P → 1 ≤ b →
    (b : ℝ) ≤ Real.exp ((Real.log (P : ℝ)) ^ ((5 : ℝ) / 4)) →
    ∀ W : (ℝ × ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) W →
      (∀ x y : ℝ, W (x + 1, y) = W (x, y)) →
      (∀ x y : ℝ, W (x, y + 1) = W (x, y)) →
      |(∑ p ∈ openPrimeBand P, W ((b : ℝ) / (p : ℝ), (b : ℝ) / (p : ℝ) ^ 2)) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), W ((b : ℝ) / t, (b : ℝ) / t ^ 2) / Real.log t| ≤
        C * c3Size W * (P : ℝ) / (Real.log (P : ℝ)) ^ 6

/-- No unspecified prime band remains in the adapter. -/
def canonicalBand (X b c : ℕ) : ℕ :=
  ⌈20 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ)⌉₊

/-- Includes both the ceiling error and the scale needed by FullReference146. -/
theorem canonicalBand_geometry {N X a b c : ℕ}
    (hbc : b < c) (hL : 4 ≤ Real.log (X : ℝ))
    (ha : (a : ℝ) ≤ 10 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ))
    (hb : 100 * ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ 2 < (b : ℝ))
    (hbig : N + 16 ≤ c - b) :
    16 ≤ canonicalBand X b c ∧ N ≤ canonicalBand X b c ∧
      a < canonicalBand X b c ∧ c - b < canonicalBand X b c ∧
      16 * canonicalBand X b c ≤ b ∧
      (canonicalBand X b c : ℝ) ≤ 21 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) := by
  have hhpos : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
  have hh1 : (1 : ℝ) ≤ ((c - b : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ c - b by omega)
  have hL1 : 1 ≤ Real.log (X : ℝ) := by linarith
  have hL0 : 0 ≤ Real.log (X : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hL1 hhpos.le
  have hhead : 20 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) ≤
      (canonicalBand X b c : ℝ) := Nat.le_ceil _
  have htail : (canonicalBand X b c : ℝ) <
      20 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hgapR : ((c - b : ℕ) : ℝ) < (canonicalBand X b c : ℝ) := by
    nlinarith only [hhpos, hmul, hhead]
  have hgap : c - b < canonicalBand X b c := by exact_mod_cast hgapR
  have haR : (a : ℝ) < (canonicalBand X b c : ℝ) := by
    nlinarith only [ha, hhead, hmul, hhpos]
  have hupper : (canonicalBand X b c : ℝ) ≤
      21 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) := by
    nlinarith only [htail, hmul, hh1]
  have hlog4 : 4 * Real.log (X : ℝ) ≤ (Real.log (X : ℝ)) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hL) hL0]
  have hscaled := mul_le_mul_of_nonneg_left hlog4
    (show 0 ≤ 100 * ((c - b : ℕ) : ℝ) by positivity)
  have hscaleR : 16 * (canonicalBand X b c : ℝ) ≤ (b : ℝ) := by
    nlinarith only [hupper, hb, hscaled, hmul, hhpos]
  exact ⟨by omega, by omega, by exact_mod_cast haR, hgap,
    by exact_mod_cast hscaleR, hupper⟩

/-- Logarithms compare uniformly under the power-width condition. -/
theorem log_band_scale {X b c : ℕ} {γ : ℝ}
    (hX : 1 ≤ X) (hγ : 0 < γ) (hbc : b < c)
    (hgap : (X : ℝ) ^ γ ≤ ((c - b : ℕ) : ℝ))
    (hP : c - b < canonicalBand X b c) :
    γ * Real.log (X : ℝ) ≤ Real.log (canonicalBand X b c : ℝ) := by
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXP : (X : ℝ) ^ γ ≤ (canonicalBand X b c : ℝ) :=
    le_trans hgap (by exact_mod_cast hP.le)
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hXp γ) hXP
  rw [Real.log_rpow hXp] at hh
  simpa only [mul_comm] using hh

/-- The actual C3 norm in the prescribed band has one constant per fixed gamma. -/
theorem canonical_c3_bound {K γ : ℝ}
    (hK : 0 < K) (hγ : 0 < γ)
    (hbound : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 → ∀ q : Bool,
      c3Size (Smooth144.test δ q) ≤ K / δ ^ 3)
    {X b c : ℕ} (hbc : b < c) (hgapP : c - b < canonicalBand X b c)
    (hPupper : (canonicalBand X b c : ℝ) ≤
      21 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ))
    (hlogs : γ * Real.log (X : ℝ) ≤ Real.log (canonicalBand X b c : ℝ)) :
    c3Size (SmoothSparse144.periodicTest b c (canonicalBand X b c)) ≤
      K * (168 / γ) ^ 3 * (Real.log (canonicalBand X b c : ℝ)) ^ 3 := by
  let P := canonicalBand X b c
  let δ : ℝ := SmoothSparse144.width b c P
  have hh : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
  have hPp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by dsimp [P]; omega)
  have hδ : 0 < δ := by dsimp [δ, SmoothSparse144.width]; positivity
  have hδsmall : δ ≤ 1 / 8 := by
    dsimp [δ, SmoothSparse144.width]
    apply (div_le_iff₀ (show (0 : ℝ) < 8 * (P : ℝ) by positivity)).mpr
    have hhP : ((c - b : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast hgapP
    linarith only [hhP]
  have hinv : δ⁻¹ ≤ 168 * Real.log (X : ℝ) := by
    have hid : δ⁻¹ = 8 * (P : ℝ) / ((c - b : ℕ) : ℝ) := by
      dsimp [δ, SmoothSparse144.width]
      field_simp [ne_of_gt hh, ne_of_gt hPp] <;> ring
    rw [hid]
    apply (div_le_iff₀ hh).mpr
    nlinarith only [hPupper]
  have hL : Real.log (X : ℝ) ≤ Real.log (P : ℝ) / γ := by
    apply (le_div_iff₀ hγ).mpr
    simpa only [mul_comm] using hlogs
  have hscale : δ⁻¹ ≤ (168 / γ) * Real.log (P : ℝ) := by
    have hs := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 168)
    calc
      δ⁻¹ ≤ 168 * Real.log (X : ℝ) := hinv
      _ ≤ 168 * (Real.log (P : ℝ) / γ) := hs
      _ = (168 / γ) * Real.log (P : ℝ) := by ring
  have hpw := pow_le_pow_left₀ (show 0 ≤ δ⁻¹ by positivity) hscale 3
  have hsize := hbound δ hδ hδsmall (decide (c < P ^ 2))
  have hsize' : c3Size (SmoothSparse144.periodicTest b c P) ≤ K * (δ⁻¹) ^ 3 := by
    simpa only [SmoothSparse144.periodicTest, δ, inv_pow, div_eq_mul_inv] using hsize
  have hm := mul_le_mul_of_nonneg_left hpw hK.le
  calc
    _ ≤ K * (δ⁻¹) ^ 3 := hsize'
    _ ≤ K * ((168 / γ) * Real.log (P : ℝ)) ^ 3 := hm
    _ = _ := by ring

/-- This algebraic absorption is independent of the prime-sampling theorem. -/
theorem sampling_error_absorb {D γ P h L y z : ℝ}
    (hD : 0 ≤ D) (hγ : 0 < γ) (hP : 0 < P) (hh : 0 ≤ h)
    (hy : 0 < y) (hz : 0 < z) (hPscale : P ≤ 21 * h * L)
    (hlogscale : γ * L ≤ y) (hzscale : z ≤ 2 * y)
    (hlarge : 26880 * D / γ ≤ y) :
    D * P / y ^ 3 ≤ h / (640 * z) := by
  have hbudget : 26880 * D ≤ γ * y := by
    have hh' := (div_le_iff₀ hγ).mp hlarge
    nlinarith only [hh']
  have hgeom : γ * P ≤ 21 * h * y := by
    have h1 := mul_le_mul_of_nonneg_left hPscale hγ.le
    have h2 := mul_le_mul_of_nonneg_left hlogscale (show 0 ≤ 21 * h by positivity)
    nlinarith only [h1, h2]
  have h1 := mul_le_mul_of_nonneg_right hbudget hP.le
  have h2 := mul_le_mul_of_nonneg_right hgeom hy.le
  have hcore : 1280 * D * P ≤ h * y ^ 2 := by nlinarith only [h1, h2]
  have h3 := mul_le_mul_of_nonneg_right hcore hy.le
  have h4 := mul_le_mul_of_nonneg_left hzscale (show 0 ≤ 640 * D * P by positivity)
  apply (div_le_div_iff₀ (pow_pos hy 3) (show (0 : ℝ) < 640 * z by positivity)).mpr
  nlinarith only [h3, h4]

/-- Polynomially related parameters lie in the published subexponential range.
This is only a range lemma, not a cancellation estimate. -/
theorem frequency_range (γ : ℝ) (hγ : 0 < γ) :
    ∃ N : ℕ, ∀ X P : ℕ, N ≤ X → (X : ℝ) ^ γ ≤ (P : ℝ) →
      (X : ℝ) ≤ Real.exp ((Real.log (P : ℝ)) ^ ((5 : ℝ) / 4)) := by
  let T : ℝ := max 1 ((1 / γ) ^ (4 : ℕ))
  obtain ⟨N, hN⟩ := eventually_log_ge127 (T / γ)
  refine ⟨max N 1, ?_⟩
  intro X P hX hXP
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hPp : (0 : ℝ) < (P : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hXp γ) hXP
  have hlogs := Real.log_le_log (Real.rpow_pos_of_pos hXp γ) hXP
  rw [Real.log_rpow hXp] at hlogs
  have hthreshold : T ≤ Real.log (X : ℝ) * γ := (div_le_iff₀ hγ).mp (hN X hXN)
  have hTy : T ≤ Real.log (P : ℝ) := by linarith only [hthreshold, hlogs]
  have hy1 : 1 ≤ Real.log (P : ℝ) := le_trans (le_max_left _ _) hTy
  have hyp : 0 < Real.log (P : ℝ) := by linarith only [hy1]
  have hyconst : (1 / γ) ^ (4 : ℕ) ≤ Real.log (P : ℝ) := le_trans (le_max_right _ _) hTy
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ (1 / γ) ^ (4 : ℕ))
    hyconst (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hconst : ((1 / γ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = 1 / γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / γ)]
    norm_num
  rw [hconst] at hroot
  have hmul := mul_le_mul_of_nonneg_left hroot hyp.le
  have hpower : (Real.log (P : ℝ)) ^ ((5 : ℝ) / 4) =
      Real.log (P : ℝ) * (Real.log (P : ℝ)) ^ ((1 : ℝ) / 4) := by
    rw [show (5 : ℝ) / 4 = 1 + 1 / 4 by norm_num, Real.rpow_add hyp, Real.rpow_one]
  have hcompare : Real.log (X : ℝ) ≤ Real.log (P : ℝ) / γ := by
    apply (le_div_iff₀ hγ).mpr
    linarith only [hlogs]
  have hfinal : Real.log (X : ℝ) ≤ (Real.log (P : ℝ)) ^ ((5 : ℝ) / 4) := by
    rw [hpower]
    have hid : Real.log (P : ℝ) / γ = Real.log (P : ℝ) * (1 / γ) := by ring
    rw [hid] at hcompare
    exact le_trans hcompare hmul
  have he := Real.exp_le_exp.mpr hfinal
  simpa only [Real.exp_log hXp] using he

/-- The entire original sparse input follows from the stated sampler.
No separate C3, continuous-integral, band-existence or error-absorption premise
is retained. The prime sampler itself is still an explicit argument. -/
theorem sparseSublog_from_sampling (HS : ReciprocalPrimeSampling) : SparseSublogCount141 4 := by
  obtain ⟨C, hC, NS, hS⟩ := HS
  obtain ⟨K, hK, hKbound⟩ := test_c3Size_uniform
  obtain ⟨NI, hNI16, hI⟩ := FullReference146.referenceIntegral_lower320
  intro γ hγ hγ1
  let D : ℝ := C * K * (168 / γ) ^ 3
  have hD : 0 < D := by dsimp [D]; positivity
  let NB : ℕ := max NS NI
  obtain ⟨NG, hNG⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := γ) (C := ((NB + 16 : ℕ) : ℝ)) hγ
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 (max 4 ((26880 * D / γ) / γ))
  obtain ⟨NF, hNF⟩ := frequency_range γ hγ
  refine ⟨max 1 (max NG (max NL NF)), ?_⟩
  intro X a b c hX hab hbc hcX hgap ha hb _hshort
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXG : NG ≤ X := by omega
  have hXL : NL ≤ X := by omega
  have hXF : NF ≤ X := by omega
  have hbig : NB + 16 ≤ c - b := by
    have hr := le_trans (hNG X hXG).le hgap
    exact_mod_cast hr
  have hLL := hNL X hXL
  have hL4 : 4 ≤ Real.log (X : ℝ) := le_trans (le_max_left _ _) hLL
  have hgeo := canonicalBand_geometry hbc hL4 ha hb hbig
  let P : ℕ := canonicalBand X b c
  have hP16 : 16 ≤ P := hgeo.1
  have hPB : NB ≤ P := hgeo.2.1
  have haP : a < P := hgeo.2.2.1
  have hgapP : c - b < P := hgeo.2.2.2.1
  have hscale : 16 * P ≤ b := hgeo.2.2.2.2.1
  have hPupper : (P : ℝ) ≤ 21 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) := hgeo.2.2.2.2.2
  have hPS : NS ≤ P := le_trans (le_max_left _ _) hPB
  have hPI : NI ≤ P := le_trans (le_max_right _ _) hPB
  have hP2 : 2 ≤ P := by omega
  have hPp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hP1R : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
  have hb1 : 1 ≤ b := by nlinarith only [hscale, hP16]
  have hh : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
  have hXP : (X : ℝ) ^ γ ≤ (P : ℝ) := le_trans hgap (by exact_mod_cast hgapP.le)
  have hfreq : (b : ℝ) ≤ Real.exp ((Real.log (P : ℝ)) ^ ((5 : ℝ) / 4)) :=
    le_trans (by exact_mod_cast (show b ≤ X by omega)) (hNF X P hXF hXP)
  have hlogs : γ * Real.log (X : ℝ) ≤ Real.log (P : ℝ) :=
    log_band_scale hX1 hγ hbc hgap hgapP
  have hy : 0 < Real.log (P : ℝ) := Real.log_pos hP1R
  have hz : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by linarith only [hP1R])
  have hzscale : Real.log (2 * (P : ℝ)) ≤ 2 * Real.log (P : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hPp)]
    have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (P : ℝ) by exact_mod_cast hP2)
    linarith only [hl2]
  have hlarge : 26880 * D / γ ≤ Real.log (P : ℝ) := by
    have hreq : (26880 * D / γ) / γ ≤ Real.log (X : ℝ) := le_trans (le_max_right _ _) hLL
    have hm := (div_le_iff₀ hγ).mp hreq
    nlinarith only [hm, hlogs]
  have hδ : 0 < SmoothSparse144.width b c P := by unfold SmoothSparse144.width; positivity
  have hδsmall : SmoothSparse144.width b c P ≤ 1 / 8 := by
    unfold SmoothSparse144.width
    apply (div_le_iff₀ (show (0 : ℝ) < 8 * (P : ℝ) by positivity)).mpr
    have hhP : ((c - b : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast hgapP
    linarith only [hhP]
  have hW : ContDiff ℝ (⊤ : ℕ∞) (SmoothSparse144.periodicTest b c P) :=
    SmoothSparse144.periodicTest_contDiff hbc hgapP
  have hWx : ∀ x y : ℝ, SmoothSparse144.periodicTest b c P (x + 1, y) =
      SmoothSparse144.periodicTest b c P (x, y) := by
    intro x y
    exact Smooth144.test_periodic_fst _ _ x y
  have hWy : ∀ x y : ℝ, SmoothSparse144.periodicTest b c P (x, y + 1) =
      SmoothSparse144.periodicTest b c P (x, y) := by
    intro x y
    exact Smooth144.test_periodic_snd _ _ x y
  have herr := hS P b hPS hP2 hb1 hfreq (SmoothSparse144.periodicTest b c P) hW hWx hWy
  rw [← openScore_eq_periodicSum b c P] at herr
  change |openScore b c P - SmoothSparse144.referenceIntegral b c P| ≤
    C * c3Size (SmoothSparse144.periodicTest b c P) * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 at herr
  have hsize := canonical_c3_bound hK hγ hKbound hbc hgapP hPupper hlogs
  have hnum := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hC.le) hPp.le
  have hnorm := div_le_div_of_nonneg_right hnum (show 0 ≤ (Real.log (P : ℝ)) ^ 6 by positivity)
  have heqid : C * (K * (168 / γ) ^ 3 * (Real.log (P : ℝ)) ^ 3) * (P : ℝ) /
      (Real.log (P : ℝ)) ^ 6 = D * (P : ℝ) / (Real.log (P : ℝ)) ^ 3 := by
    dsimp [D]
    field_simp [ne_of_gt hy] <;> ring
  rw [heqid] at hnorm
  have habsorb := sampling_error_absorb hD.le hγ hPp hh.le hy hz hPupper hlogs hzscale hlarge
  have herrfinal : |openScore b c P - SmoothSparse144.referenceIntegral b c P| ≤
      ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ))) :=
    le_trans herr (le_trans hnorm habsorb)
  have hmain := hI b c P hPI hbc hgapP hscale
  have hlow := neg_abs_le (openScore b c P - SmoothSparse144.referenceIntegral b c P)
  have htwice : ((c - b : ℕ) : ℝ) / (320 * Real.log (2 * (P : ℝ))) =
      2 * (((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ)))) := by ring
  have hscore : ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ))) ≤ openScore b c P := by
    linarith only [hmain, hlow, herrfinal, htwice]
  refine ⟨P, hP2, ?_⟩
  exact le_trans hscore (le_trans (openScore_le_score b c P)
    (SmoothSparse144.score_le_goodCount hbc hP16 haP hgapP))

/-- An alternative FOUR-input endpoint. The standard sampler is still assumed;
PNT, Harman and coarse curves are not constructed by this declaration. -/
theorem candidate_main_from_sampling147
    (HP : PsiMediumPNT134) (HC : CoarseHyperellipticCount141)
    (HF : DensityZero forwardBadIntervals141) (HS : ReciprocalPrimeSampling) : MainStatement :=
  candidate_main_from_mediumPNT141 HP ⟨sparseSublog_from_sampling HS, HF, HC⟩

theorem positive_lower_density_from_sampling147
    (HP : PsiMediumPNT134) (HC : CoarseHyperellipticCount141)
    (HF : DensityZero forwardBadIntervals141) (HS : ReciprocalPrimeSampling) : PositiveLowerDensity D6 :=
  positive_lower_density_from_mediumPNT141 HP ⟨sparseSublog_from_sampling HS, HF, HC⟩

#print axioms openScore_le_score
#print axioms canonicalBand_geometry
#print axioms canonical_c3_bound
#print axioms sampling_error_absorb
#print axioms frequency_range
#print axioms sparseSublog_from_sampling
#print axioms candidate_main_from_sampling147
#check sparseSublog_from_sampling
#check candidate_main_from_sampling147
#print ReciprocalPrimeSampling
#eval "SAMPLING CLOSURE 147 END: four inputs, with the sampler itself still UNPROVED"

end Erdos374.SamplingClosure147
end

#eval "ERDOS374 WORKING UPDATE 147 END — SAMPLER, HARMAN, PNT AND CURVE INPUTS STILL REQUIRED"

/-! Focused Working-148 checkpoints: these must be read together with all errors. -/
#print axioms Erdos374.Vaughan145.high_apply
#print axioms Erdos374.Vaughan145.phaseSum_sub
#print axioms Erdos374.PeriodicAveraging145.periodic_integral_lower
#print axioms Erdos374.PeriodicAveraging145.reciprocal_jacobian_identity
#print axioms Erdos374.PeriodicPrimitive146.primitive_abs_le_mean
#print axioms Erdos374.PeriodicPrimitive146.reciprocal_product_lower
#print axioms Erdos374.SquareMass146.square_coordinate_mass
#print axioms Erdos374.FullReference146.referenceIntegral_lower
#print axioms Erdos374.UniformC3_147.test_c3Size_uniform
#print axioms Erdos374.ReciprocalPhase147.iteratedDeriv_phase
#print axioms Erdos374.SamplingClosure147.sparseSublog_from_sampling
#print axioms Erdos374.SamplingClosure147.candidate_main_from_sampling147
#check Erdos374.SamplingClosure147.candidate_main_from_sampling147
#eval "ERDOS374 WORKING UPDATE 148 END — SAMPLER, HARMAN, PNT, CURVE INPUTS STILL REQUIRED"

/-!
Polynomial-range sampling adapter for Repair 148.

This file is an APPENDABLE SNIPPET: concatenate it after the complete repaired
Erdos374_Repair148.lean source (which already imports Mathlib). No new axiom or
analytic theorem is asserted here. PolynomialReciprocalPrimeSampling is still
an explicit unproved premise. The result reduces the required frequency range,
so a fixed derivative order depending on gamma may suffice in a future proof.

Compilation status: pending integration with the repaired base file.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.SamplingPolynomial149
open Erdos374.UniformC3_147
open Erdos374.SamplingClosure147
open Erdos374.RemainingAnalytic115.RemainingAnalytic127
open Erdos374.RemainingAnalytic115.RemainingAnalytic134
open Erdos374.RemainingAnalytic115.RemainingAnalytic141
open Erdos374.RemainingAnalytic115.RemainingAnalytic142

/-- Sampling only in each fixed polynomial range. The constant and threshold
may depend on gamma, but must be uniform in P, b and W. This proposition remains
UNPROVED; it is a weaker analytic target, not a new unconditional certificate. -/
def PolynomialReciprocalPrimeSampling : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ P b : ℕ,
    P₀ ≤ P → 2 ≤ P → 1 ≤ b →
    (b : ℝ) ^ γ ≤ (P : ℝ) →
    ∀ W : (ℝ × ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) W →
      (∀ x y : ℝ, W (x + 1, y) = W (x, y)) →
      (∀ x y : ℝ, W (x, y + 1) = W (x, y)) →
      |(∑ p ∈ openPrimeBand P, W ((b : ℝ) / (p : ℝ), (b : ℝ) / (p : ℝ) ^ 2)) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), W ((b : ℝ) / t, (b : ℝ) / t ^ 2) / Real.log t| ≤
        C * c3Size W * (P : ℝ) / (Real.log (P : ℝ)) ^ 6

/-- The original subexponential-range sampler implies the weaker target.
The finite range b < NF is handled by b <= P once P is large enough. -/
theorem polynomial_sampling_of_sampling (HS : ReciprocalPrimeSampling) :
    PolynomialReciprocalPrimeSampling := by
  obtain ⟨C, hC, NS, hS⟩ := HS
  intro γ hγ
  obtain ⟨NF, hNF⟩ := frequency_range γ hγ
  obtain ⟨N1, hN1⟩ := frequency_range 1 (by norm_num)
  refine ⟨C, hC, max NS (max NF N1), ?_⟩
  intro P b hP hP2 hb1 hpoly W hW hWx hWy
  have hPS : NS ≤ P := by omega
  have hPF : NF ≤ P := by omega
  have hP1 : N1 ≤ P := by omega
  have hfreq : (b : ℝ) ≤ Real.exp ((Real.log (P : ℝ)) ^ ((5 : ℝ) / 4)) := by
    by_cases hbP : b ≤ P
    · have hself : (P : ℝ) ^ (1 : ℝ) ≤ (P : ℝ) := by simp
      exact le_trans (by exact_mod_cast hbP) (hN1 P P hP1 hself)
    · exact hNF b P (by omega) hpoly
  exact hS P b hPS hP2 hb1 hfreq W hW hWx hWy

/-- The entire sparse input follows from polynomial-range sampling. C and the
band threshold are chosen only after gamma, matching its quantifier order. -/
theorem sparseSublog_from_polynomial_sampling (HS : PolynomialReciprocalPrimeSampling) : SparseSublogCount141 4 := by
  intro γ hγ hγ1
  obtain ⟨C, hC, NS, hS⟩ := HS γ hγ
  obtain ⟨K, hK, hKbound⟩ := test_c3Size_uniform
  obtain ⟨NI, hNI16, hI⟩ := FullReference146.referenceIntegral_lower320
  let D : ℝ := C * K * (168 / γ) ^ 3
  have hD : 0 < D := by dsimp [D]; positivity
  let NB : ℕ := max NS NI
  obtain ⟨NG, hNG⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := γ) (C := ((NB + 16 : ℕ) : ℝ)) hγ
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 (max 4 ((26880 * D / γ) / γ))
  refine ⟨max 1 (max NG NL), ?_⟩
  intro X a b c hX hab hbc hcX hgap ha hb _hshort
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXG : NG ≤ X := by omega
  have hXL : NL ≤ X := by omega
  have hbig : NB + 16 ≤ c - b := by
    have hr := le_trans (hNG X hXG).le hgap
    exact_mod_cast hr
  have hLL := hNL X hXL
  have hL4 : 4 ≤ Real.log (X : ℝ) := le_trans (le_max_left _ _) hLL
  have hgeo := canonicalBand_geometry hbc hL4 ha hb hbig
  let P : ℕ := canonicalBand X b c
  have hP16 : 16 ≤ P := hgeo.1
  have hPB : NB ≤ P := hgeo.2.1
  have haP : a < P := hgeo.2.2.1
  have hgapP : c - b < P := hgeo.2.2.2.1
  have hscale : 16 * P ≤ b := hgeo.2.2.2.2.1
  have hPupper : (P : ℝ) ≤ 21 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) := hgeo.2.2.2.2.2
  have hPS : NS ≤ P := le_trans (le_max_left _ _) hPB
  have hPI : NI ≤ P := le_trans (le_max_right _ _) hPB
  have hP2 : 2 ≤ P := by omega
  have hPp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hP1R : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
  have hb1 : 1 ≤ b := by nlinarith only [hscale, hP16]
  have hh : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
  have hXP : (X : ℝ) ^ γ ≤ (P : ℝ) := le_trans hgap (by exact_mod_cast hgapP.le)
  have hfreq : (b : ℝ) ^ γ ≤ (P : ℝ) :=
    le_trans (Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (b : ℝ))
      (by exact_mod_cast (show b ≤ X by omega)) hγ.le) hXP
  have hlogs : γ * Real.log (X : ℝ) ≤ Real.log (P : ℝ) :=
    log_band_scale hX1 hγ hbc hgap hgapP
  have hy : 0 < Real.log (P : ℝ) := Real.log_pos hP1R
  have hz : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by linarith only [hP1R])
  have hzscale : Real.log (2 * (P : ℝ)) ≤ 2 * Real.log (P : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hPp)]
    have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (P : ℝ) by exact_mod_cast hP2)
    linarith only [hl2]
  have hlarge : 26880 * D / γ ≤ Real.log (P : ℝ) := by
    have hreq : (26880 * D / γ) / γ ≤ Real.log (X : ℝ) := le_trans (le_max_right _ _) hLL
    have hm := (div_le_iff₀ hγ).mp hreq
    nlinarith only [hm, hlogs]
  have hδ : 0 < SmoothSparse144.width b c P := by unfold SmoothSparse144.width; positivity
  have hδsmall : SmoothSparse144.width b c P ≤ 1 / 8 := by
    unfold SmoothSparse144.width
    apply (div_le_iff₀ (show (0 : ℝ) < 8 * (P : ℝ) by positivity)).mpr
    have hhP : ((c - b : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast hgapP
    linarith only [hhP]
  have hW : ContDiff ℝ (⊤ : ℕ∞) (SmoothSparse144.periodicTest b c P) :=
    SmoothSparse144.periodicTest_contDiff hbc hgapP
  have hWx : ∀ x y : ℝ, SmoothSparse144.periodicTest b c P (x + 1, y) =
      SmoothSparse144.periodicTest b c P (x, y) := by
    intro x y
    exact Smooth144.test_periodic_fst _ _ x y
  have hWy : ∀ x y : ℝ, SmoothSparse144.periodicTest b c P (x, y + 1) =
      SmoothSparse144.periodicTest b c P (x, y) := by
    intro x y
    exact Smooth144.test_periodic_snd _ _ x y
  have herr := hS P b hPS hP2 hb1 hfreq (SmoothSparse144.periodicTest b c P) hW hWx hWy
  rw [← openScore_eq_periodicSum b c P] at herr
  change |openScore b c P - SmoothSparse144.referenceIntegral b c P| ≤
    C * c3Size (SmoothSparse144.periodicTest b c P) * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 at herr
  have hsize := canonical_c3_bound hK hγ hKbound hbc hgapP hPupper hlogs
  have hnum := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hC.le) hPp.le
  have hnorm := div_le_div_of_nonneg_right hnum (show 0 ≤ (Real.log (P : ℝ)) ^ 6 by positivity)
  have heqid : C * (K * (168 / γ) ^ 3 * (Real.log (P : ℝ)) ^ 3) * (P : ℝ) /
      (Real.log (P : ℝ)) ^ 6 = D * (P : ℝ) / (Real.log (P : ℝ)) ^ 3 := by
    dsimp [D]
    field_simp [ne_of_gt hy] <;> ring
  rw [heqid] at hnorm
  have habsorb := sampling_error_absorb hD.le hγ hPp hh.le hy hz hPupper hlogs hzscale hlarge
  have herrfinal : |openScore b c P - SmoothSparse144.referenceIntegral b c P| ≤
      ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ))) :=
    le_trans herr (le_trans hnorm habsorb)
  have hmain := hI b c P hPI hbc hgapP hscale
  have hlow := neg_abs_le (openScore b c P - SmoothSparse144.referenceIntegral b c P)
  have htwice : ((c - b : ℕ) : ℝ) / (320 * Real.log (2 * (P : ℝ))) =
      2 * (((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ)))) := by ring
  have hscore : ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ))) ≤ openScore b c P := by
    linarith only [hmain, hlow, herrfinal, htwice]
  refine ⟨P, hP2, ?_⟩
  exact le_trans hscore (le_trans (openScore_le_score b c P)
    (SmoothSparse144.score_le_goodCount hbc hP16 haP hgapP))

/-- The original endpoint is preserved with a weaker range requirement.
PNT, short intervals, curves, and polynomial prime sampling are still premises. -/
theorem candidate_main_from_polynomial_sampling149
    (HP : PsiMediumPNT134) (HC : CoarseHyperellipticCount141)
    (HF : DensityZero forwardBadIntervals141) (HS : PolynomialReciprocalPrimeSampling) :
    MainStatement :=
  candidate_main_from_mediumPNT141 HP
    ⟨sparseSublog_from_polynomial_sampling HS, HF, HC⟩

theorem positive_lower_density_from_polynomial_sampling149
    (HP : PsiMediumPNT134) (HC : CoarseHyperellipticCount141)
    (HF : DensityZero forwardBadIntervals141) (HS : PolynomialReciprocalPrimeSampling) :
    PositiveLowerDensity D6 :=
  positive_lower_density_from_mediumPNT141 HP
    ⟨sparseSublog_from_polynomial_sampling HS, HF, HC⟩

#print axioms polynomial_sampling_of_sampling
#print axioms sparseSublog_from_polynomial_sampling
#print axioms candidate_main_from_polynomial_sampling149
#print PolynomialReciprocalPrimeSampling

end Erdos374.SamplingPolynomial149
end

/- This is an appendable audit block, not an unconditional theorem. -/
run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.PeriodicPrimitive146.reciprocal_product_lower,
    ``Erdos374.SquareMass146.square_coordinate_mass,
    ``Erdos374.FullReference146.referenceIntegral_lower,
    ``Erdos374.SamplingClosure147.candidate_main_from_sampling147,
    ``Erdos374.SamplingPolynomial149.candidate_main_from_polynomial_sampling149]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#check Erdos374.SamplingPolynomial149.candidate_main_from_polynomial_sampling149
#print axioms Erdos374.SamplingPolynomial149.candidate_main_from_polynomial_sampling149
#eval "REPAIR 149 AUDIT REACHED: conditional endpoint; four analytic inputs remain"


end Update150_Component_1
/- END COMPONENT: Erdos374_Repair149.lean -/

/- BEGIN COMPONENT: Erdos374_SamplerConsequences149.lean -/
section Update150_Component_2


/-!
Constant-test consequences for the Repair 149 source and polynomial sampler.
The constant-test consequence below is conditional on the polynomial sampler.
It is an ordinary quantitative dyadic prime-counting estimate, with the C3
norm evaluated exactly; no additional analytic premise is introduced.
Compilation status: the standalone exact-definition probe compiled with exit 0
on Lean 4.35.0-rc2. Its three axiom reports contain only propext, Classical.choice,
and Quot.sound. Integration with the full repaired source remains to be checked.
-/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.UniformC3_147

/-- All positive-order derivatives of a constant vanish. -/
theorem c3Size_const (a : ℝ) : c3Size (fun _ : ℝ × ℝ => a) = |a| := by
  simp [c3Size, Finset.sum_range_succ, iteratedFDeriv_succ_const, Real.norm_eq_abs]

@[simp]
theorem c3Size_one : c3Size (fun _ : ℝ × ℝ => (1 : ℝ)) = 1 := by
  simpa using c3Size_const 1

end Erdos374.UniformC3_147

namespace Erdos374.SamplingClosure147

/-- The half-open band has exactly the primes counted between the endpoints. -/
theorem openPrimeBand_eq_primesLE_sdiff (P : ℕ) :
    openPrimeBand P = Nat.primesLE (2 * P) \ Nat.primesLE P := by
  ext p
  simp only [openPrimeBand, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    refine ⟨⟨hhi, hp⟩, ?_⟩
    rintro ⟨hle, _⟩
    omega
  · rintro ⟨⟨hhi, hp⟩, hnot⟩
    refine ⟨⟨?_, hhi⟩, hp⟩
    by_contra h
    apply hnot
    exact ⟨by omega, hp⟩

theorem openPrimeBand_card (P : ℕ) :
    (openPrimeBand P).card = Nat.primeCounting (2 * P) - Nat.primeCounting P := by
  rw [openPrimeBand_eq_primesLE_sdiff,
    Finset.card_sdiff_of_subset (Nat.primesLE_mono (by omega : P ≤ 2 * P))]
  simp

theorem openPrimeBand_card_real (P : ℕ) :
    ((openPrimeBand P).card : ℝ) =
      (Nat.primeCounting (2 * P) : ℝ) - (Nat.primeCounting P : ℝ) := by
  rw [openPrimeBand_card, Nat.cast_sub
    (Nat.monotone_primeCounting (by omega : P ≤ 2 * P))]

end Erdos374.SamplingClosure147

namespace Erdos374.SamplingPolynomial149
open Erdos374.UniformC3_147 Erdos374.SamplingClosure147

/-- The constant Fourier mode supplies a quantitative dyadic prime-counting
estimate. The sampler itself remains an explicit hypothesis. -/
theorem dyadic_primeCount_from_polynomial_sampling
    (HS : PolynomialReciprocalPrimeSampling) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → 2 ≤ P →
      |(Nat.primeCounting (2 * P) : ℝ) - (Nat.primeCounting P : ℝ) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), (1 : ℝ) / Real.log t| ≤
        C * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 := by
  obtain ⟨C, hC, P₀, hS⟩ := HS 1 (by norm_num)
  refine ⟨C, hC, P₀, ?_⟩
  intro P hP hP2
  have hfreq : ((1 : ℕ) : ℝ) ^ (1 : ℝ) ≤ (P : ℝ) := by
    norm_num only [Nat.cast_one, Real.one_rpow]
    have hcast : ((1 : ℕ) : ℝ) ≤ (P : ℝ) :=
      Nat.cast_le.mpr (show 1 ≤ P by omega)
    simpa only [Nat.cast_one] using hcast
  have h := hS P 1 hP hP2 (by norm_num) hfreq
    (fun _ : ℝ × ℝ => (1 : ℝ)) contDiff_const
    (by intro x y; rfl) (by intro x y; rfl)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, c3Size_one,
    openPrimeBand_card_real] using h

/-- The same concrete consequence is available from the original sampler. -/
theorem dyadic_primeCount_from_sampling (HS : ReciprocalPrimeSampling) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → 2 ≤ P →
      |(Nat.primeCounting (2 * P) : ℝ) - (Nat.primeCounting P : ℝ) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), (1 : ℝ) / Real.log t| ≤
        C * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 :=
  dyadic_primeCount_from_polynomial_sampling (polynomial_sampling_of_sampling HS)

#print axioms Erdos374.UniformC3_147.c3Size_const
#print axioms Erdos374.SamplingClosure147.openPrimeBand_card_real
#print axioms dyadic_primeCount_from_polynomial_sampling
#print axioms dyadic_primeCount_from_sampling
#check dyadic_primeCount_from_polynomial_sampling
#check dyadic_primeCount_from_sampling

end Erdos374.SamplingPolynomial149
end


end Update150_Component_2
/- END COMPONENT: Erdos374_SamplerConsequences149.lean -/

/- BEGIN COMPONENT: SamplerNextTheta.lean -/
section Update150_Component_3


/-!
The complete endpoint only needs logarithm-squared Chebyshev theta accuracy
once polynomial reciprocal-prime sampling is available. This module proves
the reduction; it does not assert either remaining analytic statement.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.SamplerNext150
open Erdos374.RemainingAnalytic115
open Erdos374.RemainingAnalytic115.RemainingAnalytic127
open Erdos374.RemainingAnalytic115.RemainingAnalytic130
open Erdos374.RemainingAnalytic115.RemainingAnalytic133
open Erdos374.RemainingAnalytic115.RemainingAnalytic135
open Erdos374.RemainingAnalytic115.RemainingAnalytic141
open Erdos374.UniformC3_147 Erdos374.SamplingClosure147 Erdos374.SamplingPolynomial149

/-- The previous sparse adapter did not use its sublogarithmic-width hypothesis.
The same quantitative estimates supply the full sparse good-prime count. -/
theorem sparseGoodPrimeCount_from_polynomial_sampling150 (HS : PolynomialReciprocalPrimeSampling) : SparseGoodPrimeCount127 := by
  intro γ hγ hγ1
  obtain ⟨C, hC, NS, hS⟩ := HS γ hγ
  obtain ⟨K, hK, hKbound⟩ := test_c3Size_uniform
  obtain ⟨NI, hNI16, hI⟩ := FullReference146.referenceIntegral_lower320
  let D : ℝ := C * K * (168 / γ) ^ 3
  have hD : 0 < D := by dsimp [D]; positivity
  let NB : ℕ := max NS NI
  obtain ⟨NG, hNG⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := γ) (C := ((NB + 16 : ℕ) : ℝ)) hγ
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 (max 4 ((26880 * D / γ) / γ))
  refine ⟨max 1 (max NG NL), ?_⟩
  intro X a b c hX hab hbc hcX hgap ha hb
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXG : NG ≤ X := by omega
  have hXL : NL ≤ X := by omega
  have hbig : NB + 16 ≤ c - b := by
    have hr := le_trans (hNG X hXG).le hgap
    exact_mod_cast hr
  have hLL := hNL X hXL
  have hL4 : 4 ≤ Real.log (X : ℝ) := le_trans (le_max_left _ _) hLL
  have hgeo := canonicalBand_geometry hbc hL4 ha hb hbig
  let P : ℕ := canonicalBand X b c
  have hP16 : 16 ≤ P := hgeo.1
  have hPB : NB ≤ P := hgeo.2.1
  have haP : a < P := hgeo.2.2.1
  have hgapP : c - b < P := hgeo.2.2.2.1
  have hscale : 16 * P ≤ b := hgeo.2.2.2.2.1
  have hPupper : (P : ℝ) ≤ 21 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) := hgeo.2.2.2.2.2
  have hPS : NS ≤ P := le_trans (le_max_left _ _) hPB
  have hPI : NI ≤ P := le_trans (le_max_right _ _) hPB
  have hP2 : 2 ≤ P := by omega
  have hPp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hP1R : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
  have hb1 : 1 ≤ b := by nlinarith only [hscale, hP16]
  have hh : (0 : ℝ) < ((c - b : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hbc
  have hXP : (X : ℝ) ^ γ ≤ (P : ℝ) := le_trans hgap (by exact_mod_cast hgapP.le)
  have hfreq : (b : ℝ) ^ γ ≤ (P : ℝ) :=
    le_trans (Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (b : ℝ))
      (by exact_mod_cast (show b ≤ X by omega)) hγ.le) hXP
  have hlogs : γ * Real.log (X : ℝ) ≤ Real.log (P : ℝ) :=
    log_band_scale hX1 hγ hbc hgap hgapP
  have hy : 0 < Real.log (P : ℝ) := Real.log_pos hP1R
  have hz : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by linarith only [hP1R])
  have hzscale : Real.log (2 * (P : ℝ)) ≤ 2 * Real.log (P : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hPp)]
    have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (P : ℝ) by exact_mod_cast hP2)
    linarith only [hl2]
  have hlarge : 26880 * D / γ ≤ Real.log (P : ℝ) := by
    have hreq : (26880 * D / γ) / γ ≤ Real.log (X : ℝ) := le_trans (le_max_right _ _) hLL
    have hm := (div_le_iff₀ hγ).mp hreq
    nlinarith only [hm, hlogs]
  have hδ : 0 < SmoothSparse144.width b c P := by unfold SmoothSparse144.width; positivity
  have hδsmall : SmoothSparse144.width b c P ≤ 1 / 8 := by
    unfold SmoothSparse144.width
    apply (div_le_iff₀ (show (0 : ℝ) < 8 * (P : ℝ) by positivity)).mpr
    have hhP : ((c - b : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast hgapP
    linarith only [hhP]
  have hW : ContDiff ℝ (⊤ : ℕ∞) (SmoothSparse144.periodicTest b c P) :=
    SmoothSparse144.periodicTest_contDiff hbc hgapP
  have hWx : ∀ x y : ℝ, SmoothSparse144.periodicTest b c P (x + 1, y) =
      SmoothSparse144.periodicTest b c P (x, y) := by
    intro x y
    exact Smooth144.test_periodic_fst _ _ x y
  have hWy : ∀ x y : ℝ, SmoothSparse144.periodicTest b c P (x, y + 1) =
      SmoothSparse144.periodicTest b c P (x, y) := by
    intro x y
    exact Smooth144.test_periodic_snd _ _ x y
  have herr := hS P b hPS hP2 hb1 hfreq (SmoothSparse144.periodicTest b c P) hW hWx hWy
  rw [← openScore_eq_periodicSum b c P] at herr
  change |openScore b c P - SmoothSparse144.referenceIntegral b c P| ≤
    C * c3Size (SmoothSparse144.periodicTest b c P) * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 at herr
  have hsize := canonical_c3_bound hK hγ hKbound hbc hgapP hPupper hlogs
  have hnum := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hC.le) hPp.le
  have hnorm := div_le_div_of_nonneg_right hnum (show 0 ≤ (Real.log (P : ℝ)) ^ 6 by positivity)
  have heqid : C * (K * (168 / γ) ^ 3 * (Real.log (P : ℝ)) ^ 3) * (P : ℝ) /
      (Real.log (P : ℝ)) ^ 6 = D * (P : ℝ) / (Real.log (P : ℝ)) ^ 3 := by
    dsimp [D]
    field_simp [ne_of_gt hy] <;> ring
  rw [heqid] at hnorm
  have habsorb := sampling_error_absorb hD.le hγ hPp hh.le hy hz hPupper hlogs hzscale hlarge
  have herrfinal : |openScore b c P - SmoothSparse144.referenceIntegral b c P| ≤
      ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ))) :=
    le_trans herr (le_trans hnorm habsorb)
  have hmain := hI b c P hPI hbc hgapP hscale
  have hlow := neg_abs_le (openScore b c P - SmoothSparse144.referenceIntegral b c P)
  have htwice : ((c - b : ℕ) : ℝ) / (320 * Real.log (2 * (P : ℝ))) =
      2 * (((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ)))) := by ring
  have hscore : ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * (P : ℝ))) ≤ openScore b c P := by
    linarith only [hmain, hlow, herrfinal, htwice]
  refine ⟨P, hP2, ?_⟩
  exact le_trans hscore (le_trans (openScore_le_score b c P)
    (SmoothSparse144.score_le_goodCount hbc hP16 haP hgapP))


theorem legalAnchorLargeL_from_theta150 (HT : ThetaLogSqRemainder127)
    (HC : CoarseHyperellipticCount141) : RemainingAnalytic38.LegalAnchorTupleBoundLargeL := by
  have htheta := HT
  have hSupply := RemainingAnalytic93.auxiliaryPrimeSupply_from_thetaGap93
    (dyadicThetaGap_from_dense127 (denseTopThetaMass_from_thetaRemainder127 htheta))
  have hEnergy := RemainingAnalytic92.analyticLargeSieveEnergy_from_classical92
    classicalPrimeAdditiveLargeSieve_proved135
  intro α η A0 hα hη hcond hA0
  obtain ⟨cp, hcp, Np, hPrimeSupply⟩ := hSupply
  obtain ⟨Cls, hCls, Nls, hLargeSieve⟩ := hEnergy
  obtain ⟨Ng, hGood⟩ := coarseAuxiliaryGood141 α η A0 hα hη hcond hA0
  let K : ℝ := 3 * Cls / cp
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, Ng, max 2 (max Np Nls), ?_⟩
  intro X r a j t h ell hX hLlarge hr1 hrα hj hjr hh hell ht hnp hH ha
  let L : ℕ := X / r
  let T : Finset ℕ := RemainingAnalytic28.AnchorSquareArgs a r j t h ell L
  let J : ℝ := (RemainingAnalytic28.AnchorSquareArgCount a r j t h ell L : ℝ)
  let E : ℝ := ∑ lam ∈ RemainingAnalytic37.auxiliaryPrimes L,
    RemainingAnalytic37.residueEnergy T lam
  let Q : ℝ := ((RemainingAnalytic37.auxiliaryPrimes L).card : ℝ)
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hLlarge
  have hLp : Np ≤ L :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLlarge)
  have hLls : Nls ≤ L :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLlarge)
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (show 1 < L by omega)
  have hlocal : ∀ lam ∈ RemainingAnalytic37.auxiliaryPrimes L,
      J ^ 2 / 3 ≤ RemainingAnalytic37.residueEnergy T lam := by
    intro lam hlam
    have hp : lam.Prime := (Finset.mem_filter.mp hlam).2.1
    have hgood := hGood X r a h ell lam hX hr1 hrα hh hell hH ha hlam
    have hres := coarse_squareResidueRestriction141 HC hj hjr hh hell ht hnp hp
      hgood.1 hgood.2.1 hgood.2.2
    have himage := RemainingAnalytic37.anchor_residue_image_card_le
      RemainingAnalytic39.squareArgumentReducesMod_proved
      (a := a) (r := r) (j := j) (t := t) (h := h) (ell := ell) (L := L) hp
    exact RemainingAnalytic37.residueEnergy_lower_of_support T lam
      (RemainingAnalytic37.AnchorSquareResidueCount a r j t h ell lam) himage hres
  have hLower : Q * J ^ 2 / 3 ≤ E := by
    have hsum := Finset.sum_le_sum hlocal
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_div_assoc] using hsum
  have hTsub : T ⊆ Finset.Icc 1 L :=
    RemainingAnalytic38.anchorSquareArgs_subset_Icc a r j t h ell L
  have hUpper : E ≤ Cls * (L : ℝ) * J := hLargeSieve L hLls T hTsub
  have hSupply' : cp * Real.sqrt (L : ℝ) / Real.log (L : ℝ) ≤ Q := hPrimeSupply L hLp
  have hJnonneg : 0 ≤ J := by dsimp [J]; positivity
  have hSolve := RemainingAnalytic37.solve_energy_squeeze
    hJnonneg hLreal hcp hCls.le hSupply' hLower hUpper
  simpa only [K, L, J] using hSolve

/-- The anchor sieve uses only the theta logarithm-squared consequence of PNT. -/
theorem uniformAnchor_from_theta150 (HT : ThetaLogSqRemainder127)
    (HC : CoarseHyperellipticCount141) : Tasks.UniformAnchorSieve :=
  RemainingAnalytic54.anchorUniform_from_growth_global54
    (factorial_growth_of_log_q (logQGrowth_from_theta130 HT))
    (RemainingAnalytic44.legalAnchorTupleBoundGlobal_from_largeL
      (legalAnchorLargeL_from_theta150 HT HC))

/-- Rebuild the original analytic core using the weaker quantitative PNT input.
The sampler supplies the full sparse region, so the stronger log-power
estimates formerly used to fill the wider sparse region are unnecessary. -/
noncomputable def core18_from_theta_and_polynomial_sampling150
    (HT : ThetaLogSqRemainder127) (HC : CoarseHyperellipticCount141)
    (HF : DensityZero forwardBadIntervals141) (HS : PolynomialReciprocalPrimeSampling) :
    AnalyticCore18 := by
  let hLim := AFiniteDensityLimit_from_theta133 HT
  let hTail := RemainingAnalytic131.AUniformTail_from_theta131 HT
  let hApprox := A_approximation_of_limit_tail hLim hTail
  have hAdensity : HasDensity A hApprox.delta := A_density_of_approximation hApprox
  have hPNT := primeCountRelativePNT_from_theta130 HT
  have hLogQ := logQGrowth_from_theta130 HT
  have hGrowth := factorial_growth_of_log_q hLogQ
  have hB : HasDensity (B alpha) (densityConstant hApprox.delta) :=
    bDensity_from_corrected_count130 hLim hTail hPNT bareCofactorMassLimit_proved130
      (cofactorIntegerCountCorrected_from_growth130 hLogQ) hAdensity
  have hDenseTheta := denseTopThetaMass_from_thetaRemainder127 HT
  have hDense := denseBranch_from_topIntervalMass
    (denseTopIntervalPrimeMass_from_logMass115
      (RemainingAnalytic119.denseTopLogPrimeMass_from_theta119 hDenseTheta))
  have hSparse := sparseWeightedTransfer_from_count127
    (sparseGoodPrimeCount_from_polynomial_sampling150 HS)
  have hBad := harman_bad_density_from_forward141 HF
  exact {
    deltaA := hApprox.delta
    deltaA_pos := hApprox.delta_pos
    A_density := hAdensity
    B_density := hB
    prime_zero := prime_zero_of_count_decay (primeCountDecay_from_relative130 hPNT)
    short_second := harman_to_secondLargest_proved (harman_from_bad_density127 hBad)
    factorial_growth := hGrowth
    interval_comparison := RemainingAnalytic44.intervalComparison_from_hardened hDense hSparse hGrowth
    uniform_anchor := uniformAnchor_from_theta150 HT HC
  }

/-- Conditional endpoint with logarithm-squared theta accuracy in place of
medium exponential PNT. All remaining premises are visible arguments. -/
theorem candidate_main_from_theta_and_polynomial_sampling150
    (HT : ThetaLogSqRemainder127) (HC : CoarseHyperellipticCount141)
    (HF : DensityZero forwardBadIntervals141) (HS : PolynomialReciprocalPrimeSampling) :
    MainStatement :=
  candidate_main_from_analytic_core18
    (core18_from_theta_and_polynomial_sampling150 HT HC HF HS)

theorem positive_lower_density_from_theta_and_polynomial_sampling150
    (HT : ThetaLogSqRemainder127) (HC : CoarseHyperellipticCount141)
    (HF : DensityZero forwardBadIntervals141) (HS : PolynomialReciprocalPrimeSampling) :
    PositiveLowerDensity D6 :=
  positive_lower_density_from_analytic_core18
    (core18_from_theta_and_polynomial_sampling150 HT HC HF HS)

#check candidate_main_from_theta_and_polynomial_sampling150
#print axioms sparseGoodPrimeCount_from_polynomial_sampling150
#print axioms legalAnchorLargeL_from_theta150
#print axioms uniformAnchor_from_theta150
#print axioms core18_from_theta_and_polynomial_sampling150
#print axioms candidate_main_from_theta_and_polynomial_sampling150
#print axioms positive_lower_density_from_theta_and_polynomial_sampling150

run_cmd do
  let targets : List Lean.Name := [
    ``sparseGoodPrimeCount_from_polynomial_sampling150,
    ``legalAnchorLargeL_from_theta150,
    ``uniformAnchor_from_theta150,
    ``candidate_main_from_theta_and_polynomial_sampling150,
    ``positive_lower_density_from_theta_and_polynomial_sampling150]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.SamplerNext150
end




end Update150_Component_3
/- END COMPONENT: SamplerNextTheta.lean -/

/- BEGIN COMPONENT: PNTMathlib149.lean -/
section Update150_Component_4
/- One-process compatibility probe of the 14-module MediumPNT dependency closure.
   Source modules remain separate and authoritative in work/pnt-port.
   Only imports/file scopes are consolidated; theorem statements are unchanged. -/
                










































set_option autoImplicit false
set_option maxHeartbeats 2400000
#eval "PNT FLAT PROBE: Lean 4.35.0-rc2"

/- BEGIN SOURCE MODULE: PrimeNumberTheoremAnd.Auxiliary -/
section Flat_PrimeNumberTheoremAnd_Auxiliary
/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
### Auxiliary lemmas
-/

namespace Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma deriv_ofReal (x : ℝ) : deriv ofReal x = 1 :=
  (hasDerivAt_ofReal x).deriv

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

lemma Differentiable.comp_ofReal {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ (fun x : ℝ ↦ e x) :=
  fun _ ↦ h.differentiableAt.comp_ofReal

lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt

lemma Differentiable.ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) :=
  fun _ ↦ hf.differentiableAt.ofReal_comp

open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]

end Flat_PrimeNumberTheoremAnd_Auxiliary
#eval "COMPLETED PrimeNumberTheoremAnd.Auxiliary"


/- BEGIN SOURCE MODULE: PrimeNumberTheoremAnd.MellinCalculus -/
section Flat_PrimeNumberTheoremAnd_MellinCalculus









end Flat_PrimeNumberTheoremAnd_MellinCalculus
end Update150_Component_4
end Update151_Component_1
end Update152_Component_1

end
