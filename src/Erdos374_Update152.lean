/- Part 7 of 7 of `Erdos374_Update152` (split for the 10,000-line limit); continues `Erdos374_Update152_Part6`. -/
module

public import Erdos374_Update152_Part6

@[expose] public section


section Update152_Component_1
section Update151_Component_2
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Erdos374.WeightedPrimeSampling151
open SamplingClosure147 SamplerConstantClosed150

/-- Unconditional quantitative sampling for every continuously differentiable
complex weight. The threshold depends only on the requested logarithmic saving;
the test function enters solely through its sup norm and total variation. -/
theorem weighted_prime_sampling (A : ℕ) :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → ∀ (f f' : ℝ → ℂ) (M V : ℝ),
      (∀ t ∈ Set.Icc (P : ℝ) (2 * (P : ℝ)), HasDerivAt f (f' t) t) →
      ContinuousOn f' (Set.Icc (P : ℝ) (2 * (P : ℝ))) →
      (∀ t ∈ Set.Icc (P : ℝ) (2 * (P : ℝ)), ‖f t‖ ≤ M) →
      (∫ t in (P : ℝ)..(2 * (P : ℝ)), ‖f' t‖) ≤ V →
      ‖(∑ p ∈ openPrimeBand P, f p) -
        (∫ t in (P : ℝ)..(2 * (P : ℝ)), f t / (Real.log t : ℂ))‖ ≤
        (2 * (P : ℝ) / (Real.log (P : ℝ)) ^ A) * (3 * M + V) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (theta_logPower_real A 1 (by norm_num))
  obtain ⟨N, hN⟩ := exists_nat_ge x₀
  obtain ⟨NL, hNL⟩ := RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨max 2 (max N NL), ?_⟩
  intro P hP f f' M V hd hc hM hV
  have hP2 : 2 ≤ P := by omega
  have hPN : N ≤ P := by omega
  have hPL : NL ≤ P := by omega
  have hL : 1 ≤ Real.log (P : ℝ) := hNL P hPL
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hL0 : 0 < Real.log (P : ℝ) := by linarith
  have hp0 : 0 < (Real.log (P : ℝ)) ^ A := pow_pos hL0 A
  apply weighted_prime_discrepancy_of_theta hP2 hL (by positivity) hd hc hM hV
  intro t ht
  have hlog : Real.log (P : ℝ) ≤ Real.log t := Real.log_le_log hP0 ht.1
  have hx : x₀ ≤ t := hN.trans ((Nat.cast_le.mpr hPN).trans ht.1)
  have hθ : |Chebyshev.theta t - t| * (Real.log t) ^ A ≤ t := by
    simpa only [one_mul] using hx₀ t hx
  apply (le_div_iff₀ hp0).mpr
  exact (le_trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hL0.le hlog A) (abs_nonneg _)) hθ).trans ht.2

#check weighted_prime_sampling
#print axioms weighted_theta_discrepancy_le
#print axioms weighted_prime_discrepancy_of_theta
#print axioms weighted_prime_sampling
run_cmd do
  let targets : List Lean.Name := [
    ``weighted_theta_abel,
    ``weighted_theta_discrepancy_eq,
    ``weighted_theta_discrepancy_le,
    ``weighted_prime_discrepancy_of_theta,
    ``weighted_prime_sampling]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.WeightedPrimeSampling151
end

end Update151_Component_2
/- END COMPONENT: WeightedPrimeSampling151.lean -/

/- BEGIN COMPONENT: ReciprocalCharacter151.lean -/
section Update151_Component_3








/-! Exact reciprocal characters and their total variation. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory Set

namespace Erdos374.ReciprocalCharacter151

def phase (u v t : ℝ) : ℝ := u / t + v / t ^ 2
def phaseD (u v t : ℝ) : ℝ := -(u / t ^ 2) - 2 * v / t ^ 3
def amplitude (u v P : ℝ) : ℝ := |u| / P + |v| / P ^ 2
def majorant (u v t : ℝ) : ℝ := |u| / t ^ 2 + 2 * |v| / t ^ 3

def character (u v t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * phase u v t : ℝ) : ℂ) * Complex.I)

def characterD (u v t : ℝ) : ℂ :=
  character u v t * (((2 * Real.pi * phaseD u v t : ℝ) : ℂ) * Complex.I)

theorem phase_hasDerivAt (u v t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (phase u v) (phaseD u v t) t := by
  have h1 := (hasDerivAt_const t u).div (hasDerivAt_id t) ht
  have h2 := (hasDerivAt_const t v).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht)
  convert h1.add h2 using 1
  · rfl
  · dsimp [phaseD]
    field_simp
    <;> ring

theorem character_hasDerivAt (u v t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (character u v) (characterD u v t) t := by
  exact ((((phase_hasDerivAt u v t ht).const_mul (2 * Real.pi)).ofReal_comp).mul_const
    Complex.I).cexp

@[simp] theorem norm_character (u v t : ℝ) : ‖character u v t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem norm_characterD (u v t : ℝ) :
    ‖characterD u v t‖ = 2 * Real.pi * |phaseD u v t| := by
  simp only [characterD, norm_mul, norm_character, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, one_mul, abs_mul]
  norm_num [abs_of_pos Real.pi_pos]

theorem phaseD_abs_le (u v t : ℝ) (ht : 0 < t) :
    |phaseD u v t| ≤ majorant u v t := by
  have h := abs_add_le (-(u / t ^ 2)) (-(2 * v / t ^ 3))
  simpa only [phaseD, majorant, sub_eq_add_neg, abs_neg, abs_div, abs_mul,
    abs_of_pos (pow_pos ht 2), abs_of_pos (pow_pos ht 3),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h

theorem norm_characterD_le (u v t : ℝ) (ht : 0 < t) :
    ‖characterD u v t‖ ≤ 2 * Real.pi * majorant u v t := by
  rw [norm_characterD]
  exact mul_le_mul_of_nonneg_left (phaseD_abs_le u v t ht) (by positivity)

theorem characterD_continuousOn (u v a b : ℝ) (ha : 0 < a) :
    ContinuousOn (characterD u v) (Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht0
  have hp : ContinuousAt (phaseD u v) t := by
    unfold phaseD
    fun_prop
  exact ((character_hasDerivAt u v t ht0).continuousAt.mul
    ((Complex.continuous_ofReal.continuousAt.comp (hp.const_mul (2 * Real.pi))).mul_const
      Complex.I)).continuousWithinAt

theorem majorant_continuousOn (u v a b : ℝ) (ha : 0 < a) :
    ContinuousOn (majorant u v) (Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht0
  apply ContinuousAt.continuousWithinAt
  unfold majorant
  fun_prop

theorem majorant_integral (u v a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, majorant u v t) =
      amplitude u v a - amplitude u v b := by
  have hd : ∀ t ∈ uIcc a b,
      HasDerivAt (fun x => -phase |u| |v| x) (majorant u v t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    convert (phase_hasDerivAt |u| |v| t ht0).neg using 1
    simp only [phaseD, majorant, abs_abs]
    <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((majorant_continuousOn u v a b ha).intervalIntegrable_of_Icc hab)
  simpa only [phase, amplitude, neg_sub_neg] using hi

theorem amplitude_nonneg (u v P : ℝ) (hP : 0 ≤ P) : 0 ≤ amplitude u v P := by
  unfold amplitude
  positivity

/-- The precise variation bound, uniform in both signed reciprocal coefficients. -/
theorem character_variation_le (u v P : ℝ) (hP : 0 < P) :
    (∫ t in P..(2 * P), ‖characterD u v t‖) ≤
      2 * Real.pi * amplitude u v P := by
  have hPP : P ≤ 2 * P := by linarith
  have hD : IntervalIntegrable (fun t => ‖characterD u v t‖) volume P (2 * P) :=
    (characterD_continuousOn u v P (2 * P) hP).norm.intervalIntegrable_of_Icc hPP
  have hM : IntervalIntegrable (majorant u v) volume P (2 * P) :=
    (majorant_continuousOn u v P (2 * P) hP).intervalIntegrable_of_Icc hPP
  calc
    _ ≤ ∫ t in P..(2 * P), 2 * Real.pi * majorant u v t :=
      intervalIntegral.integral_mono_on hPP hD (hM.const_mul _) (by
        intro t ht
        exact norm_characterD_le u v t (lt_of_lt_of_le hP ht.1))
    _ = 2 * Real.pi * (amplitude u v P - amplitude u v (2 * P)) := by
      rw [intervalIntegral.integral_const_mul, majorant_integral u v P (2 * P) hP hPP]
    _ ≤ 2 * Real.pi * amplitude u v P := by
      have hnon := amplitude_nonneg u v (2 * P) (by positivity)
      nlinarith [Real.pi_pos]

#print axioms character_hasDerivAt
#print axioms character_variation_le
run_cmd do
  for target in [``character_hasDerivAt, ``norm_character, ``norm_characterD,
      ``characterD_continuousOn, ``majorant_integral, ``character_variation_le] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalCharacter151
end

end Update151_Component_3
/- END COMPONENT: ReciprocalCharacter151.lean -/

/- BEGIN COMPONENT: ReciprocalSamplingSmall151.lean -/
section Update151_Component_4



/-!
Unconditional prime sampling of reciprocal characters with polylogarithmic
total phase variation. Large oscillatory phases remain a separate obligation.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos374.ReciprocalSamplingSmall151
open ReciprocalCharacter151 SamplingClosure147

theorem logarithmic_variation_absorb (A B : ℕ) (P L F : ℝ)
    (hP : 0 ≤ P) (hL : 1 ≤ L) (hF : F ≤ L ^ B) :
    (2 * P / L ^ (A + B)) * (3 + 2 * Real.pi * F) ≤
      (6 + 4 * Real.pi) * P / L ^ A := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLB : 1 ≤ L ^ B := one_le_pow₀ hL
  have hF' := mul_le_mul_of_nonneg_left hF (show 0 ≤ 2 * Real.pi by positivity)
  have hm : 3 + 2 * Real.pi * F ≤ (3 + 2 * Real.pi) * L ^ B := by
    nlinarith only [hF', hLB]
  calc
    _ ≤ (2 * P / L ^ (A + B)) * ((3 + 2 * Real.pi) * L ^ B) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (6 + 4 * Real.pi) * P / L ^ A := by
      rw [pow_add]
      field_simp [ne_of_gt hL0]
      <;> ring

/-- Uniform in both signed real coefficients, for every fixed logarithmic
variation budget and every requested fixed logarithmic error saving. -/
theorem small_phase_sampling (A B : ℕ) :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → ∀ u v : ℝ,
      amplitude u v (P : ℝ) ≤ (Real.log (P : ℝ)) ^ B →
      ‖(∑ p ∈ openPrimeBand P, character u v (p : ℝ)) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), character u v t / (Real.log t : ℂ)‖ ≤
        (6 + 4 * Real.pi) * (P : ℝ) / (Real.log (P : ℝ)) ^ A := by
  obtain ⟨N, hN⟩ := WeightedPrimeSampling151.weighted_prime_sampling (A + B)
  obtain ⟨NL, hNL⟩ := RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨max N (max NL 2), ?_⟩
  intro P hP u v hF
  have hPN : N ≤ P := le_trans (le_max_left _ _) hP
  have hPL : NL ≤ P := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hP
  have hP2 : 2 ≤ P := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hP2
  have hL : 1 ≤ Real.log (P : ℝ) := hNL P hPL
  have hbound := hN P hPN (character u v) (characterD u v)
    1 (2 * Real.pi * amplitude u v (P : ℝ))
    (by
      intro t ht
      exact character_hasDerivAt u v t (ne_of_gt (lt_of_lt_of_le hP0 ht.1)))
    (characterD_continuousOn u v (P : ℝ) (2 * (P : ℝ)) hP0)
    (by intro t _; exact (norm_character u v t).le)
    (character_variation_le u v (P : ℝ) hP0)
  have hscale := logarithmic_variation_absorb A B (P : ℝ) (Real.log (P : ℝ))
    (amplitude u v (P : ℝ)) hP0.le hL hF
  exact hbound.trans (by simpa only [mul_one] using hscale)

#check small_phase_sampling
#print axioms small_phase_sampling
run_cmd do
  for target in [``logarithmic_variation_absorb, ``small_phase_sampling] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalSamplingSmall151
end

end Update151_Component_4
/- END COMPONENT: ReciprocalSamplingSmall151.lean -/

/- BEGIN COMPONENT: PrimePowerRemoval151.lean -/
section Update151_Component_5




/-! Uniform removal of higher prime powers from bounded complex weighted sums. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace Erdos374.PrimePowerRemoval151

def mangoldtSum (s : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℂ) * w n

def primeLogSum (s : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ p ∈ s with p.Prime, (Real.log (p : ℝ) : ℂ) * w p

theorem mangoldt_sub_primeLog (s : Finset ℕ) (w : ℕ → ℂ) :
    mangoldtSum s w - primeLogSum s w =
      ∑ n ∈ s with ¬n.Prime, (ArithmeticFunction.vonMangoldt n : ℂ) * w n := by
  have hp : (∑ n ∈ s with n.Prime, (ArithmeticFunction.vonMangoldt n : ℂ) * w n) =
      primeLogSum s w := by
    unfold primeLogSum
    apply Finset.sum_congr rfl
    intro p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  have h := Finset.sum_filter_add_sum_filter_not s Nat.Prime
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * w n)
  rw [hp] at h
  change _ + _ = mangoldtSum s w at h
  exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)).symm

/-- The total higher-prime-power mass controls every weight of norm at most one. -/
theorem weighted_prime_power_error (N : ℕ) (s : Finset ℕ) (w : ℕ → ℂ)
    (hs : s ⊆ Finset.Ioc 0 N) (hw : ∀ n ∈ s, ‖w n‖ ≤ 1) :
    ‖mangoldtSum s w - primeLogSum s w‖ ≤
      Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) := by
  rw [mangoldt_sub_primeLog, Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
  calc
    _ ≤ ∑ n ∈ s with ¬n.Prime, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * w n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ s with ¬n.Prime, (ArithmeticFunction.vonMangoldt n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (hw n (Finset.mem_filter.mp hn).1)
    _ ≤ ∑ n ∈ Finset.Ioc 0 N with ¬n.Prime, ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_filter.mpr ⟨hs (Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2⟩
      · intro n _ _
        exact ArithmeticFunction.vonMangoldt_nonneg

/-- Explicit unconditional square-root error, uniform in the finite interval
and complex phase. It is negligible compared with every fixed log saving. -/
theorem weighted_prime_power_error_sqrt (N : ℕ) (hN : 1 ≤ N)
    (s : Finset ℕ) (w : ℕ → ℂ)
    (hs : s ⊆ Finset.Ioc 0 N) (hw : ∀ n ∈ s, ‖w n‖ ≤ 1) :
    ‖mangoldtSum s w - primeLogSum s w‖ ≤
      2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
  (weighted_prime_power_error N s w hs hw).trans
    (Chebyshev.psi_sub_theta_le (by exact_mod_cast hN))

#print axioms weighted_prime_power_error_sqrt
run_cmd do
  for target in [``mangoldt_sub_primeLog, ``weighted_prime_power_error,
      ``weighted_prime_power_error_sqrt] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.PrimePowerRemoval151
end

end Update151_Component_5
/- END COMPONENT: PrimePowerRemoval151.lean -/

/- BEGIN COMPONENT: LogWeightRemoval151.lean -/
section Update151_Component_6






/-! Removing logarithmic weights using uniform bounds on truncated sums. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Erdos374.LogWeightRemoval151

def after (P : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ := if P < n then c n else 0

lemma after_sum (P M : ℕ) (c : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 0 M, after P c n) = ∑ n ∈ Finset.Ioc P M, c n := by
  classical
  simp only [after, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro n _
    rfl

def invLog (t : ℝ) : ℝ := 1 / Real.log t
def invLogD (t : ℝ) : ℝ := -1 / (t * (Real.log t) ^ 2)

lemma invLog_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt invLog (invLogD t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h : HasDerivAt (fun x => (Real.log x)⁻¹) (invLogD t) t := by
    apply ((Real.hasDerivAt_log ht0).inv hl0).congr_deriv
    dsimp [invLogD]
    field_simp
    <;> ring
  change HasDerivAt (fun x : ℝ => 1 / Real.log x) (invLogD t) t
  simpa only [one_div] using h

lemma invLogD_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn invLogD (Icc a b) := by
  intro t ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  have hl2 : (Real.log t) ^ 2 ≠ 0 := pow_ne_zero 2 hl0
  have hden : t * (Real.log t) ^ 2 ≠ 0 := mul_ne_zero ht0 hl2
  apply ContinuousAt.continuousWithinAt
  unfold invLogD
  fun_prop

lemma invLog_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ invLog t := by
  unfold invLog
  exact div_nonneg (by norm_num) (Real.log_pos ht).le

lemma invLogD_nonpos {t : ℝ} (ht : 1 < t) : invLogD t ≤ 0 := by
  unfold invLogD
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)

lemma variation_invLog {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, |invLogD t|) = invLog a - invLog b := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun x => -invLog x) (-invLogD t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (invLog_hasDerivAt (ha.trans_le ht.1)).neg
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((invLogD_continuousOn ha).neg.intervalIntegrable_of_Icc hab)
  calc
    _ = ∫ t in a..b, -invLogD t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact abs_of_nonpos (invLogD_nonpos (ha.trans_le ht.1))
    _ = invLog a - invLog b := by simpa only [neg_sub_neg] using hi

/-- Uniform cancellation for every truncated sum removes a log weight with
the precise factor 1/log(P). No cancellation is assumed from a single endpoint. -/
theorem log_weight_removal (P N : ℕ) (hP : 2 ≤ P) (hPN : P ≤ N)
    (c : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hprefix : ∀ M : ℕ, P ≤ M → M ≤ N → ‖∑ n ∈ Finset.Ioc P M, c n‖ ≤ R) :
    ‖∑ n ∈ Finset.Ioc P N, c n / (Real.log (n : ℝ) : ℂ)‖ ≤
      R / Real.log (P : ℝ) := by
  have ha : 1 < (P : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hP
  have hab : (P : ℝ) ≤ N := by exact_mod_cast hPN
  have hb : 1 < (N : ℝ) := ha.trans_le hab
  let g : ℝ → ℂ := fun t => (invLog t : ℂ)
  let g' : ℝ → ℂ := fun t => (invLogD t : ℂ)
  have hg : ∀ t ∈ Icc (P : ℝ) (N : ℝ), HasDerivAt g (g' t) t := by
    intro t ht
    exact (invLog_hasDerivAt (ha.trans_le ht.1)).ofReal_comp
  have hgc : ContinuousOn g' (Icc (P : ℝ) (N : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn (invLogD_continuousOn ha)
  have hgi : IntegrableOn (deriv g) (Icc (P : ℝ) (N : ℝ)) := by
    apply hgc.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro t ht
    exact (hg t ht).deriv.symm
  have h := sum_mul_eq_sub_sub_integral_mul (after P c) (by linarith : (0 : ℝ) ≤ P) hab
    (fun t ht => (hg t ht).differentiableAt) hgi
  simp_rw [after_sum] at h
  simp only [Nat.floor_natCast, Finset.Ioc_self, Finset.sum_empty, mul_zero, sub_zero] at h
  rw [← intervalIntegral.integral_of_le hab] at h
  have hlhs : (∑ n ∈ Finset.Ioc P N, g n * after P c n) =
      ∑ n ∈ Finset.Ioc P N, c n / (Real.log (n : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [after, if_pos (Finset.mem_Ioc.mp hn).1, g, invLog,
      Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_one, div_eq_mul_inv, one_mul]
    ring
  rw [hlhs] at h
  have hi : ‖∫ t in (P : ℝ)..(N : ℝ),
      deriv g t * (∑ n ∈ Finset.Ioc P ⌊t⌋₊, c n)‖ ≤
      (invLog (P : ℝ) - invLog (N : ℝ)) * R := by
    rw [← variation_invLog ha hab, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · apply Filter.Eventually.of_forall
      intro t ht
      have htI : t ∈ Icc (P : ℝ) (N : ℝ) := ⟨ht.1.le, ht.2⟩
      have hPM : P ≤ ⌊t⌋₊ := by simpa using Nat.floor_le_floor htI.1
      have hMN : ⌊t⌋₊ ≤ N := by simpa using Nat.floor_le_floor htI.2
      rw [(hg t htI).deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hprefix _ hPM hMN) (abs_nonneg _)
    · exact ((invLogD_continuousOn ha).abs.intervalIntegrable_of_Icc hab).mul_const R
  have he : ‖g (N : ℝ) * (∑ n ∈ Finset.Ioc P N, c n)‖ ≤ invLog (N : ℝ) * R := by
    rw [norm_mul]
    have hn : ‖g (N : ℝ)‖ = invLog (N : ℝ) := by
      change ‖(invLog (N : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (invLog_nonneg hb)]
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hprefix N hPN le_rfl) (invLog_nonneg hb)
  rw [h]
  calc
    _ ≤ ‖g (N : ℝ) * (∑ n ∈ Finset.Ioc P N, c n)‖ +
        ‖∫ t in (P : ℝ)..(N : ℝ), deriv g t * (∑ n ∈ Finset.Ioc P ⌊t⌋₊, c n)‖ :=
      norm_sub_le _ _
    _ ≤ invLog (N : ℝ) * R + (invLog (P : ℝ) - invLog (N : ℝ)) * R :=
      add_le_add he hi
    _ = R / Real.log (P : ℝ) := by unfold invLog; ring

#print axioms log_weight_removal
run_cmd do
  for target in [``variation_invLog, ``log_weight_removal] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.LogWeightRemoval151
end

end Update151_Component_6
/- END COMPONENT: LogWeightRemoval151.lean -/

/- BEGIN COMPONENT: ContinuousLogWeightRemoval151.lean -/
section Update151_Component_7



/-! Continuous counterpart of the checked finite logarithmic-weight removal. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set MeasureTheory

namespace Erdos374.ContinuousLogWeightRemoval151
open LogWeightRemoval151

/-- Uniform bounds on a primitive imply the precise 1/log(a) weighted bound. -/
theorem continuous_log_weight_removal {F f : ℝ → ℂ} {a b R : ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt F (f t) t)
    (hc : ContinuousOn f (Icc a b)) (hFa : F a = 0)
    (hprefix : ∀ t ∈ Icc a b, ‖F t‖ ≤ R) :
    ‖∫ t in a..b, f t / (Real.log t : ℂ)‖ ≤ R / Real.log a := by
  let q : ℝ → ℂ := fun t => (invLog t : ℂ)
  let q' : ℝ → ℂ := fun t => (invLogD t : ℂ)
  have hqd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt q (q' t) t :=
    (invLog_hasDerivAt (ha.trans_le ht.1)).ofReal_comp
  have hqdc : ContinuousOn q' (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn (invLogD_continuousOn ha)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := q) (v := F) (u' := q') (v' := f)
    (by intro t ht; rw [uIcc_of_le hab] at ht; exact hqd t ht)
    (by intro t ht; rw [uIcc_of_le hab] at ht; exact hd t ht)
    (hqdc.intervalIntegrable_of_Icc hab) (hc.intervalIntegrable_of_Icc hab)
  have heq : (∫ t in a..b, q t * f t) = ∫ t in a..b, f t / (Real.log t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [q, invLog]
    push_cast
    ring
  rw [heq, hFa, mul_zero, sub_zero] at hparts
  have hi : ‖∫ t in a..b, q' t * F t‖ ≤ (invLog a - invLog b) * R := by
    rw [← variation_invLog ha hab, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · apply Filter.Eventually.of_forall
      intro t ht
      change ‖(invLogD t : ℂ) * F t‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hprefix t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)
    · exact ((invLogD_continuousOn ha).abs.intervalIntegrable_of_Icc hab).mul_const R
  have he : ‖q b * F b‖ ≤ invLog b * R := by
    change ‖(invLog b : ℂ) * F b‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (invLog_nonneg (ha.trans_le hab))]
    exact mul_le_mul_of_nonneg_left (hprefix b ⟨hab, le_rfl⟩)
      (invLog_nonneg (ha.trans_le hab))
  rw [hparts]
  calc
    _ ≤ ‖q b * F b‖ + ‖∫ t in a..b, q' t * F t‖ := norm_sub_le _ _
    _ ≤ invLog b * R + (invLog a - invLog b) * R := add_le_add he hi
    _ = R / Real.log a := by unfold invLog; ring

#print axioms continuous_log_weight_removal
run_cmd do
  let axioms ← Lean.collectAxioms ``continuous_log_weight_removal
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

end Erdos374.ContinuousLogWeightRemoval151
end

end Update151_Component_7
/- END COMPONENT: ContinuousLogWeightRemoval151.lean -/

/- BEGIN COMPONENT: MangoldtToPrimes151.lean -/
section Update151_Component_8



/-! Complete finite transfer from von Mangoldt prefix bounds to prime sums. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators

namespace Erdos374.MangoldtToPrimes151
open PrimePowerRemoval151

def primeCoeff (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n.Prime then (Real.log (n : ℝ) : ℂ) * w n else 0

lemma primeCoeff_sum (s : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ s, primeCoeff w n) = primeLogSum s w := by
  simp only [primeCoeff, primeLogSum, Finset.sum_filter]

lemma primeCoeff_div_log_sum (s : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ s, primeCoeff w n / (Real.log (n : ℝ) : ℂ)) =
      ∑ p ∈ s with p.Prime, w p := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · have hn1 : (1 : ℝ) < n := by exact_mod_cast hn.one_lt
    have hl : (Real.log (n : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos hn1))
    simp only [primeCoeff, if_pos hn]
    field_simp
  · simp [primeCoeff, hn]

/-- Every truncated weighted integer sum is required. The higher-prime-power
and logarithmic-weight errors are proved explicitly, without a PNT premise. -/
theorem prime_sum_of_mangoldt_prefix_bound (P N : ℕ) (hP : 2 ≤ P) (hPN : P ≤ N)
    (w : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ n ∈ Finset.Ioc P N, ‖w n‖ ≤ 1)
    (hprefix : ∀ M : ℕ, P ≤ M → M ≤ N → ‖mangoldtSum (Finset.Ioc P M) w‖ ≤ R) :
    ‖∑ p ∈ Finset.Ioc P N with p.Prime, w p‖ ≤
      (R + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) / Real.log (P : ℝ) := by
  have hN : 1 ≤ N := by omega
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  let K : ℝ := R + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hprime : ∀ M : ℕ, P ≤ M → M ≤ N →
      ‖∑ n ∈ Finset.Ioc P M, primeCoeff w n‖ ≤ K := by
    intro M hPM hMN
    rw [primeCoeff_sum]
    have hs : Finset.Ioc P M ⊆ Finset.Ioc 0 N := by
      intro n hn
      simp only [Finset.mem_Ioc] at hn ⊢
      omega
    have hwM : ∀ n ∈ Finset.Ioc P M, ‖w n‖ ≤ 1 := by
      intro n hn
      apply hw n
      simp only [Finset.mem_Ioc] at hn ⊢
      omega
    have he := weighted_prime_power_error_sqrt N hN (Finset.Ioc P M) w hs hwM
    calc
      _ = ‖mangoldtSum (Finset.Ioc P M) w -
          (mangoldtSum (Finset.Ioc P M) w - primeLogSum (Finset.Ioc P M) w)‖ := by
        congr 1
        ring
      _ ≤ ‖mangoldtSum (Finset.Ioc P M) w‖ +
          ‖mangoldtSum (Finset.Ioc P M) w - primeLogSum (Finset.Ioc P M) w‖ :=
        norm_sub_le _ _
      _ ≤ K := add_le_add (hprefix M hPM hMN) he
  have h := LogWeightRemoval151.log_weight_removal P N hP hPN (primeCoeff w) K hK hprime
  rw [primeCoeff_div_log_sum] at h
  exact h

#print axioms prime_sum_of_mangoldt_prefix_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``prime_sum_of_mangoldt_prefix_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

end Erdos374.MangoldtToPrimes151
end

end Update151_Component_8
/- END COMPONENT: MangoldtToPrimes151.lean -/

/- BEGIN COMPONENT: FourierSampling151.lean -/
section Update151_Component_9








/-!
Proved analytic components of the reciprocal-prime Fourier transfer.
No character discrepancy estimate or full sampling theorem is asserted here.
-/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ContDiff

namespace Erdos374.FourierSampling151

/-- Fourier coefficient on one period, with Mathlib's standard normalization. -/
def unitCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n

/-- Translation invariance proves periodicity of every actual iterated derivative;
the endpoint identities used in integration by parts are not extra assumptions. -/
theorem iteratedDeriv_periodic {f : ℝ → ℂ} (hf : Function.Periodic f 1) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) 1 := by
  have heq : (fun x : ℝ => f (x + 1)) = f := funext hf
  have h := iteratedDeriv_comp_add_const k f (1 : ℝ)
  rw [heq] at h
  intro x
  exact (congrFun h x).symm

/-- The normalized coefficient is bounded by any global bound on the function. -/
theorem unitCoeff_norm_le {f : ℝ → ℂ} {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (n : ℤ) : ‖unitCoeff f n‖ ≤ M := by
  unfold unitCoeff
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div_one, one_smul]
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖fourier (-n) (x : AddCircle ((1 : ℝ) - 0)) • f x‖ ≤ M := by
    intro x _
    simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using hM x
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- One integration by parts, with the periodic seam cancelled exactly. -/
theorem unitCoeff_iterated_step {f : ℝ → ℂ}
    (hf : ContDiff ℝ 3 f) (hp : Function.Periodic f 1)
    {n : ℤ} (hn : n ≠ 0) {k : ℕ} (hk : k < 3) :
    unitCoeff (iteratedDeriv k f) n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))⁻¹ *
        unitCoeff (iteratedDeriv (k + 1) f) n := by
  have hk' : (k : ℕ∞ω) < 3 := by exact_mod_cast hk
  have hks : ((k + 1 : ℕ) : ℕ∞ω) ≤ 3 := by exact_mod_cast (by omega : k + 1 ≤ 3)
  have hd := hf.differentiable_iteratedDeriv k hk'
  have hc := hf.continuous_iteratedDeriv (k + 1) hks
  have hseam : iteratedDeriv k f 1 = iteratedDeriv k f 0 := by
    simpa only [zero_add] using iteratedDeriv_periodic hp k 0
  have h := fourierCoeffOn_of_hasDerivAt (by norm_num : (0 : ℝ) < 1) hn
    (f := iteratedDeriv k f) (f' := iteratedDeriv (k + 1) f)
    (fun x _ => by simpa only [iteratedDeriv_succ] using (hd x).hasDerivAt)
    (hc.intervalIntegrable 0 1)
  simp only [hseam, sub_self, mul_zero, Complex.ofReal_one, Complex.ofReal_zero,
    sub_zero, one_mul, zero_sub] at h
  have hneg : (-2 : ℂ) * Real.pi * Complex.I * n =
      -(2 * (Real.pi : ℂ) * Complex.I * n) := by ring
  rw [hneg] at h
  simpa only [unitCoeff, one_div, inv_neg, neg_mul_neg] using h

/-- Three integrations by parts for a genuine C3 periodic function. -/
theorem unitCoeff_eq_third_derivative {f : ℝ → ℂ}
    (hf : ContDiff ℝ 3 f) (hp : Function.Periodic f 1)
    {n : ℤ} (hn : n ≠ 0) :
    unitCoeff f n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))⁻¹ ^ 3 *
        unitCoeff (iteratedDeriv 3 f) n := by
  have h0 := unitCoeff_iterated_step hf hp hn (k := 0) (by norm_num)
  have h1 := unitCoeff_iterated_step hf hp hn (k := 1) (by norm_num)
  have h2 := unitCoeff_iterated_step hf hp hn (k := 2) (by norm_num)
  simp only [iteratedDeriv_zero] at h0
  rw [h0, h1, h2]
  ring

/-- Cubic coefficient decay with the exact one-dimensional third derivative.
The bound M is uniform in x; the resulting constant is uniform in frequency. -/
theorem unitCoeff_cubic_decay {f : ℝ → ℂ} {M : ℝ}
    (hf : ContDiff ℝ 3 f) (hp : Function.Periodic f 1)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) {n : ℤ} (hn : n ≠ 0) :
    ‖unitCoeff f n‖ ≤ M / (2 * Real.pi * |(n : ℝ)|) ^ 3 := by
  rw [unitCoeff_eq_third_derivative hf hp hn, norm_mul, norm_pow, norm_inv]
  have hfreq : ‖2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)‖ =
      2 * Real.pi * |(n : ℝ)| := by
    simp [norm_mul, Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hfreq]
  calc
    _ ≤ ((2 * Real.pi * |(n : ℝ)|)⁻¹) ^ 3 * M :=
      mul_le_mul_of_nonneg_left (unitCoeff_norm_le hM n) (by positivity)
    _ = _ := by rw [inv_pow]; ring

/-- A continuous doubly periodic function has compact range, by reduction to
the actual closed unit square. This also applies to its derivative norms. -/
theorem compact_range_two_periodic {E : Type*} [TopologicalSpace E]
    {f : ℝ × ℝ → E} (hf : Continuous f)
    (hx : ∀ x y, f (x + 1, y) = f (x, y))
    (hy : ∀ x y, f (x, y + 1) = f (x, y)) : IsCompact (Set.range f) := by
  have heq : f '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = Set.range f := by
    apply Set.Subset.antisymm (Set.image_subset_range _ _)
    rintro _ ⟨⟨x, y⟩, rfl⟩
    have hxp : Function.Periodic (fun t => f (t, y)) 1 := fun t => hx t y
    have hxr := hxp.image_Icc (by norm_num : (0 : ℝ) < 1) 0
    simp only [zero_add] at hxr
    have hxmem : f (x, y) ∈ (fun t => f (t, y)) '' Set.Icc (0 : ℝ) 1 := by
      rw [hxr]
      exact Set.mem_range_self x
    obtain ⟨x', hx', hxx'⟩ := hxmem
    have hyp : Function.Periodic (fun t => f (x', t)) 1 := fun t => hy x' t
    have hyr := hyp.image_Icc (by norm_num : (0 : ℝ) < 1) 0
    simp only [zero_add] at hyr
    have hymem : f (x', y) ∈ (fun t => f (x', t)) '' Set.Icc (0 : ℝ) 1 := by
      rw [hyr]
      exact Set.mem_range_self y
    obtain ⟨y', hy', hyy'⟩ := hymem
    exact ⟨(x', y'), ⟨hx', hy'⟩, hyy'.trans hxx'⟩
  rw [← heq]
  exact (isCompact_Icc.prod isCompact_Icc).image hf

theorem iteratedFDeriv_two_periodic {W : ℝ × ℝ → ℝ}
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (j : ℕ) :
    (∀ x y, iteratedFDeriv ℝ j W (x + 1, y) = iteratedFDeriv ℝ j W (x, y)) ∧
    (∀ x y, iteratedFDeriv ℝ j W (x, y + 1) = iteratedFDeriv ℝ j W (x, y)) := by
  have hxeq : (fun z : ℝ × ℝ => W (z + (1, 0))) = W := by
    funext ⟨x, y⟩
    simpa only [Prod.mk_add_mk, add_zero] using hx x y
  have hyeq : (fun z : ℝ × ℝ => W (z + (0, 1))) = W := by
    funext ⟨x, y⟩
    simpa only [Prod.mk_add_mk, add_zero] using hy x y
  constructor
  · intro x y
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := W) j (1, 0) (x, y)
    rw [hxeq] at h
    simpa only [Prod.mk_add_mk, add_zero] using h.symm
  · intro x y
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := W) j (0, 1) (x, y)
    rw [hyeq] at h
    simpa only [Prod.mk_add_mk, add_zero] using h.symm

/-- Periodicity and C3 regularity justify the bounded suprema in the candidate's
actual `c3Size`; no finiteness property of those suprema is assumed. -/
theorem c3_derivative_bddAbove {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) {j : ℕ} (hj : j ≤ 3) :
    BddAbove (Set.range (fun z => ‖iteratedFDeriv ℝ j W z‖)) := by
  have hc : Continuous (fun z => ‖iteratedFDeriv ℝ j W z‖) :=
    (hW.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm
  obtain ⟨hpx, hpy⟩ := iteratedFDeriv_two_periodic hx hy j
  exact (compact_range_two_periodic hc
    (fun x y => congrArg norm (hpx x y))
    (fun x y => congrArg norm (hpy x y))).bddAbove

/-- Each derivative norm through order three is bounded by the exact C3 size
used by the sampler, with coefficient one. -/
theorem norm_iteratedFDeriv_le_c3Size {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y))
    {j : ℕ} (hj : j ≤ 3) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j W z‖ ≤ UniformC3_147.c3Size W := by
  have hnonneg : ∀ i ∈ Finset.range 4,
      0 ≤ sSup (Set.range (fun z => ‖iteratedFDeriv ℝ i W z‖)) := by
    intro i hi
    have hib : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
    exact (norm_nonneg (iteratedFDeriv ℝ i W (0, 0))).trans
      (le_csSup (c3_derivative_bddAbove hW hx hy hib) (Set.mem_range_self (0, 0)))
  calc
    _ ≤ sSup (Set.range (fun z => ‖iteratedFDeriv ℝ j W z‖)) :=
      le_csSup (c3_derivative_bddAbove hW hx hy hj) (Set.mem_range_self z)
    _ ≤ UniformC3_147.c3Size W :=
      Finset.single_le_sum hnonneg (show j ∈ Finset.range 4 by simp only [Finset.mem_range]; omega)

/-- Restricting to a coordinate line does not increase the derivative norm.
Complexification preserves that norm exactly. -/
theorem norm_iteratedDeriv_slice_fst_le {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    {j : ℕ} (hj : j ≤ 3) (x y : ℝ) :
    ‖iteratedDeriv j (fun t : ℝ => (W (t, y) : ℂ)) x‖ ≤
      ‖iteratedFDeriv ℝ j W (x, y)‖ := by
  have hj' : (j : ℕ∞ω) ≤ 3 := by exact_mod_cast hj
  have hslice : ContDiff ℝ 3 (fun t : ℝ => W (t, y)) :=
    hW.comp (contDiff_id.prodMk contDiff_const)
  have hcomplex : ‖iteratedFDeriv ℝ j (fun t : ℝ => (W (t, y) : ℂ)) x‖ =
      ‖iteratedFDeriv ℝ j (fun t : ℝ => W (t, y)) x‖ := by
    simpa only [Function.comp_def, Complex.ofRealLI_apply] using
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left hslice.contDiffAt hj'
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hcomplex]
  let g : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inl ℝ ℝ ℝ
  have hshift : ContDiff ℝ 3 (fun z : ℝ × ℝ => W (z + (0, y))) :=
    hW.comp (contDiff_id.add contDiff_const)
  have hchain := g.iteratedFDeriv_comp_right hshift x hj'
  have hshiftder : iteratedFDeriv ℝ j (fun z : ℝ × ℝ => W (z + (0, y))) (g x) =
      iteratedFDeriv ℝ j W (x, y) := by
    simpa only [g, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] using
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := W) j (0, y) (g x)
  rw [hshiftder] at hchain
  have hfun : (fun z : ℝ × ℝ => W (z + (0, y))) ∘ g =
      (fun t : ℝ => W (t, y)) := by
    funext t
    simp only [Function.comp_def, g, ContinuousLinearMap.inl_apply,
      Prod.mk_add_mk, add_zero, zero_add]
  rw [hfun] at hchain
  rw [hchain]
  simpa only [g, ContinuousLinearMap.norm_inl, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ j W (x, y)).norm_compContinuousLinearMap_le (fun _ => g)

/-- A uniform coordinate-slice Fourier bound in precisely the candidate's C3 norm.
The constant is independent of the slice location and nonzero frequency. -/
theorem slice_fst_cubic_decay {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y))
    (y : ℝ) {n : ℤ} (hn : n ≠ 0) :
    ‖unitCoeff (fun x : ℝ => (W (x, y) : ℂ)) n‖ ≤
      UniformC3_147.c3Size W / (2 * Real.pi * |(n : ℝ)|) ^ 3 := by
  apply unitCoeff_cubic_decay
    (Complex.ofRealCLM.contDiff.comp (hW.comp (contDiff_id.prodMk contDiff_const)))
    (fun x => congrArg Complex.ofReal (hx x y)) _ hn
  intro x
  exact (norm_iteratedDeriv_slice_fst_le hW (le_refl 3) x y).trans
    (norm_iteratedFDeriv_le_c3Size hW hx hy (le_refl 3) (x, y))

def unitCharacter (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))

theorem unitCharacter_eq_fourier (n : ℤ) (x : ℝ) :
    unitCharacter n x = fourier n (x : AddCircle (1 : ℝ)) := by
  simp only [unitCharacter, fourier_coe_apply, Complex.ofReal_one, div_one]

theorem norm_unitCharacter (n : ℤ) (x : ℝ) : ‖unitCharacter n x‖ = 1 := by
  rw [unitCharacter_eq_fourier, fourier_apply, Circle.norm_coe]

theorem unitCoeff_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    unitCoeff f n = ∫ x in (0 : ℝ)..1, unitCharacter (-n) x * f x := by
  simp only [unitCoeff, fourierCoeffOn_eq_integral, fourier_coe_apply,
    sub_zero, one_div_one, one_smul, smul_eq_mul, Complex.ofReal_one, div_one,
    unitCharacter]

/-- The genuine two-variable coefficient, with normalized unit periods. -/
def planeCoeff (W : ℝ × ℝ → ℝ) (n m : ℤ) : ℂ :=
  unitCoeff (fun y => unitCoeff (fun x => (W (x, y) : ℂ)) n) m

/-- Fubini identifies the two orders of taking coefficients. -/
theorem planeCoeff_swap {W : ℝ × ℝ → ℝ} (hW : Continuous W) (n m : ℤ) :
    planeCoeff W n m = planeCoeff (W ∘ Prod.swap) m n := by
  let F : ℝ → ℝ → ℂ := fun y x =>
    unitCharacter (-m) y * (unitCharacter (-n) x * (W (x, y) : ℂ))
  have hF : Continuous F.uncurry := by
    dsimp [F, Function.uncurry, unitCharacter]
    fun_prop
  have hi : IntegrableOn F.uncurry
      (Set.uIoc (0 : ℝ) 1 ×ˢ Set.uIoc (0 : ℝ) 1) := by
    apply (hF.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
    intro z hz
    simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      ⟨Set.Ioc_subset_Icc_self hz.1, Set.Ioc_subset_Icc_self hz.2⟩
  simp only [planeCoeff, unitCoeff_eq_integral, Function.comp_def, Prod.swap_prod_mk]
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [show (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      unitCharacter (-m) y * (unitCharacter (-n) x * (W (x, y) : ℂ))) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        unitCharacter (-m) y * (unitCharacter (-n) x * (W (x, y) : ℂ)) from
      intervalIntegral_intervalIntegral_swap hi]
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  ring

/-- Swapping coordinates preserves the actual C3 size, including all suprema. -/
theorem c3Size_swap (W : ℝ × ℝ → ℝ) :
    UniformC3_147.c3Size (W ∘ Prod.swap) = UniformC3_147.c3Size W := by
  unfold UniformC3_147.c3Size
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hn : ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (W ∘ Prod.swap) z‖ = ‖iteratedFDeriv ℝ j W z.swap‖ := by
    intro z
    exact (LinearIsometryEquiv.prodComm ℝ ℝ ℝ).norm_iteratedFDeriv_comp_right W z j
  simp_rw [hn]
  simpa only [Function.comp_def] using
    (show Function.Surjective (Prod.swap : ℝ × ℝ → ℝ × ℝ) from
      fun z => ⟨z.swap, Prod.swap_swap z⟩).range_comp
      (fun z : ℝ × ℝ => ‖iteratedFDeriv ℝ j W z‖)

/-- Cubic decay in the first frequency, uniformly in the second. -/
theorem planeCoeff_fst_decay {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y))
    {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    ‖planeCoeff W n m‖ ≤
      UniformC3_147.c3Size W / (2 * Real.pi * |(n : ℝ)|) ^ 3 :=
  unitCoeff_norm_le (fun y => slice_fst_cubic_decay hW hx hy y hn) m

/-- The same decay on the other axis, using the proved Fubini interchange. -/
theorem planeCoeff_snd_decay {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y))
    (n : ℤ) {m : ℤ} (hm : m ≠ 0) :
    ‖planeCoeff W n m‖ ≤
      UniformC3_147.c3Size W / (2 * Real.pi * |(m : ℝ)|) ^ 3 := by
  rw [planeCoeff_swap hW.continuous]
  have hswap : ContDiff ℝ 3 (W ∘ Prod.swap) :=
    hW.comp (contDiff_snd.prodMk contDiff_fst)
  simpa only [c3Size_swap] using planeCoeff_fst_decay hswap
    (fun x y => hy y x) (fun x y => hx y x) hm n

theorem planeCoeff_norm_le_c3Size {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (n m : ℤ) :
    ‖planeCoeff W n m‖ ≤ UniformC3_147.c3Size W := by
  apply unitCoeff_norm_le
  intro y
  apply unitCoeff_norm_le
  intro x
  simpa only [norm_iteratedFDeriv_zero, Complex.norm_real] using
    norm_iteratedFDeriv_le_c3Size hW hx hy (j := 0) (by norm_num) (x, y)

/-- The full two-dimensional cubic majorant [F3], with the absolute constant
K_F = 1. Both axes and the zero coefficient are included. -/
theorem planeCoeff_cubic_majorant {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (n m : ℤ) :
    ‖planeCoeff W n m‖ ≤
      UniformC3_147.c3Size W / (1 + |(n : ℝ)| + |(m : ℝ)|) ^ 3 := by
  have hN : 0 ≤ UniformC3_147.c3Size W :=
    (norm_nonneg (planeCoeff W 0 0)).trans (planeCoeff_norm_le_c3Size hW hx hy 0 0)
  have hpi : (3 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hdivide (a : ℝ) (ha : 1 + |(n : ℝ)| + |(m : ℝ)| ≤ 2 * Real.pi * a) :
      UniformC3_147.c3Size W / (2 * Real.pi * a) ^ 3 ≤
        UniformC3_147.c3Size W / (1 + |(n : ℝ)| + |(m : ℝ)|) ^ 3 := by
    exact div_le_div_of_nonneg_left hN (by positivity)
      (pow_le_pow_left₀ (by positivity) ha 3)
  by_cases hzero : n = 0 ∧ m = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simpa only [Int.cast_zero, abs_zero, add_zero, one_pow, div_one] using
      planeCoeff_norm_le_c3Size hW hx hy 0 0
  by_cases hnm : |(m : ℝ)| ≤ |(n : ℝ)|
  · have hn : n ≠ 0 := by
      intro hn
      apply hzero
      refine ⟨hn, ?_⟩
      rw [hn, Int.cast_zero, abs_zero] at hnm
      have hm0 : |(m : ℝ)| = 0 := le_antisymm hnm (abs_nonneg (m : ℝ))
      exact_mod_cast abs_eq_zero.mp hm0
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    apply (planeCoeff_fst_decay hW hx hy hn m).trans (hdivide _ ?_)
    calc
      _ ≤ 3 * |(n : ℝ)| := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
  · have hm : m ≠ 0 := by
      intro hm
      apply hnm
      simpa only [hm, Int.cast_zero, abs_zero] using abs_nonneg (n : ℝ)
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    apply (planeCoeff_snd_decay hW hx hy n hm).trans (hdivide _ ?_)
    calc
      _ ≤ 3 * |(m : ℝ)| := by linarith [lt_of_not_ge hnm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpi (abs_nonneg _)

/-- Absolute summability in two dimensions follows from the proved cubic
majorant and Mathlib's lattice p-series theorem. -/
theorem summable_planeCoeff {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) :
    Summable (fun k : Fin 2 → ℤ => planeCoeff W (k 0) (k 1)) := by
  have hN : 0 ≤ UniformC3_147.c3Size W :=
    (norm_nonneg (planeCoeff W 0 0)).trans (planeCoeff_norm_le_c3Size hW hx hy 0 0)
  apply ((EisensteinSeries.summable_one_div_norm_rpow
    (k := 3) (by norm_num)).mul_left (UniformC3_147.c3Size W)).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : Fin 2 → ℤ)] with k hk
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hrad : ‖k‖ ≤ 1 + |(k 0 : ℝ)| + |(k 1 : ℝ)| := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp only [Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
    apply max_le <;> linarith [abs_nonneg (k 0 : ℝ), abs_nonneg (k 1 : ℝ)]
  calc
    _ ≤ UniformC3_147.c3Size W / (1 + |(k 0 : ℝ)| + |(k 1 : ℝ)|) ^ 3 :=
      planeCoeff_cubic_majorant hW hx hy (k 0) (k 1)
    _ ≤ UniformC3_147.c3Size W / ‖k‖ ^ 3 :=
      div_le_div_of_nonneg_left hN (pow_pos hkpos 3)
        (pow_le_pow_left₀ hkpos.le hrad 3)
    _ = _ := by rw [Real.rpow_neg hkpos.le, show (3 : ℝ) = (3 : ℕ) by norm_num,
      Real.rpow_natCast]; rfl

def leftLift (W : ℝ × ℝ → ℝ)
    (hx : ∀ x y, W (x + 1, y) = W (x, y)) (x : UnitAddCircle) (y : ℝ) : ℝ :=
  (show Function.Periodic (fun x : ℝ => fun y : ℝ => W (x, y)) 1 from
    fun x => funext (hx x)).lift x y

theorem leftLift_periodic (W : ℝ × ℝ → ℝ)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (x : UnitAddCircle) :
    Function.Periodic (leftLift W hx x) 1 := by
  refine Quotient.inductionOn' x ?_
  intro x
  exact hy x

def pairLift (W : ℝ × ℝ → ℝ)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y))
    (z : UnitAddCircle × UnitAddCircle) : ℂ :=
  ((leftLift_periodic W hx hy z.1).lift z.2 : ℝ)

@[simp] theorem pairLift_coe (W : ℝ × ℝ → ℝ)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (x y : ℝ) :
    pairLift W hx hy (x, y) = (W (x, y) : ℂ) := rfl

theorem continuous_pairLift (W : ℝ × ℝ → ℝ) (hW : Continuous W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) : Continuous (pairLift W hx hy) := by
  have hq : IsOpenQuotientMap ((↑) : ℝ → UnitAddCircle) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  rw [← (hq.prodMap hq).continuous_comp_iff]
  exact Complex.continuous_ofReal.comp hW

/-- The smooth test genuinely descends to Mathlib's compact two-dimensional torus. -/
def torusLift (W : ℝ × ℝ → ℝ) (hW : Continuous W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) :
    C(UnitAddTorus (Fin 2), ℂ) where
  toFun z := pairLift W hx hy (z 0, z 1)
  continuous_toFun := (continuous_pairLift W hW hx hy).comp
    ((continuous_apply 0).prodMk (continuous_apply 1))

@[simp] theorem torusLift_coe (W : ℝ × ℝ → ℝ) (hW : Continuous W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (x y : ℝ) :
    torusLift W hW hx hy ![(x : UnitAddCircle), (y : UnitAddCircle)] =
      (W (x, y) : ℂ) := rfl

theorem integral_haar_unit_eq (f : UnitAddCircle → ℂ) :
    (∫ z, f z ∂AddCircle.haarAddCircle) = ∫ x in (0 : ℝ)..1, f x := by
  rw [AddCircle.integral_haarAddCircle]
  simpa only [inv_one, one_smul, zero_add] using
    (AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f).symm

/-- Identification of the iterated coefficients with Mathlib's actual torus
Fourier coefficients, including the Haar normalization and product measure. -/
theorem torusLift_coefficient (W : ℝ × ℝ → ℝ) (hW : Continuous W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusLift W hW hx hy) k =
      planeCoeff W (k 0) (k 1) := by
  let F : UnitAddCircle × UnitAddCircle → ℂ := fun z =>
    fourier (-(k 0)) z.1 * fourier (-(k 1)) z.2 * pairLift W hx hy z
  have hF : Continuous F := by
    dsimp [F]
    exact (((fourier _).continuous.comp continuous_fst).mul
      ((fourier _).continuous.comp continuous_snd)).mul (continuous_pairLift W hW hx hy)
  have hi : Integrable F (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have heq : UnitAddTorus.mFourierCoeff (torusLift W hW hx hy) k =
      ∫ z, F z ∂(AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) := by
    unfold UnitAddTorus.mFourierCoeff
    rw [← (measurePreserving_finTwoArrow (AddCircle.haarAddCircle : Measure UnitAddCircle)).integral_comp' F]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      simp [F, UnitAddTorus.mFourier, torusLift, Fin.prod_univ_two, smul_eq_mul,
        MeasurableEquiv.finTwoArrow_apply])
  rw [heq, integral_prod F hi]
  simp_rw [integral_haar_unit_eq]
  simp only [F, pairLift_coe, ← unitCharacter_eq_fourier]
  rw [planeCoeff_swap hW]
  simp only [planeCoeff, unitCoeff_eq_integral, Function.comp_def, Prod.swap_prod_mk]
  simp_rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  ring

/-- Uniform two-dimensional Fourier reconstruction, with summability supplied
by the proved C3 estimate rather than taken as an additional assumption. -/
theorem hasSum_torus_fourier {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) :
    HasSum (fun k : Fin 2 → ℤ =>
      planeCoeff W (k 0) (k 1) • UnitAddTorus.mFourier k)
      (torusLift W hW.continuous hx hy) := by
  have hs : Summable (UnitAddTorus.mFourierCoeff (torusLift W hW.continuous hx hy)) := by
    change Summable (fun k => UnitAddTorus.mFourierCoeff (torusLift W hW.continuous hx hy) k)
    simpa only [torusLift_coefficient] using summable_planeCoeff hW hx hy
  simpa only [torusLift_coefficient] using UnitAddTorus.hasSum_mFourier_series_of_summable hs

/-- The reconstruction evaluated at arbitrary real coordinates. -/
theorem hasSum_plane_fourier {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (x y : ℝ) :
    HasSum (fun k : Fin 2 → ℤ => planeCoeff W (k 0) (k 1) *
      (unitCharacter (k 0) x * unitCharacter (k 1) y)) (W (x, y) : ℂ) := by
  have h := (ContinuousMap.evalCLM ℂ ![(x : UnitAddCircle), (y : UnitAddCircle)]).hasSum
    (hasSum_torus_fourier hW hx hy)
  simpa only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
    torusLift_coe, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, ← unitCharacter_eq_fourier] using h
#print axioms unitCoeff_norm_le
#print axioms unitCoeff_eq_third_derivative
#print axioms unitCoeff_cubic_decay
#print axioms norm_iteratedFDeriv_le_c3Size
#print axioms slice_fst_cubic_decay
#print axioms planeCoeff_swap
#print axioms planeCoeff_snd_decay
#print axioms planeCoeff_cubic_majorant
#print axioms summable_planeCoeff
#print axioms torusLift_coefficient
#print axioms hasSum_plane_fourier

end Erdos374.FourierSampling151
end


end Update151_Component_9
/- END COMPONENT: FourierSampling151.lean -/

/- BEGIN COMPONENT: FourierTail151.lean -/
section Update151_Component_10


noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ContDiff

namespace Erdos374.FourierSampling151

/-- Regrouping a summable lattice series into the finite square shells. -/
theorem tsum_eq_tsum_box {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    (∑' p, f p) = ∑' n : ℕ, ∑ p ∈ Finset.box n, f p := by
  let e := Set.sigmaEquiv (fun n : ℕ => (↑(Finset.box n : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)))
    Int.existsUnique_mem_box
  have he : Summable (fun p => f (e p)) := e.summable_iff.mpr hf
  rw [← e.tsum_eq f, he.tsum_sigma]
  apply tsum_congr
  intro n
  exact Finset.tsum_subtype (Finset.box n) f

theorem sum_reciprocal_telescope (R L : ℕ) :
    (∑ n ∈ Finset.range L, 1 / (((R + n + 1 : ℕ) : ℝ) * (R + n + 2))) =
      1 / ((R : ℝ) + 1) - 1 / (R + L + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (R : ℝ) + L + 1 ≠ 0 := by positivity
    have h2 : (R : ℝ) + L + 2 ≠ 0 := by positivity
    field_simp
    <;> ring

theorem tsum_reciprocal_telescope_le (R : ℕ) :
    (∑' n : ℕ, 1 / (((R + n + 1 : ℕ) : ℝ) * (R + n + 2))) ≤
      1 / ((R : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro L
  rw [sum_reciprocal_telescope]
  exact sub_le_self _ (by positivity)

theorem summable_reciprocal_telescope (R : ℕ) :
    Summable (fun n : ℕ => 1 / (((R + n + 1 : ℕ) : ℝ) * (R + n + 2))) := by
  apply summable_of_sum_range_le (c := 1 / ((R : ℝ) + 1)) (fun n => by positivity)
  intro L
  rw [sum_reciprocal_telescope]
  exact sub_le_self _ (by positivity)

theorem planeCoeff_box_sum_le {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) {r : ℕ} (hr : r ≠ 0) :
    (∑ p ∈ (Finset.box r : Finset (ℤ × ℤ)), ‖planeCoeff W p.1 p.2‖) ≤
      8 * UniformC3_147.c3Size W / ((r : ℝ) * (r + 1)) := by
  have hN : 0 ≤ UniformC3_147.c3Size W :=
    (norm_nonneg (planeCoeff W 0 0)).trans (planeCoeff_norm_le_c3Size hW hx hy 0 0)
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
  calc
    _ ≤ ∑ _p ∈ (Finset.box r : Finset (ℤ × ℤ)),
        UniformC3_147.c3Size W / ((r : ℝ) + 1) ^ 3 := by
      apply Finset.sum_le_sum
      intro p hp
      apply (planeCoeff_cubic_majorant hW hx hy p.1 p.2).trans
      have hb := Int.mem_box.mp hp
      have hrad : (r : ℝ) ≤ |(p.1 : ℝ)| + |(p.2 : ℝ)| := by
        rw [← hb, Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
        exact max_le (by linarith [abs_nonneg (p.2 : ℝ)])
          (by linarith [abs_nonneg (p.1 : ℝ)])
      apply div_le_div_of_nonneg_left hN (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      linarith
    _ = (8 * (r : ℝ)) * (UniformC3_147.c3Size W / ((r : ℝ) + 1) ^ 3) := by
      rw [Finset.sum_const, nsmul_eq_mul, Int.card_box hr]
      push_cast
      rfl
    _ ≤ _ := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg hN (show (0 : ℝ) ≤ (r + 1) * (2 * r + 1) by positivity)]

/-- Absolute summability in pair coordinates. -/
theorem summable_planeCoeff_norm_pair {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) :
    Summable (fun p : ℤ × ℤ => ‖planeCoeff W p.1 p.2‖) := by
  simpa only [Function.comp_def, finTwoArrowEquiv_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    (finTwoArrowEquiv ℤ).symm.summable_iff.mpr (summable_planeCoeff hW hx hy).norm

/-- The coefficient mass outside the radius-R square. -/
def squareTail (W : ℝ × ℝ → ℝ) (R : ℕ) : ℝ :=
  ∑' p : ℤ × ℤ, if R < max p.1.natAbs p.2.natAbs then ‖planeCoeff W p.1 p.2‖ else 0

theorem squareTail_le {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (R : ℕ) :
    squareTail W R ≤ 8 * UniformC3_147.c3Size W / ((R : ℝ) + 1) := by
  classical
  let q : ℤ × ℤ → ℝ := fun p =>
    if R < max p.1.natAbs p.2.natAbs then ‖planeCoeff W p.1 p.2‖ else 0
  have hq : Summable q := by
    exact (summable_planeCoeff_norm_pair hW hx hy).of_nonneg_of_le
      (fun p => by dsimp [q]; split_ifs <;> positivity)
      (fun p => by dsimp [q]; split_ifs <;> simp only [le_refl, norm_nonneg])
  let s : ℕ → ℝ := fun r => ∑ p ∈ (Finset.box r : Finset (ℤ × ℤ)), q p
  have hsum : squareTail W R = ∑' r, s r := tsum_eq_tsum_box hq
  have hs : Summable s := by
    have h := hq.hasSum.tsum_fiberwise (fun p => max p.1.natAbs p.2.natAbs)
    have hset (r : ℕ) :
        (fun p : ℤ × ℤ => max p.1.natAbs p.2.natAbs) ⁻¹' {r} =
          (↑(Finset.box r : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
      ext p
      simp
    apply h.summable.congr
    intro r
    rw [hset]
    exact Finset.tsum_subtype (Finset.box r) q
  have hzero : ∑ r ∈ Finset.range (R + 1), s r = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro p hp
    have hb := Int.mem_box.mp hp
    simp only [q, hb, if_neg (show ¬ R < r by have := Finset.mem_range.mp hr; omega)]
  have htail : squareTail W R = ∑' n : ℕ, s (n + (R + 1)) := by
    rw [← hs.sum_add_tsum_nat_add (R + 1), hzero, zero_add] at hsum
    exact hsum
  rw [htail]
  have hN : 0 ≤ UniformC3_147.c3Size W :=
    (norm_nonneg (planeCoeff W 0 0)).trans (planeCoeff_norm_le_c3Size hW hx hy 0 0)
  calc
    _ ≤ ∑' n : ℕ, (8 * UniformC3_147.c3Size W) *
        (1 / (((R + n + 1 : ℕ) : ℝ) * (R + n + 2))) := by
      apply Summable.tsum_le_tsum
        (g := fun n : ℕ => (8 * UniformC3_147.c3Size W) *
          (1 / (((R + n + 1 : ℕ) : ℝ) * (R + n + 2))))
      · intro n
        have hsq : s (n + (R + 1)) =
            ∑ p ∈ (Finset.box (n + (R + 1)) : Finset (ℤ × ℤ)),
              ‖planeCoeff W p.1 p.2‖ := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [q, Int.mem_box.mp hp, if_pos (show R < n + (R + 1) by omega)]
        rw [hsq]
        convert planeCoeff_box_sum_le hW hx hy (r := n + (R + 1)) (by omega) using 1 <;>
          push_cast <;> ring
      · exact hs.comp_injective (add_left_injective (R + 1))
      · exact (summable_reciprocal_telescope R).mul_left _
    _ = (8 * UniformC3_147.c3Size W) *
        (∑' n : ℕ, 1 / (((R + n + 1 : ℕ) : ℝ) * (R + n + 2))) := tsum_mul_left
    _ ≤ _ := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left (tsum_reciprocal_telescope_le R) (by positivity :
          0 ≤ 8 * UniformC3_147.c3Size W)

/-- A uniform absolute coefficient mass bound, independent of the test. -/
theorem planeCoeff_l1_le {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) :
    (∑' p : ℤ × ℤ, ‖planeCoeff W p.1 p.2‖) ≤ 9 * UniformC3_147.c3Size W := by
  have heq : (∑' p : ℤ × ℤ, ‖planeCoeff W p.1 p.2‖) =
      ‖planeCoeff W 0 0‖ + squareTail W 0 := by
    rw [(summable_planeCoeff_norm_pair hW hx hy).tsum_eq_add_tsum_ite (0, 0)]
    congr 1
    apply tsum_congr
    intro p
    by_cases hp : p = (0, 0)
    · simp [hp]
    · have hmax : 0 < max p.1.natAbs p.2.natAbs := by
        by_contra h
        have : p.1.natAbs = 0 ∧ p.2.natAbs = 0 := by omega
        exact hp (Prod.ext (Int.natAbs_eq_zero.mp this.1) (Int.natAbs_eq_zero.mp this.2))
      simp [hp, hmax]
  rw [heq]
  have h0 := planeCoeff_norm_le_c3Size hW hx hy 0 0
  have ht := squareTail_le hW hx hy 0
  norm_num at ht
  linarith

def frequencySquare (R : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(R : ℤ × ℤ)) R

theorem mem_frequencySquare (R : ℕ) (p : ℤ × ℤ) :
    p ∈ frequencySquare R ↔ max p.1.natAbs p.2.natAbs ≤ R := by
  simp only [frequencySquare, Finset.mem_Icc, Prod.le_def,
    Prod.fst_neg, Prod.snd_neg, Prod.fst_natCast, Prod.snd_natCast, max_le_iff]
  omega

def squareTruncation (W : ℝ × ℝ → ℝ) (R : ℕ) : C(UnitAddTorus (Fin 2), ℂ) :=
  ∑ p ∈ frequencySquare R, planeCoeff W p.1 p.2 • UnitAddTorus.mFourier ![p.1, p.2]

theorem hasSum_torus_fourier_pair {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) :
    HasSum (fun p : ℤ × ℤ =>
      planeCoeff W p.1 p.2 • UnitAddTorus.mFourier ![p.1, p.2])
      (torusLift W hW.continuous hx hy) := by
  simpa only [Function.comp_def, finTwoArrowEquiv_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    (finTwoArrowEquiv ℤ).symm.hasSum_iff.mpr (hasSum_torus_fourier hW hx hy)

/-- Uniform finite Fourier approximation with an explicit inverse cutoff error. -/
theorem norm_sub_squareTruncation_le {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (R : ℕ) :
    ‖torusLift W hW.continuous hx hy - squareTruncation W R‖ ≤
      8 * UniformC3_147.c3Size W / ((R : ℝ) + 1) := by
  have hf := (frequencySquare R).hasSum_iff_compl.mp (hasSum_torus_fourier_pair hW hx hy)
  have hg := ((summable_planeCoeff_norm_pair hW hx hy).subtype
    (fun p => p ∉ frequencySquare R)).hasSum
  have hnorm := hf.norm_le_of_bounded hg (fun p => by
    simp only [norm_smul, UnitAddTorus.mFourier_norm, mul_one, Function.comp_apply, le_refl])
  have heq : (∑' p : {p : ℤ × ℤ // p ∉ frequencySquare R},
      ‖planeCoeff W p.val.1 p.val.2‖) = squareTail W R := by
    refine (tsum_subtype {p : ℤ × ℤ | p ∉ frequencySquare R}
      (fun p : ℤ × ℤ => ‖planeCoeff W p.1 p.2‖)).trans ?_
    apply tsum_congr
    intro p
    simp only [Set.indicator_apply, Set.mem_setOf_eq, mem_frequencySquare, not_le,
      squareTail]
  exact hnorm.trans (heq ▸ squareTail_le hW hx hy R)

/-- The Fourier reduction for any continuous linear discrepancy functional.
Only the finitely many square frequencies require a strong estimate. -/
theorem finite_character_transfer {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) (R : ℕ)
    (L : C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] ℂ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmall : ∀ p ∈ frequencySquare R, ‖L (UnitAddTorus.mFourier ![p.1, p.2])‖ ≤ A)
    (hL : ‖L‖ ≤ B) :
    ‖L (torusLift W hW.continuous hx hy)‖ ≤
      9 * A * UniformC3_147.c3Size W +
        8 * B * UniformC3_147.c3Size W / ((R : ℝ) + 1) := by
  have hN : 0 ≤ UniformC3_147.c3Size W :=
    (norm_nonneg (planeCoeff W 0 0)).trans (planeCoeff_norm_le_c3Size hW hx hy 0 0)
  have hlow : ‖L (squareTruncation W R)‖ ≤ 9 * A * UniformC3_147.c3Size W := by
    simp only [squareTruncation, map_sum, map_smul]
    calc
      _ ≤ ∑ p ∈ frequencySquare R, ‖planeCoeff W p.1 p.2‖ * A := by
        apply norm_sum_le_of_le
        intro p hp
        simpa only [norm_smul] using
          mul_le_mul_of_nonneg_left (hsmall p hp) (norm_nonneg _)
      _ = (∑ p ∈ frequencySquare R, ‖planeCoeff W p.1 p.2‖) * A :=
        (Finset.sum_mul ..).symm
      _ ≤ (9 * UniformC3_147.c3Size W) * A := by
        apply mul_le_mul_of_nonneg_right _ hA
        exact ((summable_planeCoeff_norm_pair hW hx hy).sum_le_tsum
          (frequencySquare R) (fun _ _ => norm_nonneg _)).trans (planeCoeff_l1_le hW hx hy)
      _ = _ := by ring
  have hhigh : ‖L (torusLift W hW.continuous hx hy - squareTruncation W R)‖ ≤
      8 * B * UniformC3_147.c3Size W / ((R : ℝ) + 1) := by
    calc
      _ ≤ ‖L‖ * ‖torusLift W hW.continuous hx hy - squareTruncation W R‖ := L.le_opNorm _
      _ ≤ B * (8 * UniformC3_147.c3Size W / ((R : ℝ) + 1)) :=
        mul_le_mul hL (norm_sub_squareTruncation_le hW hx hy R) (norm_nonneg _) hB
      _ = _ := by ring
  have heq : L (torusLift W hW.continuous hx hy) =
      L (squareTruncation W R) + L (torusLift W hW.continuous hx hy - squareTruncation W R) := by
    rw [map_sub]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hlow hhigh)

#print axioms tsum_eq_tsum_box
#print axioms planeCoeff_box_sum_le
#print axioms squareTail_le
#print axioms planeCoeff_l1_le
#print axioms norm_sub_squareTruncation_le
#print axioms finite_character_transfer

end Erdos374.FourierSampling151
end





end Update151_Component_10
/- END COMPONENT: FourierTail151.lean -/

/- BEGIN COMPONENT: FourierSamplerReduction151.lean -/
section Update151_Component_11



noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ContDiff

namespace Erdos374.FourierSampling151
open SamplingClosure147 UniformC3_147

def curveCharacter (b : ℝ) (n m : ℤ) (t : ℝ) : ℂ :=
  unitCharacter n (b / t) * unitCharacter m (b / t ^ 2)

theorem curveCharacter_eq_exp (b : ℝ) (n m : ℤ) (t : ℝ) :
    curveCharacter b n m t = Complex.exp
      (((2 * Real.pi * ((n : ℝ) * b / t + (m : ℝ) * b / t ^ 2) : ℝ) : ℂ) * Complex.I) := by
  simp only [curveCharacter, unitCharacter, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact same-curve discrepancy for one signed integer Fourier frequency. -/
def characterDiscrepancy (P b : ℕ) (n m : ℤ) : ℂ :=
  (∑ p ∈ openPrimeBand P, curveCharacter b n m p) -
    ∫ t in (P : ℝ)..(2 * (P : ℝ)), curveCharacter b n m t / (Real.log t : ℂ)

/-- The still-open oscillatory estimate. The threshold is uniform in b and
every retained nonzero frequency, including both axes and both signs. -/
def FiniteNonzeroCharacterSampling : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ P b : ℕ,
    P₀ ≤ P → 2 ≤ P → 1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) →
    ∀ n m : ℤ, 0 < n.natAbs + m.natAbs →
      n.natAbs + m.natAbs ≤ ⌈(Real.log (P : ℝ)) ^ 6⌉₊ →
      ‖characterDiscrepancy P b n m‖ ≤ C * (P : ℝ) / (Real.log (P : ℝ)) ^ 6

theorem zero_character_sampling :
    ∃ P₀ : ℕ, ∀ P b : ℕ, P₀ ≤ P →
      ‖characterDiscrepancy P b 0 0‖ ≤
        4 * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 := by
  obtain ⟨N, hN⟩ := SamplerConstantClosed150.constant_sampling_unconditional
  refine ⟨N, ?_⟩
  intro P b hP
  have heq : characterDiscrepancy P b 0 0 =
      (((∑ p ∈ openPrimeBand P, (1 : ℝ)) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), 1 / Real.log t : ℝ) : ℂ) := by
    simp only [characterDiscrepancy, curveCharacter, unitCharacter, Int.cast_zero,
      mul_zero, zero_mul, Complex.exp_zero, one_mul]
    push_cast
    rw [← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_div, Complex.ofReal_one]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  simpa only [c3Size_const, abs_one, mul_one] using hN P hP 1

theorem square_cutoff_frequency_le (H : ℕ) {p : ℤ × ℤ}
    (hp : p ∈ frequencySquare (H / 2)) : p.1.natAbs + p.2.natAbs ≤ H := by
  have h := (mem_frequencySquare (H / 2) p).mp hp
  omega

theorem half_ceil_denom (x : ℝ) : x ≤ 2 * ((⌈x⌉₊ / 2 : ℕ) + 1 : ℝ) := by
  have hx : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hh : ⌈x⌉₊ ≤ 2 * (⌈x⌉₊ / 2 + 1) := by omega
  exact hx.trans (by exact_mod_cast hh)

theorem transfer_logarithmic_arithmetic (C N P L : ℝ)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hP : 0 ≤ P) (hL : 0 < L) :
    9 * (C * P / L ^ 6) * N +
      8 * (2 * P) * N / (((⌈L ^ 6⌉₊ / 2 : ℕ) : ℝ) + 1) ≤
      (9 * C + 32) * N * P / L ^ 6 := by
  have hden := half_ceil_denom (L ^ 6)
  have htail : 8 * (2 * P) * N / (((⌈L ^ 6⌉₊ / 2 : ℕ) : ℝ) + 1) ≤
      32 * N * P / L ^ 6 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 16 * N * P by positivity) (sub_nonneg.mpr hden)]
  calc
    _ ≤ 9 * (C * P / L ^ 6) * N + 32 * N * P / L ^ 6 := add_le_add (le_refl _) htail
    _ = _ := by ring

#print axioms zero_character_sampling
#print axioms transfer_logarithmic_arithmetic

end Erdos374.FourierSampling151
end



end Update151_Component_11
/- END COMPONENT: FourierSamplerReduction151.lean -/

/- BEGIN COMPONENT: TorusDiscrepancy151.lean -/
section Update151_Component_12


noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Erdos374.TorusDiscrepancy151
open SamplingClosure147

def curvePoint (b t : ℝ) : UnitAddTorus (Fin 2) :=
  ![((b / t : ℝ) : UnitAddCircle), ((b / t ^ 2 : ℝ) : UnitAddCircle)]

theorem continuousOn_curvePoint (b P : ℝ) (hP : 0 < P) :
    ContinuousOn (curvePoint b) (Set.Icc P (2 * P)) := by
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · change ContinuousOn (fun t : ℝ => ((b / t : ℝ) : UnitAddCircle)) _
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn
      (continuousOn_const.div continuousOn_id (fun t ht => (hP.trans_le ht.1).ne'))
  · change ContinuousOn (fun t : ℝ => ((b / t ^ 2 : ℝ) : UnitAddCircle)) _
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn
      (continuousOn_const.div (continuousOn_id.pow 2)
        (fun t ht => pow_ne_zero 2 (hP.trans_le ht.1).ne'))

theorem weighted_curve_intervalIntegrable (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) (f : C(UnitAddTorus (Fin 2), ℂ)) :
    IntervalIntegrable (fun t : ℝ => f (curvePoint b t) / (Real.log t : ℂ))
      volume (P : ℝ) (2 * P) := by
  have hcont : ContinuousOn (fun t : ℝ => f (curvePoint b t) / (Real.log t : ℂ))
      (Set.Icc (P : ℝ) (2 * P)) := by
    apply (f.continuous.comp_continuousOn (continuousOn_curvePoint b P hPpos)).div
    · exact Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono (fun t ht => (hPpos.trans_le ht.1).ne'))
    · intro t ht
      have hlogt : 1 ≤ Real.log t := hlog.trans (Real.log_le_log hPpos ht.1)
      exact_mod_cast (show Real.log t ≠ 0 by linarith)
  exact hcont.intervalIntegrable_of_Icc (by linarith)

theorem norm_weighted_curve_integral_le (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) (f : C(UnitAddTorus (Fin 2), ℂ)) :
    ‖∫ t in (P : ℝ)..2 * P, f (curvePoint b t) / (Real.log t : ℂ)‖ ≤ (P : ℝ) * ‖f‖ := by
  have hbound : ∀ t ∈ Set.uIoc (P : ℝ) (2 * P),
      ‖f (curvePoint b t) / (Real.log t : ℂ)‖ ≤ ‖f‖ := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : (P : ℝ) ≤ 2 * P)] at ht
    have hlogt : 1 ≤ Real.log t := hlog.trans (Real.log_le_log hPpos ht.1.le)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log t)]
    exact (div_le_self (norm_nonneg _) hlogt).trans (f.norm_coe_le_norm _)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hlen : |2 * (P : ℝ) - P| = P := by rw [abs_of_nonneg (by linarith)]; ring
  calc
    _ ≤ ‖f‖ * |2 * (P : ℝ) - P| := h
    _ = _ := by rw [hlen]; ring

theorem norm_prime_curve_sum_le (P b : ℕ) (f : C(UnitAddTorus (Fin 2), ℂ)) :
    ‖∑ p ∈ openPrimeBand P, f (curvePoint b p)‖ ≤ (P : ℝ) * ‖f‖ := by
  have hcard : (openPrimeBand P).card ≤ P := by
    calc
      _ ≤ (Finset.Ioc P (2 * P)).card := Finset.card_filter_le _ _
      _ = P := by simp [Nat.card_Ioc]; omega
  calc
    _ ≤ ∑ p ∈ openPrimeBand P, ‖f (curvePoint b p)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ openPrimeBand P, ‖f‖ := Finset.sum_le_sum (fun _ _ => f.norm_coe_le_norm _)
    _ = ((openPrimeBand P).card : ℝ) * ‖f‖ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (norm_nonneg _)

def discrepancyLinearMap (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) : C(UnitAddTorus (Fin 2), ℂ) →ₗ[ℂ] ℂ where
  toFun f := (∑ p ∈ openPrimeBand P, f (curvePoint b p)) -
    ∫ t in (P : ℝ)..2 * P, f (curvePoint b t) / (Real.log t : ℂ)
  map_add' f g := by
    change (∑ p ∈ openPrimeBand P, (f (curvePoint b p) + g (curvePoint b p))) -
      (∫ t in (P : ℝ)..2 * P, (f (curvePoint b t) + g (curvePoint b t)) / (Real.log t : ℂ)) = _
    simp_rw [add_div]
    rw [Finset.sum_add_distrib, intervalIntegral.integral_add
      (weighted_curve_intervalIntegrable P b hPpos hlog f)
      (weighted_curve_intervalIntegrable P b hPpos hlog g)]
    ring
  map_smul' c f := by
    change (∑ p ∈ openPrimeBand P, c * f (curvePoint b p)) -
      (∫ t in (P : ℝ)..2 * P, (c * f (curvePoint b t)) / (Real.log t : ℂ)) =
      c * ((∑ p ∈ openPrimeBand P, f (curvePoint b p)) -
        ∫ t in (P : ℝ)..2 * P, f (curvePoint b t) / (Real.log t : ℂ))
    simp_rw [mul_div_assoc]
    rw [← Finset.mul_sum, intervalIntegral.integral_const_mul]
    ring

theorem discrepancyLinearMap_bound (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) (f : C(UnitAddTorus (Fin 2), ℂ)) :
    ‖discrepancyLinearMap P b hPpos hlog f‖ ≤ (2 * (P : ℝ)) * ‖f‖ := by
  exact (norm_sub_le _ _).trans ((add_le_add (norm_prime_curve_sum_le P b f)
    (norm_weighted_curve_integral_le P b hPpos hlog f)).trans_eq (by ring))

def discrepancyCLM (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) : C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] ℂ :=
  (discrepancyLinearMap P b hPpos hlog).mkContinuous (2 * (P : ℝ))
    (discrepancyLinearMap_bound P b hPpos hlog)

theorem discrepancyCLM_apply (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) (f : C(UnitAddTorus (Fin 2), ℂ)) :
    discrepancyCLM P b hPpos hlog f =
      (∑ p ∈ openPrimeBand P, f (curvePoint b p)) -
        ∫ t in (P : ℝ)..2 * P, f (curvePoint b t) / (Real.log t : ℂ) := rfl

theorem norm_discrepancyCLM_le (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) : ‖discrepancyCLM P b hPpos hlog‖ ≤ 2 * (P : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end Erdos374.TorusDiscrepancy151
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.TorusDiscrepancy151.curvePoint,
    ``Erdos374.TorusDiscrepancy151.continuousOn_curvePoint,
    ``Erdos374.TorusDiscrepancy151.weighted_curve_intervalIntegrable,
    ``Erdos374.TorusDiscrepancy151.norm_weighted_curve_integral_le,
    ``Erdos374.TorusDiscrepancy151.norm_prime_curve_sum_le,
    ``Erdos374.TorusDiscrepancy151.discrepancyLinearMap,
    ``Erdos374.TorusDiscrepancy151.discrepancyLinearMap_bound,
    ``Erdos374.TorusDiscrepancy151.discrepancyCLM,
    ``Erdos374.TorusDiscrepancy151.discrepancyCLM_apply,
    ``Erdos374.TorusDiscrepancy151.norm_discrepancyCLM_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.TorusDiscrepancy151.norm_discrepancyCLM_le

end Update151_Component_12
/- END COMPONENT: TorusDiscrepancy151.lean -/

/- BEGIN COMPONENT: FourierPrimeSampling151.lean -/
section Update151_Component_13



noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ContDiff

namespace Erdos374.FourierSampling151
open SamplingClosure147 UniformC3_147 TorusDiscrepancy151

theorem discrepancyCLM_character (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) (n m : ℤ) :
    discrepancyCLM P b hPpos hlog (UnitAddTorus.mFourier ![n, m]) =
      characterDiscrepancy P b n m := by
  rw [discrepancyCLM_apply]
  simp only [characterDiscrepancy, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    curvePoint, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← unitCharacter_eq_fourier, curveCharacter]

theorem discrepancyCLM_real_test (P b : ℕ) (hPpos : 0 < (P : ℝ))
    (hlog : 1 ≤ Real.log (P : ℝ)) (W : ℝ × ℝ → ℝ) (hW : Continuous W)
    (hx : ∀ x y, W (x + 1, y) = W (x, y))
    (hy : ∀ x y, W (x, y + 1) = W (x, y)) :
    discrepancyCLM P b hPpos hlog (torusLift W hW hx hy) =
      (((∑ p ∈ openPrimeBand P, W ((b : ℝ) / p, (b : ℝ) / (p : ℝ) ^ 2)) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)),
          W ((b : ℝ) / t, (b : ℝ) / t ^ 2) / Real.log t : ℝ) : ℂ) := by
  rw [discrepancyCLM_apply]
  simp only [curvePoint, torusLift_coe]
  push_cast
  rw [← intervalIntegral.integral_ofReal]
  simp only [Complex.ofReal_div]

/-- All Fourier analysis and the zero mode are discharged. The sole sampling
input is the explicitly quantified finite nonzero-character estimate NZ6. -/
theorem polynomial_sampling_of_finite_nonzero
    (HS : FiniteNonzeroCharacterSampling) :
    SamplingPolynomial149.PolynomialReciprocalPrimeSampling := by
  intro γ hγ
  obtain ⟨C, hC, N, hN⟩ := HS γ hγ
  obtain ⟨NZ, hNZ⟩ := zero_character_sampling
  obtain ⟨NL, hNL⟩ := RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨9 * max C 4 + 32, by positivity, max N (max NZ NL), ?_⟩
  intro P b hP hP2 hb1 hpoly W hW hx hy
  have hPN : N ≤ P := by omega
  have hPZ : NZ ≤ P := by omega
  have hPL : NL ≤ P := by omega
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hlog : 1 ≤ Real.log (P : ℝ) := hNL P hPL
  have hlogpos : 0 < Real.log (P : ℝ) := by linarith
  have hW3 : ContDiff ℝ 3 W := hW.of_le (by norm_num)
  have hsize : 0 ≤ c3Size W := (norm_nonneg (planeCoeff W 0 0)).trans
    (planeCoeff_norm_le_c3Size hW3 hx hy 0 0)
  let R : ℕ := ⌈(Real.log (P : ℝ)) ^ 6⌉₊ / 2
  let L := discrepancyCLM P b hPpos hlog
  have hsmall : ∀ p ∈ frequencySquare R,
      ‖L (UnitAddTorus.mFourier ![p.1, p.2])‖ ≤
        max C 4 * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 := by
    intro p hp
    dsimp only [L]
    rw [discrepancyCLM_character]
    by_cases hz : p = (0, 0)
    · subst p
      exact (hNZ P b hPZ).trans (by
        gcongr
        exact le_max_right C 4)
    · have hp0 : 0 < p.1.natAbs + p.2.natAbs := by
        by_contra hn
        have habs : p.1.natAbs = 0 ∧ p.2.natAbs = 0 := by omega
        exact hz (Prod.ext (Int.natAbs_eq_zero.mp habs.1) (Int.natAbs_eq_zero.mp habs.2))
      exact (hN P b hPN hP2 hb1 hpoly p.1 p.2 hp0
        (square_cutoff_frequency_le _ hp)).trans (by
          gcongr
          exact le_max_left C 4)
  have hbound := finite_character_transfer hW3 hx hy R L
    (A := max C 4 * (P : ℝ) / (Real.log (P : ℝ)) ^ 6) (B := 2 * (P : ℝ))
    (by positivity) (by positivity) hsmall (norm_discrepancyCLM_le P b hPpos hlog)
  have hfinal := hbound.trans (transfer_logarithmic_arithmetic (max C 4) (c3Size W)
    (P : ℝ) (Real.log (P : ℝ)) (by positivity) hsize hPpos.le hlogpos)
  dsimp only [L] at hfinal
  rw [discrepancyCLM_real_test, Complex.norm_real, Real.norm_eq_abs] at hfinal
  exact hfinal

#print axioms polynomial_sampling_of_finite_nonzero

run_cmd do
  let axioms ← Lean.collectAxioms ``polynomial_sampling_of_finite_nonzero
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in polynomial_sampling_of_finite_nonzero"

end Erdos374.FourierSampling151
end

end Update151_Component_13
/- END COMPONENT: FourierPrimeSampling151.lean -/

/- BEGIN COMPONENT: SmoothSamplingSmall151.lean -/
section Update151_Component_14





/-! Unconditional sampling of smooth periodic weights in the low-variation range. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Erdos374.SmoothSamplingSmall151
open ReciprocalCharacter151 SamplingClosure147 UniformC3_147

def curve (b t : ℝ) : ℝ × ℝ := (b / t, b / t ^ 2)
def curveD (b t : ℝ) : ℝ × ℝ := (-(b / t ^ 2), -(2 * b / t ^ 3))
def test (b : ℝ) (W : ℝ × ℝ → ℝ) (t : ℝ) : ℂ := W (curve b t)
def testD (b : ℝ) (W : ℝ × ℝ → ℝ) (t : ℝ) : ℂ :=
  fderiv ℝ W (curve b t) (curveD b t)

theorem curve_hasDerivAt (b t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (curve b) (curveD b t) t := by
  have h1 := phase_hasDerivAt b 0 t ht
  have h2 := phase_hasDerivAt 0 b t ht
  change HasDerivAt (fun x => (b / x, b / x ^ 2)) _ t
  simpa only [phase, phaseD, zero_div, zero_mul, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, zero_sub, curve, curveD] using h1.prodMk h2

theorem test_hasDerivAt (b t : ℝ) {W : ℝ × ℝ → ℝ}
    (hW : ContDiff ℝ 3 W) (ht : t ≠ 0) :
    HasDerivAt (test b W) (testD b W t) t :=
  (((hW.differentiable (by norm_num)) (curve b t)).hasFDerivAt.comp_hasDerivAt t
    (curve_hasDerivAt b t ht)).ofReal_comp

theorem testD_continuousOn (b a z : ℝ) {W : ℝ × ℝ → ℝ}
    (hW : ContDiff ℝ 3 W) (ha : 0 < a) :
    ContinuousOn (testD b W) (Icc a z) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht0
  have hc := (curve_hasDerivAt b t ht0).continuousAt
  have hd : ContinuousAt (curveD b) t := by unfold curveD; fun_prop
  exact (Complex.continuous_ofReal.continuousAt.comp
    (((hW.continuous_fderiv (by norm_num)).continuousAt.comp hc).clm_apply hd)).continuousWithinAt

variable {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 3 W)
  (hx : ∀ x y, W (x + 1, y) = W (x, y))
  (hy : ∀ x y, W (x, y + 1) = W (x, y))

include hW hx hy

theorem norm_value_le (z : ℝ × ℝ) : ‖W z‖ ≤ c3Size W := by
  simpa only [norm_iteratedFDeriv_zero] using
    FourierSampling151.norm_iteratedFDeriv_le_c3Size hW hx hy (j := 0) (by norm_num) z

theorem norm_fderiv_le (z : ℝ × ℝ) : ‖fderiv ℝ W z‖ ≤ c3Size W := by
  simpa only [norm_iteratedFDeriv_one] using
    FourierSampling151.norm_iteratedFDeriv_le_c3Size hW hx hy (j := 1) (by norm_num) z

theorem c3Size_nonneg : 0 ≤ c3Size W :=
  (norm_nonneg (W (0, 0))).trans (norm_value_le hW hx hy (0, 0))

omit hW hx hy in
theorem norm_curveD_le (b t : ℝ) (ht : 0 < t) :
    ‖curveD b t‖ ≤ majorant b b t := by
  simp only [curveD, Prod.norm_def, norm_neg, Real.norm_eq_abs, abs_div,
    abs_mul, abs_of_pos (pow_pos ht 2), abs_of_pos (pow_pos ht 3),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold majorant
  exact max_le (le_add_of_nonneg_right (by positivity))
    (le_add_of_nonneg_left (by positivity))

theorem norm_testD_le (b t : ℝ) (ht : 0 < t) :
    ‖testD b W t‖ ≤ c3Size W * majorant b b t := by
  rw [testD, Complex.norm_real]
  calc
    _ ≤ ‖fderiv ℝ W (curve b t)‖ * ‖curveD b t‖ :=
      (fderiv ℝ W (curve b t)).le_opNorm _
    _ ≤ c3Size W * majorant b b t :=
      mul_le_mul (norm_fderiv_le hW hx hy _) (norm_curveD_le b t ht)
        (norm_nonneg _) (c3Size_nonneg hW hx hy)

theorem test_variation_le (b P : ℝ) (hP : 0 < P) :
    (∫ t in P..(2 * P), ‖testD b W t‖) ≤ c3Size W * amplitude b b P := by
  have hab : P ≤ 2 * P := by linarith
  have hi : IntervalIntegrable (fun t => ‖testD b W t‖) volume P (2 * P) :=
    (testD_continuousOn b P (2 * P) hW hP).norm.intervalIntegrable_of_Icc hab
  have hm : IntervalIntegrable (majorant b b) volume P (2 * P) :=
    (majorant_continuousOn b b P (2 * P) hP).intervalIntegrable_of_Icc hab
  calc
    _ ≤ ∫ t in P..(2 * P), c3Size W * majorant b b t :=
      intervalIntegral.integral_mono_on hab hi (hm.const_mul _) (by
        intro t ht
        exact norm_testD_le hW hx hy b t (hP.trans_le ht.1))
    _ = c3Size W * (amplitude b b P - amplitude b b (2 * P)) := by
      rw [intervalIntegral.integral_const_mul, majorant_integral b b P (2 * P) hP hab]
    _ ≤ c3Size W * amplitude b b P :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (amplitude_nonneg b b _ (by positivity)))
        (c3Size_nonneg hW hx hy)

omit hW hx hy in
theorem smooth_variation_sampling (A : ℕ) :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → ∀ (b : ℝ) (W : ℝ × ℝ → ℝ),
      ContDiff ℝ 3 W → (∀ x y, W (x + 1, y) = W (x, y)) →
      (∀ x y, W (x, y + 1) = W (x, y)) →
      ‖(∑ p ∈ openPrimeBand P, test b W p) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), test b W t / (Real.log t : ℂ)‖ ≤
      (2 * (P : ℝ) / (Real.log (P : ℝ)) ^ A) *
        c3Size W * (3 + amplitude b b P) := by
  obtain ⟨N, hN⟩ := WeightedPrimeSampling151.weighted_prime_sampling A
  refine ⟨max N 2, ?_⟩
  intro P hP b W hW hx hy
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have h := hN P (by omega) (test b W) (testD b W) (c3Size W)
    (c3Size W * amplitude b b P)
    (by intro t ht; exact test_hasDerivAt b t hW (ne_of_gt (hP0.trans_le ht.1)))
    (testD_continuousOn b P (2 * P) hW hP0)
    (by intro t _; simpa only [test, Complex.norm_real] using norm_value_le hW hx hy (curve b t))
    (test_variation_le hW hx hy b P hP0)
  convert h using 1 <;> ring

omit hW hx hy in
theorem amplitude_le_log_budget (B : ℕ) (b P L : ℝ)
    (hP : 1 ≤ P) (hb : 0 ≤ b) (hbP : b ≤ P * L ^ B) :
    amplitude b b P ≤ 2 * L ^ B := by
  have hP0 : 0 < P := by linarith
  have h1 : b / P ≤ L ^ B := (div_le_iff₀ hP0).mpr (by simpa [mul_comm] using hbP)
  have h2 : b / P ^ 2 ≤ b / P :=
    div_le_div_of_nonneg_left hb hP0 (by nlinarith)
  simp only [amplitude, abs_of_nonneg hb]
  linarith

omit hW hx hy in
/-- Every fixed polylogarithmic range of b/P, with any requested logarithmic saving.
The threshold is chosen before b and W. -/
theorem smooth_small_sampling (A B : ℕ) :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → ∀ (b : ℝ) (W : ℝ × ℝ → ℝ),
      0 ≤ b → b ≤ (P : ℝ) * (Real.log (P : ℝ)) ^ B →
      ContDiff ℝ 3 W → (∀ x y, W (x + 1, y) = W (x, y)) →
      (∀ x y, W (x, y + 1) = W (x, y)) →
      ‖(∑ p ∈ openPrimeBand P, test b W p) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), test b W t / (Real.log t : ℂ)‖ ≤
      10 * c3Size W * (P : ℝ) / (Real.log (P : ℝ)) ^ A := by
  obtain ⟨N, hN⟩ := smooth_variation_sampling (A + B)
  obtain ⟨NL, hNL⟩ := RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨max N (max NL 2), ?_⟩
  intro P hP b W hb hbP hW hx hy
  have hP2 : 2 ≤ P := by omega
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  have hP0 : (0 : ℝ) < P := by linarith
  have hL : 1 ≤ Real.log (P : ℝ) := hNL P (by omega)
  have hL0 : 0 < Real.log (P : ℝ) := by linarith
  have hLB : 1 ≤ (Real.log (P : ℝ)) ^ B := one_le_pow₀ hL
  have hF := amplitude_le_log_budget B b P (Real.log P) hP1 hb hbP
  have hC := c3Size_nonneg hW hx hy
  calc
    _ ≤ (2 * (P : ℝ) / (Real.log (P : ℝ)) ^ (A + B)) *
        c3Size W * (3 + amplitude b b P) := hN P (by omega) b W hW hx hy
    _ ≤ (2 * (P : ℝ) / (Real.log (P : ℝ)) ^ (A + B)) *
        c3Size W * (5 * (Real.log (P : ℝ)) ^ B) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 10 * c3Size W * (P : ℝ) / (Real.log (P : ℝ)) ^ A := by
      rw [pow_add]
      field_simp [ne_of_gt hL0]
      <;> ring

omit hW hx hy in
theorem smooth_small_sampling_real (A B : ℕ) :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → ∀ (b : ℝ) (W : ℝ × ℝ → ℝ),
      0 ≤ b → b ≤ (P : ℝ) * (Real.log (P : ℝ)) ^ B →
      ContDiff ℝ 3 W → (∀ x y, W (x + 1, y) = W (x, y)) →
      (∀ x y, W (x, y + 1) = W (x, y)) →
      |(∑ p ∈ openPrimeBand P, W (b / p, b / (p : ℝ) ^ 2)) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), W (b / t, b / t ^ 2) / Real.log t| ≤
      10 * c3Size W * (P : ℝ) / (Real.log (P : ℝ)) ^ A := by
  obtain ⟨P₀, h⟩ := smooth_small_sampling A B
  refine ⟨P₀, ?_⟩
  intro P hP b W hb hbP hW hx hy
  have hbound := h P hP b W hb hbP hW hx hy
  simpa only [test, curve, ← Complex.ofReal_div, intervalIntegral.integral_ofReal,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hbound

#print axioms smooth_variation_sampling
#print axioms smooth_small_sampling_real
run_cmd do
  for target in [``curve_hasDerivAt, ``test_hasDerivAt, ``norm_testD_le,
      ``test_variation_le, ``smooth_variation_sampling, ``smooth_small_sampling,
      ``smooth_small_sampling_real] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.SmoothSamplingSmall151
end

end Update151_Component_14
/- END COMPONENT: SmoothSamplingSmall151.lean -/

/- BEGIN COMPONENT: ExponentialSum151.lean -/
section Update151_Component_15






/-! Finite van der Corput differencing with its diagonal retained explicitly.
These are proved finite inequalities, not postulated phase-cancellation estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.ExponentialSum151

lemma norm_sum_sq_le_card_energy {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hn := norm_sum_le s f
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  exact hs.trans hc

lemma shift_sum_of_support {E : Type*} [AddCommMonoid E]
    (s T : Finset ℤ) (f : ℤ → E) (h : ℤ)
    (hz : ∀ n ∉ s, f n = 0) (hT : ∀ n ∈ s, n - h ∈ T) :
    (∑ x ∈ T, f (x + h)) = ∑ n ∈ s, f n := by
  have himg : s.image (fun n => n - h) ⊆ T := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact hT n hn
  calc
    _ = ∑ x ∈ s.image (fun n => n - h), f (x + h) := by
      apply (Finset.sum_subset himg ?_).symm
      intro x hx hxnot
      apply hz
      intro hmem
      apply hxnot
      exact Finset.mem_image.mpr ⟨x + h, hmem, by omega⟩
    _ = _ := by
      rw [Finset.sum_image]
      · simp only [sub_add_cancel]
      · intro a ha b hb hab
        dsimp only at hab
        omega

lemma norm_sum_sq_eq_correlations {ι : Type*} (H : Finset ι) (z : ι → ℂ) :
    ‖∑ h ∈ H, z h‖ ^ 2 =
      ∑ h ∈ H, ∑ k ∈ H, (z h * conj (z k)).re := by
  have heq := congrArg Complex.re (Complex.mul_conj' (∑ h ∈ H, z h))
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum,
    ← Complex.ofReal_pow, Complex.ofReal_re] at heq
  exact heq.symm.trans (Finset.sum_comm)

def correlation (T : Finset ℤ) (f : ℤ → ℂ) (h k : ℤ) : ℂ :=
  ∑ x ∈ T, f (x + h) * conj (f (x + k))

lemma shift_energy_eq_correlations (T H : Finset ℤ) (f : ℤ → ℂ) :
    (∑ x ∈ T, ‖∑ h ∈ H, f (x + h)‖ ^ 2) =
      ∑ h ∈ H, ∑ k ∈ H, (correlation T f h k).re := by
  simp_rw [norm_sum_sq_eq_correlations]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  simp only [correlation, Complex.re_sum]

lemma correlation_diagonal (s T : Finset ℤ) (f : ℤ → ℂ) (h : ℤ)
    (hz : ∀ n ∉ s, f n = 0) (hT : ∀ n ∈ s, n - h ∈ T) :
    (correlation T f h h).re = ∑ n ∈ s, ‖f n‖ ^ 2 := by
  simp only [correlation, Complex.re_sum, Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.ofReal_re]
  apply shift_sum_of_support s T (fun n => ‖f n‖ ^ 2) h _ hT
  intro n hn
  simp [hz n hn]

/-- The diagonal energy is separated before taking absolute values of the
off-diagonal correlations. In particular zero phase differences are retained. -/
lemma shift_energy_le (s T H : Finset ℤ) (f : ℤ → ℂ)
    (hz : ∀ n ∉ s, f n = 0)
    (hT : ∀ n ∈ s, ∀ h ∈ H, n - h ∈ T) :
    (∑ x ∈ T, ‖∑ h ∈ H, f (x + h)‖ ^ 2) ≤
      (H.card : ℝ) * (∑ n ∈ s, ‖f n‖ ^ 2) +
        ∑ h ∈ H, ∑ k ∈ H.erase h, ‖correlation T f h k‖ := by
  rw [shift_energy_eq_correlations]
  calc
    _ = ∑ h ∈ H, ((correlation T f h h).re +
        ∑ k ∈ H.erase h, (correlation T f h k).re) := by
      apply Finset.sum_congr rfl
      intro h hh
      exact (Finset.add_sum_erase H (fun k => (correlation T f h k).re) hh).symm
    _ ≤ ∑ h ∈ H, ((∑ n ∈ s, ‖f n‖ ^ 2) +
        ∑ k ∈ H.erase h, ‖correlation T f h k‖) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [correlation_diagonal s T f h hz (fun n hn => hT n hn h hh)]
      apply add_le_add le_rfl
      exact Finset.sum_le_sum (fun k hk => Complex.re_le_norm _)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

/-- Finite van der Corput differencing over arbitrary containing sets.
The shifted support condition is exact and there are no boundary-error terms. -/
theorem van_der_corput_finite (s T H : Finset ℤ) (f : ℤ → ℂ)
    (hz : ∀ n ∉ s, f n = 0)
    (hT : ∀ n ∈ s, ∀ h ∈ H, n - h ∈ T) :
    (H.card : ℝ) ^ 2 * ‖∑ n ∈ s, f n‖ ^ 2 ≤
      (T.card : ℝ) * ((H.card : ℝ) * (∑ n ∈ s, ‖f n‖ ^ 2) +
        ∑ h ∈ H, ∑ k ∈ H.erase h, ‖correlation T f h k‖) := by
  have hsum : (∑ x ∈ T, ∑ h ∈ H, f (x + h)) =
      (H.card : ℂ) * ∑ n ∈ s, f n := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ _h ∈ H, ∑ n ∈ s, f n := by
        apply Finset.sum_congr rfl
        intro h hh
        exact shift_sum_of_support s T f h hz (fun n hn => hT n hn h hh)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc := norm_sum_sq_le_card_energy T (fun x => ∑ h ∈ H, f (x + h))
  rw [hsum, norm_mul, Complex.norm_natCast, mul_pow] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (shift_energy_le s T H f hz hT) (by positivity))

/-- The usual bounded-sequence form, still with the diagonal explicitly present. -/
theorem van_der_corput_finite_unit (s T H : Finset ℤ) (f : ℤ → ℂ)
    (hz : ∀ n ∉ s, f n = 0)
    (hT : ∀ n ∈ s, ∀ h ∈ H, n - h ∈ T)
    (hf : ∀ n ∈ s, ‖f n‖ ≤ 1) :
    (H.card : ℝ) ^ 2 * ‖∑ n ∈ s, f n‖ ^ 2 ≤
      (T.card : ℝ) * ((H.card : ℝ) * (s.card : ℝ) +
        ∑ h ∈ H, ∑ k ∈ H.erase h, ‖correlation T f h k‖) := by
  have he : (∑ n ∈ s, ‖f n‖ ^ 2) ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have := hf n hn
        nlinarith [norm_nonneg (f n)]
      _ = _ := by simp
  apply (van_der_corput_finite s T H f hz hT).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T.card)
  exact add_le_add (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg H.card)) le_rfl

lemma card_integer_interval (N : ℕ) :
    (Finset.Ico (0 : ℤ) (N : ℤ)).card = N := by
  rw [Int.card_Ico]
  simp

lemma card_shift_interval (N H : ℕ) :
    (Finset.Ico (-(H : ℤ)) (N : ℤ)).card = N + H := by
  rw [Int.card_Ico]
  have he : (N : ℤ) - -(H : ℤ) = ((N + H : ℕ) : ℤ) := by omega
  rw [he]
  omega

/-- Interval specialization, with shifts `0,...,H-1` and containing interval
`[-H,N)`. No assumption `H ≤ N` is necessary. -/
theorem van_der_corput_interval_supported (N H : ℕ) (f : ℤ → ℂ)
    (hz : ∀ n ∉ Finset.Ico (0 : ℤ) (N : ℤ), f n = 0)
    (hf : ∀ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), ‖f n‖ ≤ 1) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), f n‖ ^ 2 ≤
      ((N : ℝ) + H) * ((H : ℝ) * N +
        ∑ h ∈ Finset.Ico (0 : ℤ) (H : ℤ),
          ∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
            ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) f h k‖) := by
  have hT : ∀ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      ∀ h ∈ Finset.Ico (0 : ℤ) (H : ℤ),
      n - h ∈ Finset.Ico (-(H : ℤ)) (N : ℤ) := by
    intro n hn h hh
    simp only [Finset.mem_Ico] at *
    omega
  simpa only [card_integer_interval, card_shift_interval, Nat.cast_add] using
    van_der_corput_finite_unit (Finset.Ico (0 : ℤ) (N : ℤ))
      (Finset.Ico (-(H : ℤ)) (N : ℤ)) (Finset.Ico (0 : ℤ) (H : ℤ)) f hz hT hf

/-- Zero extension is made explicit so arbitrary phases can be used directly. -/
def intervalSequence (N : ℕ) (g : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n ∈ Finset.Ico (0 : ℤ) (N : ℤ) then g n else 0

theorem van_der_corput_interval (N H : ℕ) (g : ℤ → ℂ)
    (hg : ∀ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), ‖g n‖ ≤ 1) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), g n‖ ^ 2 ≤
      ((N : ℝ) + H) * ((H : ℝ) * N +
        ∑ h ∈ Finset.Ico (0 : ℤ) (H : ℤ),
          ∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
            ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ))
              (intervalSequence N g) h k‖) := by
  have hs : (∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), intervalSequence N g n) =
      ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), g n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [intervalSequence, hn]
  have hz : ∀ n ∉ Finset.Ico (0 : ℤ) (N : ℤ), intervalSequence N g n = 0 := by
    intro n hn
    simp [intervalSequence, hn]
  have hf : ∀ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), ‖intervalSequence N g n‖ ≤ 1 := by
    intro n hn
    simpa [intervalSequence, hn] using hg n hn
  simpa only [hs] using van_der_corput_interval_supported N H (intervalSequence N g) hz hf

#print axioms van_der_corput_finite
#print axioms van_der_corput_interval
run_cmd do
  let targets : List Lean.Name := [
    ``norm_sum_sq_le_card_energy,
    ``shift_sum_of_support,
    ``norm_sum_sq_eq_correlations,
    ``shift_energy_eq_correlations,
    ``correlation_diagonal,
    ``shift_energy_le,
    ``van_der_corput_finite,
    ``van_der_corput_finite_unit,
    ``van_der_corput_interval_supported,
    ``van_der_corput_interval]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ExponentialSum151
end

end Update151_Component_15
/- END COMPONENT: ExponentialSum151.lean -/

/- BEGIN COMPONENT: KusminLandau151.lean -/
section Update151_Component_16




/-! A discrete first-derivative estimate from exact summation by parts.
All separation, monotonicity, and endpoint terms are explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace Erdos374.KusminLandau151

def e (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cot_antitone_on (x y : ℝ) (hx : 0 < x) (hy : y < Real.pi) (hxy : x ≤ y) :
    Real.cos y / Real.sin y ≤ Real.cos x / Real.sin x := by
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (hxy.trans_lt hy)
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi (hx.trans_le hxy) hy
  apply (div_le_div_iff₀ hsy hsx).mpr
  have hsub := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hxy)
    (show y - x ≤ Real.pi by linarith)
  rw [Real.sin_sub] at hsub
  nlinarith

lemma sin_pi_mul_lower (δ x : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hx : δ ≤ x) (hx' : x ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * x) := by
  by_cases hhalf : x ≤ 1 / 2
  · have hp0 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le (hδ.le.trans hx)
    have hp : Real.pi * x ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hh := Real.mul_le_sin hp0 hp
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by
      field_simp
    rw [heq] at hh
    linarith
  · have hp0 : 0 ≤ Real.pi * (1 - x) := by nlinarith [Real.pi_pos]
    have hp : Real.pi * (1 - x) ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hh := Real.mul_le_sin hp0 hp
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by
      field_simp
    rw [heq] at hh
    have hs : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [hs, Real.sin_pi_sub] at hh
    linarith

def q (x : ℝ) : ℝ := - (Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) / 2

def lineWeight (t : ℝ) : ℂ := (-1 / 2 : ℝ) + (t : ℂ) * Complex.I

lemma q_monotone (x y : ℝ) (hx : 0 < x) (hy : y < 1) (hxy : x ≤ y) :
    q x ≤ q y := by
  have h := cot_antitone_on (Real.pi * x) (Real.pi * y)
    (mul_pos Real.pi_pos hx) (by nlinarith [Real.pi_pos])
    (mul_le_mul_of_nonneg_left hxy Real.pi_pos.le)
  unfold q
  linarith

lemma q_bound (δ x : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hx : δ ≤ x) (hx' : x ≤ 1 - δ) : |q x| ≤ 1 / (4 * δ) := by
  have hs := sin_pi_mul_lower δ x hδ hδhalf hx hx'
  have hs0 : 0 < Real.sin (Real.pi * x) := by linarith
  have hc := Real.abs_cos_le_one (Real.pi * x)
  unfold q
  rw [abs_div, abs_neg, abs_div, abs_of_pos hs0,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply (div_le_iff₀ hs0).mpr
  have heq : (1 / (4 * δ) * 2) * Real.sin (Real.pi * x) =
      Real.sin (Real.pi * x) / (2 * δ) := by ring
  rw [heq]
  exact hc.trans ((le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr (by linarith))

lemma factor_identity (x : ℝ) (hx : 0 < x) (hx' : x < 1) :
    (e x - 1) * lineWeight (q x) = 1 := by
  have hs : Real.sin (Real.pi * x) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx)
      (by nlinarith [Real.pi_pos])).ne'
  unfold e lineWeight q
  rw [Complex.exp_ofReal_mul_I]
  have htw : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
  rw [htw, Real.cos_two_mul_eq_one_sub, Real.sin_two_mul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    field_simp [hs]
    nlinarith [congrArg (fun t : ℝ => t * Real.sin (Real.pi * x))
      (Real.sin_sq_add_cos_sq (Real.pi * x))]
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, mul_zero,
      zero_mul, sub_zero, add_zero, zero_add]
    field_simp [hs]
    ring

lemma summation_by_parts (z w : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (z (n + 1) - z n) * w n) =
      z (N + 1) * w N - z 0 * w 0 -
        ∑ n ∈ Finset.range N, z (n + 1) * (w (n + 1) - w n) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

lemma norm_lineWeight_le (t : ℝ) : ‖lineWeight t‖ ≤ 1 / 2 + |t| := by
  unfold lineWeight
  have hh := norm_add_le ((-1 / 2 : ℝ) : ℂ) ((t : ℂ) * Complex.I)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_div, abs_neg, abs_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using hh

lemma norm_lineWeight_sub (x y : ℝ) : ‖lineWeight x - lineWeight y‖ = |x - y| := by
  have heq : lineWeight x - lineWeight y = ((x - y : ℝ) : ℂ) * Complex.I := by
    unfold lineWeight
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]

lemma lineWeight_variation_le (r : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hb : ∀ n ≤ N, |r n| ≤ C)
    (hm : MonotoneOn r (Set.Iic N) ∨ AntitoneOn r (Set.Iic N)) :
    (∑ n ∈ Finset.range N, ‖lineWeight (r (n + 1)) - lineWeight (r n)‖) ≤ 2 * C := by
  simp_rw [norm_lineWeight_sub]
  have hbN := abs_le.mp (hb N le_rfl)
  have hb0 := abs_le.mp (hb 0 (Nat.zero_le N))
  rcases hm with hm | hm
  · have he : (∑ n ∈ Finset.range N, |r (n + 1) - r n|) =
        ∑ n ∈ Finset.range N, (r (n + 1) - r n) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnN := Finset.mem_range.mp hn
      apply abs_of_nonneg
      apply sub_nonneg.mpr
      exact hm (by simp only [Set.mem_Iic]; omega)
        (by simp only [Set.mem_Iic]; omega) (Nat.le_succ n)
    rw [he, Finset.sum_range_sub]
    linarith
  · have he : (∑ n ∈ Finset.range N, |r (n + 1) - r n|) =
        -∑ n ∈ Finset.range N, (r (n + 1) - r n) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      have hnN := Finset.mem_range.mp hn
      apply abs_of_nonpos
      apply sub_nonpos.mpr
      exact hm (by simp only [Set.mem_Iic]; omega)
        (by simp only [Set.mem_Iic]; omega) (Nat.le_succ n)
    rw [he, Finset.sum_range_sub]
    linarith

lemma phase_step (f : ℕ → ℝ) (n : ℕ)
    (h0 : 0 < f (n + 1) - f n) (h1 : f (n + 1) - f n < 1) :
    (e (f (n + 1)) - e (f n)) * lineWeight (q (f (n + 1) - f n)) = e (f n) := by
  have he : e (f (n + 1)) = e (f n) * e (f (n + 1) - f n) := by
    rw [← e_add]
    congr 1
    ring
  rw [he, ← mul_sub_one, mul_assoc, factor_identity _ h0 h1, mul_one]

/-- Discrete first-derivative cancellation with either direction of monotonicity.
The separation assumptions are only imposed on the increments actually used. -/
theorem kusmin_landau_succ (N : ℕ) (f : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hd : ∀ n ≤ N, δ ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ 1 - δ)
    (hm : MonotoneOn (fun n => f (n + 1) - f n) (Set.Iic N) ∨
      AntitoneOn (fun n => f (n + 1) - f n) (Set.Iic N)) :
    ‖∑ n ∈ Finset.range (N + 1), e (f n)‖ ≤ 2 / δ := by
  let r : ℕ → ℝ := fun n => q (f (n + 1) - f n)
  let C : ℝ := 1 / (4 * δ)
  have hb : ∀ n ≤ N, |r n| ≤ C := by
    intro n hn
    exact q_bound δ _ hδ hδhalf (hd n hn).1 (hd n hn).2
  have hrm : MonotoneOn r (Set.Iic N) ∨ AntitoneOn r (Set.Iic N) := by
    rcases hm with hm | hm
    · left
      intro m hmN n hnN hmn
      exact q_monotone _ _ (hδ.trans_le (hd m hmN).1)
        (by have := (hd n hnN).2; linarith) (hm hmN hnN hmn)
    · right
      intro m hmN n hnN hmn
      exact q_monotone _ _ (hδ.trans_le (hd n hnN).1)
        (by have := (hd m hmN).2; linarith) (hm hmN hnN hmn)
  have he : (∑ n ∈ Finset.range (N + 1), e (f n)) =
      e (f (N + 1)) * lineWeight (r N) - e (f 0) * lineWeight (r 0) -
        ∑ n ∈ Finset.range N,
          e (f (n + 1)) * (lineWeight (r (n + 1)) - lineWeight (r n)) := by
    rw [← summation_by_parts (fun n => e (f n)) (fun n => lineWeight (r n)) N]
    apply Finset.sum_congr rfl
    intro n hn
    have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
    exact (phase_step f n (hδ.trans_le (hd n hnN).1)
      (by have := (hd n hnN).2; linarith)).symm
  have hend : ∀ n ≤ N, ‖lineWeight (r n)‖ ≤ 1 / 2 + C := by
    intro n hn
    exact (norm_lineWeight_le _).trans (add_le_add le_rfl (hb n hn))
  have hvar := lineWeight_variation_le r N C hb hrm
  have hsum : ‖∑ n ∈ Finset.range (N + 1), e (f n)‖ ≤ 1 + 4 * C := by
    rw [he]
    calc
      _ ≤ ‖e (f (N + 1)) * lineWeight (r N) - e (f 0) * lineWeight (r 0)‖ +
          ‖∑ n ∈ Finset.range N,
            e (f (n + 1)) * (lineWeight (r (n + 1)) - lineWeight (r n))‖ :=
        norm_sub_le _ _
      _ ≤ (‖e (f (N + 1)) * lineWeight (r N)‖ + ‖e (f 0) * lineWeight (r 0)‖) +
          ∑ n ∈ Finset.range N,
            ‖e (f (n + 1)) * (lineWeight (r (n + 1)) - lineWeight (r n))‖ :=
        add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
      _ = (‖lineWeight (r N)‖ + ‖lineWeight (r 0)‖) +
          ∑ n ∈ Finset.range N, ‖lineWeight (r (n + 1)) - lineWeight (r n)‖ := by
        simp only [norm_mul, norm_e, one_mul]
      _ ≤ (1 / 2 + C + (1 / 2 + C)) + 2 * C :=
        add_le_add (add_le_add (hend N le_rfl) (hend 0 (Nat.zero_le _))) hvar
      _ = _ := by ring
  apply hsum.trans
  apply (le_div_iff₀ hδ).mpr
  have hC : 4 * C * δ = 1 := by
    dsimp [C]
    field_simp
  nlinarith

/-- Kusmin–Landau for a sum of length `N`, with constant `2`.
The increment sequence may be monotone or antitone on `[0,N)`. -/
theorem kusmin_landau (N : ℕ) (f : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hd : ∀ n < N, δ ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ 1 - δ)
    (hm : MonotoneOn (fun n => f (n + 1) - f n) (Set.Iio N) ∨
      AntitoneOn (fun n => f (n + 1) - f n) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range N, e (f n)‖ ≤ 2 / δ := by
  cases N with
  | zero => simp; positivity
  | succ N =>
    have hset : Set.Iio (N + 1) = Set.Iic N := by ext n; simp
    apply kusmin_landau_succ N f δ hδ hδhalf
    · intro n hn
      exact hd n (by omega)
    · simpa only [Nat.succ_eq_add_one, hset] using hm

lemma e_int (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  have he : ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I =
      (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma e_sub_int (x : ℝ) (k : ℤ) : e (x - (k : ℝ)) = e x := by
  have h := e_add (x - (k : ℝ)) (k : ℝ)
  simpa only [sub_add_cancel, e_int, mul_one] using h.symm

/-- The same cancellation estimate on any gap between consecutive integers.
In particular `k = -1` handles negative reciprocal-phase increments. -/
theorem kusmin_landau_integer (N : ℕ) (f : ℕ → ℝ) (δ : ℝ) (k : ℤ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hd : ∀ n < N, (k : ℝ) + δ ≤ f (n + 1) - f n ∧
      f (n + 1) - f n ≤ (k : ℝ) + 1 - δ)
    (hm : MonotoneOn (fun n => f (n + 1) - f n) (Set.Iio N) ∨
      AntitoneOn (fun n => f (n + 1) - f n) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range N, e (f n)‖ ≤ 2 / δ := by
  let F : ℕ → ℝ := fun n => f n - (k : ℝ) * (n : ℝ)
  have hstep (n : ℕ) : F (n + 1) - F n = f (n + 1) - f n - (k : ℝ) := by
    dsimp [F]
    push_cast
    ring
  have he (n : ℕ) : e (F n) = e (f n) := by
    dsimp [F]
    have hk : (k : ℝ) * (n : ℝ) = ((k * (n : ℤ) : ℤ) : ℝ) := by push_cast; rfl
    rw [hk, e_sub_int]
  have hd' : ∀ n < N, δ ≤ F (n + 1) - F n ∧ F (n + 1) - F n ≤ 1 - δ := by
    intro n hn
    rw [hstep]
    have := hd n hn
    constructor <;> linarith
  have hm' : MonotoneOn (fun n => F (n + 1) - F n) (Set.Iio N) ∨
      AntitoneOn (fun n => F (n + 1) - F n) (Set.Iio N) := by
    rcases hm with hm | hm
    · left
      intro m hmN n hnN hmn
      dsimp only
      rw [hstep, hstep]
      have := hm hmN hnN hmn
      linarith
    · right
      intro m hmN n hnN hmn
      dsimp only
      rw [hstep, hstep]
      have := hm hmN hnN hmn
      linarith
  simpa only [he] using kusmin_landau N F δ hδ hδhalf hd' hm'

#print axioms kusmin_landau
#print axioms kusmin_landau_integer
run_cmd do
  let targets : List Lean.Name := [
    ``cot_antitone_on, ``sin_pi_mul_lower, ``q_bound, ``factor_identity,
    ``summation_by_parts, ``lineWeight_variation_le,
    ``kusmin_landau_succ, ``kusmin_landau, ``kusmin_landau_integer]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.KusminLandau151
end

end Update151_Component_16
/- END COMPONENT: KusminLandau151.lean -/

/- BEGIN COMPONENT: SecondDerivative151.lean -/
section Update151_Component_17



/-! A discrete second-derivative ingredient.  Cancellation of every shifted
phase is derived from finite second differences and the checked first-derivative
test; no small-correlation hypothesis is postulated. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.SecondDerivative151
open Erdos374.KusminLandau151

def increment (f : ℕ → ℝ) (n : ℕ) : ℝ := f (n + 1) - f n

def secondDifference (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  increment f (n + 1) - increment f n

def shiftedPhase (f : ℕ → ℝ) (h n : ℕ) : ℝ := f (n + h) - f n

lemma shifted_increment_eq_sum (f : ℕ → ℝ) (h n : ℕ) :
    increment (shiftedPhase f h) n =
      ∑ j ∈ Finset.range h, secondDifference f (n + j) := by
  have ht := Finset.sum_range_sub (fun j => increment f (n + j)) h
  have he : increment (shiftedPhase f h) n = increment f (n + h) - increment f n := by
    unfold increment shiftedPhase
    rw [show n + 1 + h = n + h + 1 by omega]
    ring
  rw [he]
  symm
  simpa only [secondDifference, Nat.add_assoc, Nat.add_zero] using ht

lemma shifted_increment_bounds (f : ℕ → ℝ) (N h n : ℕ) (L U : ℝ)
    (hn : n < N - h)
    (hd : ∀ m < N, L ≤ secondDifference f m ∧ secondDifference f m ≤ U) :
    (h : ℝ) * L ≤ increment (shiftedPhase f h) n ∧
      increment (shiftedPhase f h) n ≤ (h : ℝ) * U := by
  rw [shifted_increment_eq_sum]
  constructor
  · calc
      _ = ∑ _j ∈ Finset.range h, L := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjh := Finset.mem_range.mp hj
        exact (hd (n + j) (by omega)).1
  · calc
      _ ≤ ∑ _j ∈ Finset.range h, U := by
        apply Finset.sum_le_sum
        intro j hj
        have hjh := Finset.mem_range.mp hj
        exact (hd (n + j) (by omega)).2
      _ = _ := by simp

lemma shifted_increment_monotone (f : ℕ → ℝ) (N h : ℕ)
    (hm : MonotoneOn (secondDifference f) (Set.Iio N) ∨
      AntitoneOn (secondDifference f) (Set.Iio N)) :
    MonotoneOn (increment (shiftedPhase f h)) (Set.Iio (N - h)) ∨
      AntitoneOn (increment (shiftedPhase f h)) (Set.Iio (N - h)) := by
  rcases hm with hm | hm
  · left
    intro m hmN n hnN hmn
    rw [shifted_increment_eq_sum, shifted_increment_eq_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjh := Finset.mem_range.mp hj
    exact hm (by simp only [Set.mem_Iio] at *; omega)
      (by simp only [Set.mem_Iio] at *; omega) (by omega)
  · right
    intro m hmN n hnN hmn
    rw [shifted_increment_eq_sum, shifted_increment_eq_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjh := Finset.mem_range.mp hj
    exact hm (by simp only [Set.mem_Iio] at *; omega)
      (by simp only [Set.mem_Iio] at *; omega) (by omega)

/-- Actual cancellation of a phase difference, derived from second differences.
The additional monotonicity of the second differences is explicit; it is
available for a single reciprocal phase and must be checked in applications. -/
theorem shifted_phase_cancellation (f : ℕ → ℝ) (N h : ℕ) (L U : ℝ)
    (hh : 0 < h) (hL : 0 < L) (hU : (h : ℝ) * U ≤ 1 / 2)
    (hd : ∀ m < N, L ≤ secondDifference f m ∧ secondDifference f m ≤ U)
    (hm : MonotoneOn (secondDifference f) (Set.Iio N) ∨
      AntitoneOn (secondDifference f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range (N - h), KusminLandau151.e (shiftedPhase f h n)‖ ≤ 2 / ((h : ℝ) * L) := by
  by_cases hhN : h < N
  · have hδ : 0 < (h : ℝ) * L := mul_pos (Nat.cast_pos.mpr hh) hL
    have hLU : L ≤ U := (hd 0 (by omega)).1.trans (hd 0 (by omega)).2
    have hδhalf : (h : ℝ) * L ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hLU (Nat.cast_nonneg h)).trans hU
    apply kusmin_landau (N - h) (shiftedPhase f h) ((h : ℝ) * L) hδ hδhalf
    · intro n hn
      have hb := shifted_increment_bounds f N h n L U hn hd
      change (h : ℝ) * L ≤ increment (shiftedPhase f h) n ∧
        increment (shiftedPhase f h) n ≤ 1 - (h : ℝ) * L
      exact ⟨hb.1, by linarith [hb.2]⟩
    · exact shifted_increment_monotone f N h hm
  · have he : N - h = 0 := by omega
    rw [he]
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity

def reciprocalPhase (a u : ℝ) (n : ℕ) : ℝ := u / (a + (n : ℝ))

lemma reciprocal_secondDifference (a u : ℝ) (ha : 0 < a) (n : ℕ) :
    secondDifference (reciprocalPhase a u) n =
      2 * u / ((a + (n : ℝ)) * (a + (n : ℝ) + 1) * (a + (n : ℝ) + 2)) := by
  have h0 : a + (n : ℝ) ≠ 0 := by positivity
  have h1 : a + (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : a + (n : ℝ) + 2 ≠ 0 := by positivity
  unfold secondDifference increment reciprocalPhase
  push_cast
  have he : a + ((n : ℝ) + 1 + 1) = a + (n : ℝ) + 2 := by ring
  rw [he]
  simp only [← add_assoc]
  field_simp [h0, h1, h2]
  ring

lemma reciprocal_secondDifference_antitone (a u : ℝ) (ha : 0 < a) (hu : 0 ≤ u) :
    Antitone (secondDifference (reciprocalPhase a u)) := by
  intro m n hmn
  rw [reciprocal_secondDifference a u ha m, reciprocal_secondDifference a u ha n]
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

lemma reciprocal_secondDifference_bounds (a u : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (N n : ℕ) (hn : n < N) :
    2 * u / (a + (N : ℝ) + 2) ^ 3 ≤ secondDifference (reciprocalPhase a u) n ∧
      secondDifference (reciprocalPhase a u) n ≤ 2 * u / a ^ 3 := by
  rw [reciprocal_secondDifference a u ha n]
  have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.le
  have hlo : a ^ 3 ≤ (a + (n : ℝ)) * (a + (n : ℝ) + 1) * (a + (n : ℝ) + 2) := by
    calc
      _ = a * a * a := by ring
      _ ≤ _ :=
        mul_le_mul
          (mul_le_mul (by linarith [Nat.cast_nonneg (α := ℝ) n])
            (by linarith [Nat.cast_nonneg (α := ℝ) n]) ha.le (by positivity))
          (by linarith [Nat.cast_nonneg (α := ℝ) n]) ha.le (by positivity)
  have hhi : (a + (n : ℝ)) * (a + (n : ℝ) + 1) * (a + (n : ℝ) + 2) ≤
      (a + (N : ℝ) + 2) ^ 3 := by
    calc
      _ ≤ (a + (N : ℝ) + 2) * (a + (N : ℝ) + 2) * (a + (N : ℝ) + 2) := by
        exact mul_le_mul
          (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
          (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  constructor
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hhi
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hlo

/-- A fully proved reciprocal-phase correlation bound, with no monotonicity or
second-difference premise remaining for the phase itself. -/
theorem reciprocal_shifted_cancellation (a u : ℝ) (N h : ℕ)
    (ha : 0 < a) (hu : 0 < u) (hh : 0 < h)
    (hsmall : (h : ℝ) * (2 * u / a ^ 3) ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range (N - h),
      KusminLandau151.e (u / (a + (n + h : ℕ)) - u / (a + (n : ℝ)))‖ ≤
        2 / ((h : ℝ) * (2 * u / (a + (N : ℝ) + 2) ^ 3)) := by
  apply shifted_phase_cancellation (reciprocalPhase a u) N h
    (2 * u / (a + (N : ℝ) + 2) ^ 3) (2 * u / a ^ 3) hh (by positivity) hsmall
  · intro n hn
    exact reciprocal_secondDifference_bounds a u ha hu.le N n hn
  · right
    intro m hm n hn hmn
    exact reciprocal_secondDifference_antitone a u ha hu.le hmn

#print axioms shifted_phase_cancellation
#print axioms reciprocal_shifted_cancellation
run_cmd do
  let targets : List Lean.Name := [``shifted_increment_eq_sum,
    ``shifted_increment_bounds, ``shifted_increment_monotone, ``shifted_phase_cancellation,
    ``reciprocal_secondDifference, ``reciprocal_secondDifference_antitone,
    ``reciprocal_secondDifference_bounds, ``reciprocal_shifted_cancellation]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.SecondDerivative151
end



end Update151_Component_17
/- END COMPONENT: SecondDerivative151.lean -/

/- BEGIN COMPONENT: SecondDerivativeVdC151.lean -/
section Update151_Component_18



/-! The exact correlation bridge needed to combine finite differencing with
the first-derivative bounds for shifted phases. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.SecondDerivativeVdC151
open Erdos374.ExponentialSum151 Erdos374.KusminLandau151 Erdos374.SecondDerivative151

lemma sum_Ico_int_eq_sum_range {E : Type*} [AddCommMonoid E] (N : ℕ) (g : ℤ → E) :
    (∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), g n) = ∑ n ∈ Finset.range N, g (n : ℤ) := by
  have he : Finset.Ico (0 : ℤ) (N : ℤ) = (Finset.range N).image (fun n : ℕ => (n : ℤ)) := by
    ext n
    constructor
    · intro hn
      have hn' := Finset.mem_Ico.mp hn
      refine Finset.mem_image.mpr ⟨n.toNat, Finset.mem_range.mpr (by omega), by omega⟩
    · intro hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
      have hmN := Finset.mem_range.mp hm
      simp only [Finset.mem_Ico]
      omega
  rw [he, Finset.sum_image]
  intro a ha b hb hab
  dsimp only at hab
  exact_mod_cast hab

lemma e_mul_conj (x y : ℝ) : KusminLandau151.e x * conj (KusminLandau151.e y) = KusminLandau151.e (x - y) := by
  have hc : conj (KusminLandau151.e y) = KusminLandau151.e (-y) := by
    unfold KusminLandau151.e
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hc, ← e_add, sub_eq_add_neg]

def phaseSequence (N : ℕ) (f : ℕ → ℝ) (n : ℤ) : ℂ :=
  if n ∈ Finset.Ico (0 : ℤ) (N : ℤ) then KusminLandau151.e (f n.toNat) else 0

lemma phaseSequence_support (N : ℕ) (f : ℕ → ℝ) :
    ∀ n ∉ Finset.Ico (0 : ℤ) (N : ℤ), phaseSequence N f n = 0 := by
  intro n hn
  simp [phaseSequence, hn]

lemma phaseSequence_nat (N : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    phaseSequence N f (n : ℤ) = if n < N then KusminLandau151.e (f n) else 0 := by
  simp [phaseSequence]

lemma sum_phaseSequence (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), phaseSequence N f n) =
      ∑ n ∈ Finset.range N, KusminLandau151.e (f n) := by
  rw [sum_Ico_int_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseSequence_nat, ite_eq_left (Finset.mem_range.mp hn)]

lemma norm_correlation_swap (T : Finset ℤ) (f : ℤ → ℂ) (h k : ℤ) :
    ‖correlation T f h k‖ = ‖correlation T f k h‖ := by
  have he : correlation T f h k = conj (correlation T f k h) := by
    simp only [correlation, map_sum, map_mul, Complex.conj_conj]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he, Complex.norm_conj]

lemma correlation_translate (s T : Finset ℤ) (f : ℤ → ℂ) (h k : ℤ)
    (hz : ∀ n ∉ s, f n = 0) (hT : ∀ n ∈ s, n - k ∈ T) :
    correlation T f h k = ∑ n ∈ s, f (n + (h - k)) * conj (f n) := by
  have hs : ∀ n ∉ s, f (n + (h - k)) * conj (f n) = 0 := by
    intro n hn
    simp [hz n hn]
  have ht := shift_sum_of_support s T
    (fun n => f (n + (h - k)) * conj (f n)) k hs hT
  convert ht using 1
  unfold correlation
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  omega

lemma phase_correlation_forward (N H : ℕ) (f : ℕ → ℝ) (h k : ℤ)
    (hk0 : 0 ≤ k) (hkH : k < (H : ℤ)) (hkh : k ≤ h) :
    correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k =
      ∑ n ∈ Finset.range (N - (h - k).toNat),
        KusminLandau151.e (shiftedPhase f (h - k).toNat n) := by
  have hT : ∀ n ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      n - k ∈ Finset.Ico (-(H : ℤ)) (N : ℤ) := by
    intro n hn
    simp only [Finset.mem_Ico] at *
    omega
  rw [correlation_translate _ _ _ h k (phaseSequence_support N f) hT,
    sum_Ico_int_eq_sum_range]
  let d := (h - k).toNat
  have hdeq : (d : ℤ) = h - k := by dsimp [d]; omega
  have hs : Finset.range (N - d) ⊆ Finset.range N := Finset.range_mono (Nat.sub_le _ _)
  calc
    _ = ∑ n ∈ Finset.range (N - d),
        phaseSequence N f ((n : ℤ) + (h - k)) * conj (phaseSequence N f (n : ℤ)) := by
      apply (Finset.sum_subset hs ?_).symm
      intro n hn hnnot
      have hnN := Finset.mem_range.mp hn
      have hnNd : ¬n < N - d := by simpa only [Finset.mem_range] using hnnot
      rw [← hdeq, ← Nat.cast_add, phaseSequence_nat,
        ite_eq_right (show ¬n + d < N by omega), zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnNd := Finset.mem_range.mp hn
      rw [← hdeq, ← Nat.cast_add, phaseSequence_nat, phaseSequence_nat,
        ite_eq_left (show n + d < N by omega), ite_eq_left (show n < N by omega), e_mul_conj]
      rfl

lemma phase_correlation_le_forward (N H : ℕ) (f : ℕ → ℝ) (h k : ℤ) (L U : ℝ)
    (hk0 : 0 ≤ k) (hkH : k < (H : ℤ)) (hhH : h < (H : ℤ)) (hkh : k < h)
    (hL : 0 < L) (hU0 : 0 ≤ U) (hU : (H : ℝ) * U ≤ 1 / 2)
    (hd : ∀ m < N, L ≤ secondDifference f m ∧ secondDifference f m ≤ U)
    (hm : MonotoneOn (secondDifference f) (Set.Iio N) ∨
      AntitoneOn (secondDifference f) (Set.Iio N)) :
    ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖ ≤
      2 / (|((h - k : ℤ) : ℝ)| * L) := by
  rw [phase_correlation_forward N H f h k hk0 hkH hkh.le]
  have hdpos : 0 < (h - k).toNat := by omega
  have hdH : (h - k).toNat ≤ H := by omega
  have hsmall : ((h - k).toNat : ℝ) * U ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hdH) hU0).trans hU
  have hdreal : ((h - k).toNat : ℝ) = |((h - k : ℤ) : ℝ)| := by
    rw [abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ h - k by omega))]
    exact_mod_cast (show (((h - k).toNat : ℕ) : ℤ) = h - k by omega)
  simpa only [hdreal] using shifted_phase_cancellation f N (h - k).toNat L U hdpos hL hsmall hd hm

lemma phase_correlation_le (N H : ℕ) (f : ℕ → ℝ) (h k : ℤ) (L U : ℝ)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ)) (hk : k ∈ Finset.Ico (0 : ℤ) (H : ℤ))
    (hne : h ≠ k) (hL : 0 < L) (hU0 : 0 ≤ U) (hU : (H : ℝ) * U ≤ 1 / 2)
    (hd : ∀ m < N, L ≤ secondDifference f m ∧ secondDifference f m ≤ U)
    (hm : MonotoneOn (secondDifference f) (Set.Iio N) ∨
      AntitoneOn (secondDifference f) (Set.Iio N)) :
    ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖ ≤
      2 / (|((h - k : ℤ) : ℝ)| * L) := by
  have hh' := Finset.mem_Ico.mp hh
  have hk' := Finset.mem_Ico.mp hk
  rcases lt_or_gt_of_ne hne with hhk | hkh
  · rw [norm_correlation_swap]
    have he : |((k - h : ℤ) : ℝ)| = |((h - k : ℤ) : ℝ)| := by
      push_cast
      exact abs_sub_comm _ _
    simpa only [he] using phase_correlation_le_forward N H f k h L U
      hh'.1 hh'.2 hk'.2 hhk hL hU0 hU hd hm
  · exact phase_correlation_le_forward N H f h k L U
      hk'.1 hk'.2 hh'.2 hkh hL hU0 hU hd hm

/-- A quantitative second-difference estimate, retaining exact distances in
the off-diagonal sum. Every correlation bound is derived by Kusmin–Landau. -/
theorem second_difference_vdc (N H : ℕ) (f : ℕ → ℝ) (L U : ℝ)
    (hL : 0 < L) (hU0 : 0 ≤ U) (hU : (H : ℝ) * U ≤ 1 / 2)
    (hd : ∀ m < N, L ≤ secondDifference f m ∧ secondDifference f m ≤ U)
    (hm : MonotoneOn (secondDifference f) (Set.Iio N) ∨
      AntitoneOn (secondDifference f) (Set.Iio N)) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      ((N : ℝ) + H) * ((H : ℝ) * N +
        ∑ h ∈ Finset.Ico (0 : ℤ) (H : ℤ),
          ∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
            2 / (|((h - k : ℤ) : ℝ)| * L)) := by
  have hv := van_der_corput_interval_supported N H (phaseSequence N f)
    (phaseSequence_support N f) (fun n hn => by simp [phaseSequence, hn, norm_e])
  rw [sum_phaseSequence] at hv
  apply hv.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro h hh
  apply Finset.sum_le_sum
  intro k hk
  exact phase_correlation_le N H f h k L U hh (Finset.mem_erase.mp hk).2
    (Ne.symm (Finset.mem_erase.mp hk).1) hL hU0 hU hd hm

def distanceCost (L : ℝ) (d : ℤ) : ℝ := 2 / (|(d : ℝ)| * L)

lemma sum_injective_le (s S : Finset ℤ) (i : ℤ → ℤ) (g : ℤ → ℝ)
    (hi : Set.InjOn i (s : Set ℤ)) (hmem : ∀ n ∈ s, i n ∈ S)
    (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ s, g (i n)) ≤ ∑ n ∈ S, g n := by
  have hs : s.image i ⊆ S := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    exact hmem m hm
  calc
    _ = ∑ n ∈ s.image i, g n := by rw [Finset.sum_image]; exact hi
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => hg n)

lemma distance_row_le (H : ℕ) (h : ℤ) (L : ℝ) (hL : 0 < L)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ)) :
    (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h, distanceCost L (h - k)) ≤
      2 * ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), distanceCost L d := by
  let S := (Finset.Ico (0 : ℤ) (H : ℤ)).erase h
  have hh' := Finset.mem_Ico.mp hh
  have hn : ∀ d : ℤ, 0 ≤ distanceCost L d := by intro d; unfold distanceCost; positivity
  have hlow : (∑ k ∈ S.filter (fun k => k < h), distanceCost L (h - k)) ≤
      ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), distanceCost L d := by
    apply sum_injective_le _ _ (fun k => h - k) (distanceCost L) _ _ hn
    · intro a ha b hb he
      dsimp only at he
      omega
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkS := Finset.mem_erase.mp hk'.1
      have hkI := Finset.mem_Ico.mp hkS.2
      simp only [Finset.mem_Icc]
      omega
  have hupp : (∑ k ∈ S.filter (fun k => ¬ k < h), distanceCost L (h - k)) ≤
      ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), distanceCost L d := by
    calc
      _ = ∑ k ∈ S.filter (fun k => ¬ k < h), distanceCost L (k - h) := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold distanceCost
        push_cast
        rw [abs_sub_comm]
      _ ≤ _ := by
        apply sum_injective_le _ _ (fun k => k - h) (distanceCost L) _ _ hn
        · intro a ha b hb he
          dsimp only at he
          omega
        · intro k hk
          have hk' := Finset.mem_filter.mp hk
          have hkS := Finset.mem_erase.mp hk'.1
          have hkI := Finset.mem_Ico.mp hkS.2
          simp only [Finset.mem_Icc]
          omega
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun k => k < h)
    (fun k => distanceCost L (h - k))
  change (∑ k ∈ S, distanceCost L (h - k)) ≤ _
  rw [← hsplit]
  linarith

lemma distanceCost_sum_eq_harmonic (H : ℕ) (L : ℝ) :
    (∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), distanceCost L d) =
      (2 / L) * (harmonic H : ℝ) := by
  have he : Finset.Icc (1 : ℤ) (H : ℤ) =
      (Finset.Icc (1 : ℕ) H).image (fun n : ℕ => (n : ℤ)) := by
    ext n
    constructor
    · intro hn
      have hn' := Finset.mem_Icc.mp hn
      exact Finset.mem_image.mpr ⟨n.toNat, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
      have hm' := Finset.mem_Icc.mp hm
      simp only [Finset.mem_Icc]
      omega
  rw [he, Finset.sum_image]
  · simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [distanceCost, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      div_eq_mul_inv, mul_inv_rev]
    ring
  · intro a ha b hb hab
    dsimp only at hab
    exact_mod_cast hab

lemma distance_sum_le_harmonic (H : ℕ) (L : ℝ) (hL : 0 < L) :
    (∑ h ∈ Finset.Ico (0 : ℤ) (H : ℤ),
      ∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
        2 / (|((h - k : ℤ) : ℝ)| * L)) ≤
      (4 * (H : ℝ) / L) * (harmonic H : ℝ) := by
  calc
    _ ≤ ∑ _h ∈ Finset.Ico (0 : ℤ) (H : ℤ),
        2 * ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), distanceCost L d := by
      exact Finset.sum_le_sum (fun h hh => distance_row_le H h L hL hh)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, card_integer_interval, distanceCost_sum_eq_harmonic]
      ring

/-- Finite second-derivative bound with an explicit logarithmic factor.
The diagonal term is `H N`; the factor `1+log H` comes only from summing the
proved inverse-distance correlation bounds. -/
theorem second_difference_vdc_log (N H : ℕ) (f : ℕ → ℝ) (L U : ℝ)
    (hL : 0 < L) (hU0 : 0 ≤ U) (hU : (H : ℝ) * U ≤ 1 / 2)
    (hd : ∀ m < N, L ≤ secondDifference f m ∧ secondDifference f m ≤ U)
    (hm : MonotoneOn (secondDifference f) (Set.Iio N) ∨
      AntitoneOn (secondDifference f) (Set.Iio N)) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      ((N : ℝ) + H) * ((H : ℝ) * N +
        (4 * (H : ℝ) / L) * (1 + Real.log (H : ℝ))) := by
  apply (second_difference_vdc N H f L U hL hU0 hU hd hm).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  exact (distance_sum_le_harmonic H L hL).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log H) (by positivity))

/-- The same estimate divided by the positive shift parameter. -/
theorem second_difference_norm_sq_le (N H : ℕ) (f : ℕ → ℝ) (L U : ℝ)
    (hH : 0 < H) (hL : 0 < L) (hU0 : 0 ≤ U) (hU : (H : ℝ) * U ≤ 1 / 2)
    (hd : ∀ m < N, L ≤ secondDifference f m ∧ secondDifference f m ≤ U)
    (hm : MonotoneOn (secondDifference f) (Set.Iio N) ∨
      AntitoneOn (secondDifference f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      (((N : ℝ) + H) / H) * ((N : ℝ) + (4 / L) * (1 + Real.log (H : ℝ))) := by
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hv := second_difference_vdc_log N H f L U hL hU0 hU hd hm
  have he : ((N : ℝ) + H) * ((H : ℝ) * N +
      (4 * (H : ℝ) / L) * (1 + Real.log (H : ℝ))) =
      (H : ℝ) ^ 2 * ((((N : ℝ) + H) / H) *
        ((N : ℝ) + (4 / L) * (1 + Real.log (H : ℝ)))) := by
    field_simp
  rw [he] at hv
  exact le_of_mul_le_mul_left hv (pow_pos hHr 2)

/-- A full finite reciprocal exponential-sum estimate. Its hypotheses are
only positivity and the explicit shift restriction; all phase-shape facts
and all correlation cancellation have been proved in the preceding modules. -/
theorem reciprocal_norm_sq_le (a u : ℝ) (N H : ℕ)
    (ha : 0 < a) (hu : 0 < u) (hH : 0 < H)
    (hsmall : (H : ℝ) * (2 * u / a ^ 3) ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (u / (a + (n : ℝ)))‖ ^ 2 ≤
      (((N : ℝ) + H) / H) *
        ((N : ℝ) + (2 * (a + (N : ℝ) + 2) ^ 3 / u) * (1 + Real.log (H : ℝ))) := by
  have hv := second_difference_norm_sq_le N H (reciprocalPhase a u)
    (2 * u / (a + (N : ℝ) + 2) ^ 3) (2 * u / a ^ 3) hH (by positivity)
    (by positivity) hsmall
    (fun n hn => reciprocal_secondDifference_bounds a u ha hu.le N n hn)
    (Or.inr (fun _ _ _ _ hmn => reciprocal_secondDifference_antitone a u ha hu.le hmn))
  have he : 4 / (2 * u / (a + (N : ℝ) + 2) ^ 3) =
      2 * (a + (N : ℝ) + 2) ^ 3 / u := by field_simp; ring
  simpa only [reciprocalPhase, he] using hv

#print axioms second_difference_vdc
#print axioms second_difference_vdc_log
#print axioms reciprocal_norm_sq_le
run_cmd do
  let targets : List Lean.Name := [``phase_correlation_forward,
    ``phase_correlation_le_forward, ``phase_correlation_le, ``second_difference_vdc,
    ``distance_row_le, ``distanceCost_sum_eq_harmonic,
    ``distance_sum_le_harmonic, ``second_difference_vdc_log,
    ``second_difference_norm_sq_le, ``reciprocal_norm_sq_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.SecondDerivativeVdC151
end



end Update151_Component_18
/- END COMPONENT: SecondDerivativeVdC151.lean -/

/- BEGIN COMPONENT: SecondDerivativeOptimized151.lean -/
section Update151_Component_19


/-! Choosing the differencing parameter in the checked second-difference test. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Erdos374.SecondDerivativeOptimized151
open Erdos374.KusminLandau151 Erdos374.SecondDerivative151 Erdos374.SecondDerivativeVdC151

lemma optimize_shift_bound (n h L C G : ℝ) (hh : 0 < h) (hhn : h ≤ n)
    (hL : 0 < L) (hC : 1 ≤ C) (hG : 1 ≤ G)
    (hchoice : h = n ∨ 1 ≤ 4 * h * C * L) :
    ((n + h) / h) * (n + (4 / L) * G) ≤ 32 * C * G * (n ^ 2 * L + 1 / L) := by
  let Q := n ^ 2 * L + 1 / L
  have hn : 0 ≤ n := hh.le.trans hhn
  have hC0 : 0 ≤ C := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQN : n ^ 2 * L ≤ Q := by
    exact le_add_of_nonneg_right (by positivity)
  have hQI : 1 / L ≤ Q := by
    exact le_add_of_nonneg_left (by positivity)
  have hNQ : 2 * n ≤ Q := by
    have hs : 0 ≤ (n * L - 1) ^ 2 / L := by positivity
    have he : (n * L - 1) ^ 2 / L = Q - 2 * n := by dsimp [Q]; field_simp; ring
    rw [he] at hs
    linarith
  have hGQ : Q ≤ G * Q := by nlinarith
  have hCGQ : G * Q ≤ C * G * Q := by nlinarith [mul_nonneg hG0 hQ0]
  have hCGQ0 : 0 ≤ C * G * Q := by positivity
  change _ ≤ 32 * C * G * Q
  rcases hchoice with he | he
  · subst h
    have hratio : (n + n) / n = 2 := by field_simp; norm_num
    rw [hratio]
    have hterm1 : 2 * n ≤ C * G * Q := hNQ.trans (hGQ.trans hCGQ)
    have hterm2 : G / L ≤ C * G * Q := by
      calc
        _ = G * (1 / L) := by ring
        _ ≤ G * Q := mul_le_mul_of_nonneg_left hQI hG0
        _ ≤ _ := hCGQ
    calc
      _ = 2 * n + 8 * (G / L) := by ring
      _ ≤ C * G * Q + 8 * (C * G * Q) :=
        add_le_add hterm1 (mul_le_mul_of_nonneg_left hterm2 (by norm_num))
      _ ≤ _ := by nlinarith
  · have hratio : (n + h) / h ≤ 8 * n * C * L := by
      apply (div_le_iff₀ hh).mpr
      have hp := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * n by positivity)
      nlinarith
    have hmain : n ^ 2 * L ≤ G * Q := hQN.trans hGQ
    calc
      _ ≤ (8 * n * C * L) * (n + (4 / L) * G) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = (8 * C) * (n ^ 2 * L) + (16 * C * G) * (2 * n) := by field_simp; ring
      _ ≤ (8 * C) * (G * Q) + (16 * C * G) * Q :=
        add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity))
          (mul_le_mul_of_nonneg_left hNQ (by positivity))
      _ ≤ _ := by nlinarith

lemma norm_phase_sum_le (N : ℕ) (f : ℕ → ℝ) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖KusminLandau151.e (f n)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_e, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- A second-difference estimate at the usual square-root scale, with a
logarithmic loss. Monotonicity of the finite second differences is explicit. -/
theorem second_difference_optimized (N : ℕ) (f : ℕ → ℝ) (L C : ℝ)
    (hL : 0 < L) (hC : 1 ≤ C)
    (hd : ∀ m < N, L ≤ secondDifference f m ∧ secondDifference f m ≤ C * L)
    (hm : MonotoneOn (secondDifference f) (Set.Iio N) ∨
      AntitoneOn (secondDifference f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      32 * C * (1 + Real.log ((N : ℝ) + 1)) * ((N : ℝ) ^ 2 * L + 1 / L) := by
  have hC0 : 0 < C := by linarith
  have hG : 1 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, zero_pow (by omega : 2 ≠ 0),
      Nat.cast_zero, zero_add, Real.log_one, add_zero, zero_mul]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  by_cases hlarge : 1 / 4 ≤ C * L
  · have hs := norm_phase_sum_le N f
    have hs2 : ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤ (N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hs 2
    apply hs2.trans
    have hprod := mul_le_mul_of_nonneg_left hlarge (sq_nonneg (N : ℝ))
    have hQ : (N : ℝ) ^ 2 * L ≤ (N : ℝ) ^ 2 * L + 1 / L :=
      le_add_of_nonneg_right (by positivity)
    have hQ0 : 0 ≤ (N : ℝ) ^ 2 * L + 1 / L := by positivity
    have hCGQ : C * ((N : ℝ) ^ 2 * L + 1 / L) ≤
        C * (1 + Real.log ((N : ℝ) + 1)) * ((N : ℝ) ^ 2 * L + 1 / L) := by
      nlinarith [mul_nonneg hC0.le hQ0]
    nlinarith [mul_le_mul_of_nonneg_left hQ hC0.le]
  · let X : ℝ := 1 / (2 * C * L)
    let K : ℕ := ⌊X⌋₊
    let H : ℕ := min N K
    have hX0 : 0 ≤ X := by dsimp [X]; positivity
    have hX2 : 2 ≤ X := by
      dsimp [X]
      apply (le_div_iff₀ (by positivity : 0 < 2 * C * L)).mpr
      linarith
    have hK1 : 1 ≤ K := by
      apply (Nat.le_floor_iff hX0).mpr
      simpa only [Nat.cast_one] using (show (1 : ℝ) ≤ X by linarith)
    have hKX : (K : ℝ) ≤ X := Nat.floor_le hX0
    have hXK : X < (K : ℝ) + 1 := Nat.lt_floor_add_one X
    have hH : 0 < H := by dsimp [H]; omega
    have hHN : H ≤ N := Nat.min_le_left _ _
    have hHK : H ≤ K := Nat.min_le_right _ _
    have hHU : (H : ℝ) * (C * L) ≤ 1 / 2 := by
      have hHX : (H : ℝ) ≤ X := (Nat.cast_le.mpr hHK).trans hKX
      have hp := mul_le_mul_of_nonneg_right hHX (show 0 ≤ C * L by positivity)
      have he : X * (C * L) = 1 / 2 := by dsimp [X]; field_simp
      rwa [he] at hp
    have hchoice : (H : ℝ) = (N : ℝ) ∨ 1 ≤ 4 * (H : ℝ) * C * L := by
      by_cases he : H = N
      · exact Or.inl (congrArg (fun n : ℕ => (n : ℝ)) he)
      · right
        have hHK' : H = K := by dsimp [H] at *; omega
        have hhalf : X / 2 ≤ (K : ℝ) := by linarith
        have hp := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ 4 * C * L by positivity)
        have heq : X / 2 * (4 * C * L) = 1 := by dsimp [X]; field_simp; norm_num
        rw [heq, ← hHK'] at hp
        nlinarith
    have hv := second_difference_norm_sq_le N H f L (C * L) hH hL (by positivity) hHU hd hm
    have hlog : Real.log (H : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (Nat.cast_pos.mpr hH) (by exact_mod_cast (show H ≤ N + 1 by omega))
    have hv' : ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
        (((N : ℝ) + H) / H) * ((N : ℝ) + (4 / L) * (1 + Real.log ((N : ℝ) + 1))) := by
      apply hv.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact hv'.trans (optimize_shift_bound (N : ℝ) (H : ℝ) L C
      (1 + Real.log ((N : ℝ) + 1)) (Nat.cast_pos.mpr hH) (Nat.cast_le.mpr hHN)
      hL hC hG hchoice)

#print axioms second_difference_optimized
run_cmd do
  for target in [``optimize_shift_bound, ``second_difference_optimized] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.SecondDerivativeOptimized151
end


end Update151_Component_19
/- END COMPONENT: SecondDerivativeOptimized151.lean -/

/- BEGIN COMPONENT: OscillatoryIntegral151.lean -/
section Update151_Component_20



/-! A proved continuous cancellation estimate, by integration by parts. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory

namespace Erdos374.OscillatoryIntegral151

def wave (f : ℝ → ℝ) (t : ℝ) : ℂ := Complex.exp ((f t : ℂ) * Complex.I)
def waveD (f g : ℝ → ℝ) (t : ℝ) : ℂ := wave f t * ((g t : ℂ) * Complex.I)
def invSlope (g : ℝ → ℝ) (t : ℝ) : ℂ := ((g t)⁻¹ : ℝ) * (-Complex.I)
def invSlopeD (g h : ℝ → ℝ) (t : ℝ) : ℂ :=
  (-h t / (g t) ^ 2 : ℝ) * (-Complex.I)

theorem wave_hasDerivAt {f g : ℝ → ℝ} {t : ℝ} (hf : HasDerivAt f (g t) t) :
    HasDerivAt (wave f) (waveD f g t) t := (hf.ofReal_comp.mul_const Complex.I).cexp

theorem invSlope_hasDerivAt {g h : ℝ → ℝ} {t : ℝ}
    (hg : HasDerivAt g (h t) t) (hg0 : g t ≠ 0) :
    HasDerivAt (invSlope g) (invSlopeD g h t) t := by
  exact ((hg.inv hg0).ofReal_comp.mul_const (-Complex.I))

@[simp] theorem norm_wave (f : ℝ → ℝ) (t : ℝ) : ‖wave f t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem norm_invSlope (g : ℝ → ℝ) (t : ℝ) : ‖invSlope g t‖ = 1 / |g t| := by
  simp only [invSlope, norm_inv, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    Complex.norm_I, mul_one, one_div]

theorem norm_invSlopeD (g h : ℝ → ℝ) (t : ℝ) :
    ‖invSlopeD g h t‖ = |h t| / |g t| ^ 2 := by
  simp only [invSlopeD, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one, abs_div, abs_neg, abs_pow]

/-- This bound supplies cancellation when a phase derivative stays away from zero.
It is uniform in the phase's absolute value and the position of the interval. -/
theorem norm_integral_wave_le {f g h : ℝ → ℝ} {a b η M : ℝ}
    (hab : a ≤ b) (hη : 0 < η)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (h t) t)
    (hh : ContinuousOn h (Icc a b))
    (haway : ∀ t ∈ Icc a b, η ≤ |g t|)
    (hM : ∀ t ∈ Icc a b, |h t| ≤ M) :
    ‖∫ t in a..b, wave f t‖ ≤ 2 / η + (b - a) * M / η ^ 2 := by
  have hn (t : ℝ) (ht : t ∈ Icc a b) : g t ≠ 0 :=
    abs_pos.mp (hη.trans_le (haway t ht))
  have hfc : ContinuousOn (wave f) (Icc a b) :=
    fun t ht => (wave_hasDerivAt (hf t ht)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hqc : ContinuousOn (invSlope g) (Icc a b) :=
    fun t ht => (invSlope_hasDerivAt (hg t ht) (hn t ht)).continuousAt.continuousWithinAt
  have hwdc : ContinuousOn (waveD f g) (Icc a b) :=
    hfc.mul ((Complex.continuous_ofReal.comp_continuousOn hgc).mul_const _)
  have hqdc : ContinuousOn (invSlopeD g h) (Icc a b) := by
    unfold invSlopeD
    exact (Complex.continuous_ofReal.comp_continuousOn
      (hh.neg.div (hgc.pow 2) (by intro t ht; exact pow_ne_zero _ (hn t ht)))).mul_const _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := invSlope g) (v := wave f) (u' := invSlopeD g h) (v' := waveD f g)
    (by intro t ht; rw [uIcc_of_le hab] at ht; exact invSlope_hasDerivAt (hg t ht) (hn t ht))
    (by intro t ht; rw [uIcc_of_le hab] at ht; exact wave_hasDerivAt (hf t ht))
    (hqdc.intervalIntegrable_of_Icc hab) (hwdc.intervalIntegrable_of_Icc hab)
  have hprod : (∫ t in a..b, invSlope g t * waveD f g t) = ∫ t in a..b, wave f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hgt : (g t : ℂ) ≠ 0 := by exact_mod_cast hn t ht
    unfold invSlope waveD
    push_cast
    field_simp
    simp [Complex.I_sq]
  rw [hprod] at hparts
  have hbnd (t : ℝ) (ht : t ∈ Icc a b) : ‖invSlope g t * wave f t‖ ≤ 1 / η := by
    rw [norm_mul, norm_wave, mul_one, norm_invSlope]
    exact one_div_le_one_div_of_le hη (haway t ht)
  have hMint : ‖∫ t in a..b, invSlopeD g h t * wave f t‖ ≤ (b - a) * (M / η ^ 2) := by
    calc
      _ ≤ ∫ t in a..b, ‖invSlopeD g h t * wave f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, M / η ^ 2 :=
        intervalIntegral.integral_mono_on hab
          ((hqdc.mul hfc).norm.intervalIntegrable_of_Icc hab) intervalIntegrable_const (by
            intro t ht
            rw [norm_mul, norm_wave, mul_one, norm_invSlopeD]
            exact div_le_div₀ ((abs_nonneg _).trans (hM t ht)) (hM t ht) (sq_pos_of_pos hη)
              (pow_le_pow_left₀ hη.le (haway t ht) 2))
      _ = _ := by rw [intervalIntegral.integral_const]; rfl
  rw [hparts]
  calc
    _ ≤ ‖invSlope g b * wave f b - invSlope g a * wave f a‖ +
        ‖∫ t in a..b, invSlopeD g h t * wave f t‖ := norm_sub_le _ _
    _ ≤ (1 / η + 1 / η) + (b - a) * (M / η ^ 2) :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add (hbnd b ⟨hab, le_rfl⟩)
        (hbnd a ⟨le_rfl, hab⟩))) hMint
    _ = _ := by ring

#print axioms norm_integral_wave_le
run_cmd do
  for target in [``wave_hasDerivAt, ``invSlope_hasDerivAt, ``norm_integral_wave_le] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.OscillatoryIntegral151
end

end Update151_Component_20
/- END COMPONENT: OscillatoryIntegral151.lean -/

/- BEGIN COMPONENT: ReciprocalIntegral151.lean -/
section Update151_Component_21


/-! Continuous cancellation for reciprocal phases away from a stationary point. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory

namespace Erdos374.ReciprocalIntegral151
open ReciprocalCharacter151 OscillatoryIntegral151

def phaseDD (u v t : ℝ) : ℝ := 2 * u / t ^ 3 + 6 * v / t ^ 4
def secondMajorant (u v t : ℝ) : ℝ := 2 * |u| / t ^ 3 + 6 * |v| / t ^ 4

theorem phaseD_hasDerivAt (u v t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (phaseD u v) (phaseDD u v t) t := by
  have h1 := ((hasDerivAt_const t u).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht)).neg
  have h2 := (hasDerivAt_const t (2 * v)).div ((hasDerivAt_id t).pow 3) (pow_ne_zero 3 ht)
  convert h1.sub h2 using 1
  · rfl
  · dsimp [phaseDD]
    field_simp
    <;> ring

theorem phaseDD_continuousOn (u v a b : ℝ) (ha : 0 < a) :
    ContinuousOn (phaseDD u v) (Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
  have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht0
  have ht4 : t ^ 4 ≠ 0 := pow_ne_zero 4 ht0
  apply ContinuousAt.continuousWithinAt
  unfold phaseDD
  fun_prop

theorem phaseDD_abs_le (u v a t : ℝ) (ha : 0 < a) (hat : a ≤ t) :
    |phaseDD u v t| ≤ secondMajorant u v a := by
  have ht : 0 < t := ha.trans_le hat
  calc
    _ ≤ |2 * u / t ^ 3| + |6 * v / t ^ 4| := abs_add_le _ _
    _ = 2 * |u| / t ^ 3 + 6 * |v| / t ^ 4 := by
      simp only [abs_div, abs_mul, abs_of_pos (pow_pos ht 3), abs_of_pos (pow_pos ht 4)]
      norm_num
    _ ≤ secondMajorant u v a := add_le_add
      (div_le_div_of_nonneg_left (by positivity) (pow_pos ha 3)
        (pow_le_pow_left₀ ha.le hat 3))
      (div_le_div_of_nonneg_left (by positivity) (pow_pos ha 4)
        (pow_le_pow_left₀ ha.le hat 4))

theorem norm_integral_character_le (u v a b η : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η)
    (haway : ∀ t ∈ Icc a b, η ≤ |phaseD u v t|) :
    ‖∫ t in a..b, character u v t‖ ≤
      1 / (Real.pi * η) + (b - a) * secondMajorant u v a / (2 * Real.pi * η ^ 2) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hbound := norm_integral_wave_le
    (f := fun t => 2 * Real.pi * phase u v t)
    (g := fun t => 2 * Real.pi * phaseD u v t)
    (h := fun t => 2 * Real.pi * phaseDD u v t)
    (η := 2 * Real.pi * η) (M := 2 * Real.pi * secondMajorant u v a)
    hab (mul_pos hπ hη)
    (by intro t ht; exact (phase_hasDerivAt u v t (ne_of_gt (ha.trans_le ht.1))).const_mul _)
    (by intro t ht; exact (phaseD_hasDerivAt u v t (ne_of_gt (ha.trans_le ht.1))).const_mul _)
    ((phaseDD_continuousOn u v a b ha).const_mul _)
    (by intro t ht; rw [abs_mul, abs_of_pos hπ]; exact mul_le_mul_of_nonneg_left (haway t ht) hπ.le)
    (by
      intro t ht
      rw [abs_mul, abs_of_pos hπ]
      exact mul_le_mul_of_nonneg_left (phaseDD_abs_le u v a t ha ht.1) hπ.le)
  convert hbound using 1
  · rfl
  · field_simp [ne_of_gt Real.pi_pos, ne_of_gt hη]
    <;> ring

theorem positive_phaseD_lower (u v P t : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hP : 0 < P) (ht : t ∈ Icc P (2 * P)) :
    amplitude u v P / (4 * P) ≤ |phaseD u v t| := by
  have ht0 : 0 < t := hP.trans_le ht.1
  have ht2 : t ^ 2 ≤ 4 * P ^ 2 := by
    nlinarith [pow_le_pow_left₀ ht0.le ht.2 2]
  have ht3 : t ^ 3 ≤ 8 * P ^ 3 := by
    nlinarith [pow_le_pow_left₀ ht0.le ht.2 3]
  have h1 : u / (4 * P ^ 2) ≤ u / t ^ 2 :=
    div_le_div_of_nonneg_left hu (pow_pos ht0 2) ht2
  have h2 : 2 * v / (8 * P ^ 3) ≤ 2 * v / t ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos ht0 3) ht3
  have hn : phaseD u v t ≤ 0 := by
    unfold phaseD
    have hpos1 : 0 ≤ u / t ^ 2 := by positivity
    have hpos2 : 0 ≤ 2 * v / t ^ 3 := by positivity
    linarith
  rw [abs_of_nonpos hn]
  calc
    _ = u / (4 * P ^ 2) + 2 * v / (8 * P ^ 3) := by
      simp only [amplitude, abs_of_nonneg hu, abs_of_nonneg hv]
      field_simp
      <;> ring
    _ ≤ u / t ^ 2 + 2 * v / t ^ 3 := add_le_add h1 h2
    _ = -phaseD u v t := by unfold phaseD; ring

/-- Genuine decay for the nonstationary same-sign quadrant, uniform in u,v. -/
theorem positive_character_integral (u v P : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hP : 0 < P) (hF : 0 < amplitude u v P) :
    ‖∫ t in P..(2 * P), character u v t‖ ≤
      52 * P / (Real.pi * amplitude u v P) := by
  have hη : 0 < amplitude u v P / (4 * P) := by positivity
  have hbound := norm_integral_character_le u v P (2 * P) _ hP (by linarith) hη
    (by intro t ht; exact positive_phaseD_lower u v P t hu hv hP ht)
  have hM : secondMajorant u v P ≤ 6 * amplitude u v P / P ^ 2 := by
    simp only [secondMajorant, amplitude, abs_of_nonneg hu, abs_of_nonneg hv]
    apply (le_div_iff₀ (pow_pos hP 2)).mpr
    field_simp
    nlinarith
  calc
    _ ≤ 1 / (Real.pi * (amplitude u v P / (4 * P))) +
        (2 * P - P) * secondMajorant u v P /
          (2 * Real.pi * (amplitude u v P / (4 * P)) ^ 2) := hbound
    _ ≤ 1 / (Real.pi * (amplitude u v P / (4 * P))) +
        (2 * P - P) * (6 * amplitude u v P / P ^ 2) /
          (2 * Real.pi * (amplitude u v P / (4 * P)) ^ 2) := by
      gcongr
      linarith
    _ = _ := by
      field_simp [ne_of_gt hP, ne_of_gt hF, ne_of_gt Real.pi_pos]
      <;> ring

#print axioms positive_character_integral
run_cmd do
  for target in [``phaseD_hasDerivAt, ``norm_integral_character_le,
      ``positive_phaseD_lower, ``positive_character_integral] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalIntegral151
end

end Update151_Component_21
/- END COMPONENT: ReciprocalIntegral151.lean -/

/- BEGIN COMPONENT: HarmanAnalytic151.lean -/
section Update151_Component_22




/-!
Unconditional finite sieve identities for Harman's section 2.
No prime-distribution, mean-value, or exceptional-set assumption is used.
-/

noncomputable section
open scoped BigOperators

namespace Erdos374.HarmanAnalytic151

/-- No prime strictly smaller than the cutoff divides the integer. -/
def Rough (z n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n

def sifted (A : Finset ℕ) (z : ℕ) : Finset ℕ := by
  classical
  exact A.filter (Rough z)

def divisorSlice (A : Finset ℕ) (d : ℕ) : Finset ℕ := A.filter (d ∣ ·)

def primeBand (a b : ℕ) : Finset ℕ := (Finset.Ico a b).filter Nat.Prime

def siftedSum {α : Type*} [AddCommMonoid α]
    (A : Finset ℕ) (z : ℕ) (w : ℕ → α) : α := ∑ n ∈ sifted A z, w n

theorem rough_succ (z n : ℕ) :
    Rough (z + 1) n ↔ Rough z n ∧ ¬ (z.Prime ∧ z ∣ n) := by
  constructor
  · intro h
    constructor
    · intro p hp hpz
      exact h p hp (Nat.lt_succ_of_lt hpz)
    · rintro ⟨hz, hzn⟩
      exact h z hz (Nat.lt_succ_self z) hzn
  · rintro ⟨h, hz⟩ p hp hpz hpn
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hpz) with hlt | rfl
    · exact h p hp hlt hpn
    · exact hz ⟨hp, hpn⟩

theorem sifted_succ (A : Finset ℕ) (z : ℕ) :
    sifted A (z + 1) =
      (sifted A z).filter (fun n => ¬ (z.Prime ∧ z ∣ n)) := by
  classical
  ext n
  simp [sifted, rough_succ, and_assoc]

/-- Remove the integers whose smallest prime divisor is the new sieve prime. -/
theorem weighted_buchstab_step {α : Type*} [AddCommMonoid α]
    (A : Finset ℕ) (z : ℕ) (w : ℕ → α) :
    siftedSum A z w = siftedSum A (z + 1) w +
      if z.Prime then siftedSum (divisorSlice A z) z w else 0 := by
  classical
  have hbad : (sifted A z).filter (fun n => z.Prime ∧ z ∣ n) =
      if z.Prime then sifted (divisorSlice A z) z else ∅ := by
    by_cases hz : z.Prime
    · ext n
      simp [hz, sifted, divisorSlice, and_assoc, and_left_comm, and_comm]
    · simp [hz]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (sifted A z) (fun n => z.Prime ∧ z ∣ n) w
  rw [← sifted_succ, hbad] at hsplit
  by_cases hz : z.Prime
  · simpa [hz, siftedSum, add_comm] using hsplit.symm
  · simpa [hz, siftedSum] using hsplit.symm

/-- Weighted finite Buchstab identity, valid even when the support contains 0 or 1. -/
theorem weighted_buchstab {α : Type*} [AddCommMonoid α]
    (A : Finset ℕ) (a b : ℕ) (w : ℕ → α) (hab : a ≤ b) :
    siftedSum A a w = siftedSum A b w +
      ∑ p ∈ primeBand a b, siftedSum (divisorSlice A p) p w := by
  classical
  have hraw : ∀ b : ℕ, a ≤ b →
      siftedSum A a w = siftedSum A b w +
        ∑ p ∈ Finset.Ico a b,
          if p.Prime then siftedSum (divisorSlice A p) p w else 0 := by
    intro b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
        rw [Finset.sum_Ico_succ_top hab]
        calc
          siftedSum A a w = siftedSum A b w +
              ∑ p ∈ Finset.Ico a b,
                if p.Prime then siftedSum (divisorSlice A p) p w else 0 := ih
          _ = (siftedSum A (b + 1) w +
                if b.Prime then siftedSum (divisorSlice A b) b w else 0) +
              ∑ p ∈ Finset.Ico a b,
                if p.Prime then siftedSum (divisorSlice A p) p w else 0 := by
                  rw [weighted_buchstab_step A b w]
          _ = _ := by ac_rfl
  simpa [primeBand, Finset.sum_filter] using hraw b hab

theorem buchstab_card (A : Finset ℕ) (a b : ℕ) (hab : a ≤ b) :
    (sifted A a).card = (sifted A b).card +
      ∑ p ∈ primeBand a b, (sifted (divisorSlice A p) p).card := by
  simpa [siftedSum] using weighted_buchstab A a b (fun _ => (1 : ℕ)) hab

theorem divisorSlice_mul (A : Finset ℕ) {p q : ℕ} (hpq : p.Coprime q) :
    divisorSlice (divisorSlice A p) q = divisorSlice A (p * q) := by
  ext n
  simp only [divisorSlice, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hn, hp⟩, hq⟩
    exact ⟨hn, hpq.mul_dvd_of_dvd_of_dvd hp hq⟩
  · rintro ⟨hn, hpq'⟩
    exact ⟨⟨hn, dvd_trans (dvd_mul_right p q) hpq'⟩,
      dvd_trans (dvd_mul_left q p) hpq'⟩

/-- A second Buchstab expansion, with a cutoff depending on the first prime.
This produces the positive correction terms used in Harman's sieve decomposition. -/
theorem weighted_buchstab_refined {α : Type*} [AddCommGroup α]
    (A : Finset ℕ) (a b : ℕ) (z : ℕ → ℕ) (w : ℕ → α)
    (hab : a ≤ b) (hz : ∀ p ∈ primeBand a b, z p ≤ p) :
    siftedSum A b w = siftedSum A a w -
        (∑ p ∈ primeBand a b, siftedSum (divisorSlice A p) (z p) w) +
        ∑ p ∈ primeBand a b, ∑ q ∈ primeBand (z p) p,
          siftedSum (divisorSlice A (p * q)) q w := by
  classical
  have hparts :
      (∑ p ∈ primeBand a b, siftedSum (divisorSlice A p) (z p) w) =
        (∑ p ∈ primeBand a b, siftedSum (divisorSlice A p) p w) +
        ∑ p ∈ primeBand a b, ∑ q ∈ primeBand (z p) p,
          siftedSum (divisorSlice A (p * q)) q w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [weighted_buchstab (divisorSlice A p) (z p) p w (hz p hp)]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2
    have hqp : q < p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2
    rw [divisorSlice_mul A ((Nat.coprime_primes hpPrime hqPrime).mpr
      (Ne.symm (Nat.ne_of_lt hqp)))]
  rw [weighted_buchstab A a b w hab, hparts]
  abel

theorem sum_primeBand_split {α : Type*} [AddCommMonoid α]
    (a b c : ℕ) (f : ℕ → α) (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ p ∈ primeBand a c, f p) =
      (∑ p ∈ primeBand a b, f p) + ∑ p ∈ primeBand b c, f p := by
  classical
  simpa only [primeBand, Finset.sum_filter] using
    (Finset.sum_Ico_consecutive (fun p => if p.Prime then f p else 0) hab hbc).symm

/-- The exact five-term Buchstab decomposition underlying Harman's section 2.
The cutoff `z p` may be chosen differently in the two prime bands. -/
theorem weighted_buchstab_five_terms {α : Type*} [AddCommGroup α]
    (A : Finset ℕ) (a b c : ℕ) (z : ℕ → ℕ) (w : ℕ → α)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hz : ∀ p ∈ primeBand a c, z p ≤ p) :
    siftedSum A c w = siftedSum A a w -
        (∑ p ∈ primeBand a b, siftedSum (divisorSlice A p) (z p) w) -
        (∑ p ∈ primeBand b c, siftedSum (divisorSlice A p) (z p) w) +
        (∑ p ∈ primeBand a b, ∑ q ∈ primeBand (z p) p,
          siftedSum (divisorSlice A (p * q)) q w) +
        ∑ p ∈ primeBand b c, ∑ q ∈ primeBand (z p) p,
          siftedSum (divisorSlice A (p * q)) q w := by
  rw [weighted_buchstab_refined A a c z w (le_trans hab hbc) hz,
    sum_primeBand_split a b c (fun p => siftedSum (divisorSlice A p) (z p) w) hab hbc,
    sum_primeBand_split a b c
      (fun p => ∑ q ∈ primeBand (z p) p, siftedSum (divisorSlice A (p * q)) q w)
      hab hbc]
  abel

end Erdos374.HarmanAnalytic151
end

#print axioms Erdos374.HarmanAnalytic151.weighted_buchstab_refined

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanAnalytic151.Rough,
    ``Erdos374.HarmanAnalytic151.sifted,
    ``Erdos374.HarmanAnalytic151.divisorSlice,
    ``Erdos374.HarmanAnalytic151.primeBand,
    ``Erdos374.HarmanAnalytic151.siftedSum,
    ``Erdos374.HarmanAnalytic151.rough_succ,
    ``Erdos374.HarmanAnalytic151.sifted_succ,
    ``Erdos374.HarmanAnalytic151.weighted_buchstab_step,
    ``Erdos374.HarmanAnalytic151.weighted_buchstab,
    ``Erdos374.HarmanAnalytic151.buchstab_card,
    ``Erdos374.HarmanAnalytic151.divisorSlice_mul,
    ``Erdos374.HarmanAnalytic151.weighted_buchstab_refined,
    ``Erdos374.HarmanAnalytic151.sum_primeBand_split,
    ``Erdos374.HarmanAnalytic151.weighted_buchstab_five_terms]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#eval "HARMAN ANALYTIC 151: unconditional weighted Buchstab identities checked"

end Update151_Component_22
/- END COMPONENT: HarmanAnalytic151.lean -/

/- BEGIN COMPONENT: HarmanAnalytic151Orientation.lean -/
section Update151_Component_23



/-! A checked orientation adapter. Its exceptional-measure hypothesis remains
an explicit analytic obligation; it is not a proof of Harman's theorem. -/

noncomputable section
open MeasureTheory Filter

namespace Erdos374.HarmanAnalytic151Orientation
open HarmanBoundary150

def backwardExponent151 : ℝ := 81 / 800
def initialExponent151 : ℝ := 399 / 400

def realBackwardBad151 : Set ℝ :=
  {x | ¬ ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧
    x - (p : ℝ) ≤ x ^ backwardExponent151}

def RealBackwardExceptionalMeasure151 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ X : ℝ, Y ≤ X →
    volume.real (realBackwardBad151 ∩ Set.Icc 1 X) < ε * X

theorem bounded_backward_measure_finite151 (X : ℝ) :
    volume (realBackwardBad151 ∩ Set.Icc 1 X) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_right)

theorem eventual_power_dominance151 {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∃ Y : ℝ, ∀ X : ℝ, Y ≤ X → C * X ^ a < X ^ b := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (eventually_gt_atTop C))
  refine ⟨max Y 1, ?_⟩
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one ((le_max_right Y 1).trans hX)
  have hmul := mul_lt_mul_of_pos_left (hY X ((le_max_left Y 1).trans hX))
    (Real.rpow_pos_of_pos hX0 a)
  have hsplit : X ^ b = X ^ a * X ^ (b - a) := by
    rw [← Real.rpow_add hX0]
    congr 1
    ring
  simpa only [hsplit, mul_comm C] using hmul

theorem eventual_small_power151 {d : ℝ} (hd : d < 1) {η : ℝ} (hη : 0 < η) :
    ∃ Y : ℝ, ∀ X : ℝ, Y ≤ X → X ^ d < η * X := by
  obtain ⟨Y, hY⟩ := eventual_power_dominance151 hd (1 / η)
  refine ⟨Y, ?_⟩
  intro X hX
  have h := hY X hX
  rw [Real.rpow_one, div_mul_eq_mul_div, one_mul] at h
  simpa only [mul_comm] using (div_lt_iff₀ hη).mp h

theorem orientation_scale151 :
    ∃ Y : ℝ, ∀ X : ℝ, Y ≤ X →
      1 ≤ X ∧ (2 * X) ^ backwardExponent151 ≤ X ∧
        (2 * X) ^ backwardExponent151 ≤
          (X ^ initialExponent151) ^ realForwardExponent150 := by
  obtain ⟨Y, hY⟩ := eventual_power_dominance151
    (a := backwardExponent151)
    (b := initialExponent151 * realForwardExponent150)
    (by norm_num [backwardExponent151, initialExponent151, realForwardExponent150])
    ((2 : ℝ) ^ backwardExponent151)
  refine ⟨max Y 1, ?_⟩
  intro X hX
  have hX1 := (le_max_right Y 1).trans hX
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  have hscale := (hY X ((le_max_left Y 1).trans hX)).le
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX0] at hscale
  have hpow : X ^ (initialExponent151 * realForwardExponent150) ≤ X := by
    calc
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1
        (by norm_num [initialExponent151, realForwardExponent150])
      _ = X := Real.rpow_one X
  refine ⟨hX1, hscale.trans hpow, ?_⟩
  rwa [← Real.rpow_mul hX0]

theorem forward_bad_subset151 {X : ℝ} (hX : 1 ≤ X)
    (hL : (2 * X) ^ backwardExponent151 ≤ X)
    (hscale : (2 * X) ^ backwardExponent151 ≤
      (X ^ initialExponent151) ^ realForwardExponent150) :
    realForwardBad150 ∩ Set.Icc 1 X ⊆
      Set.Icc 1 (X ^ initialExponent151) ∪
      (fun x : ℝ => x + (2 * X) ^ backwardExponent151) ⁻¹'
        (realBackwardBad151 ∩ Set.Icc 1 (2 * X)) := by
  intro x hx
  by_cases hsmall : x ≤ X ^ initialExponent151
  · exact Or.inl ⟨hx.2.1, hsmall⟩
  right
  have hx0 : 0 ≤ x := zero_le_one.trans hx.2.1
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hL0 : 0 ≤ (2 * X) ^ backwardExponent151 :=
    Real.rpow_nonneg (by positivity) _
  have hy : x + (2 * X) ^ backwardExponent151 ≤ 2 * X := by linarith [hx.2.2]
  refine ⟨?_, by constructor <;> linarith [hx.2.1]⟩
  intro hprime
  rcases hprime with ⟨p, hp, hpupper, hplower⟩
  apply hx.1
  have hback : (x + (2 * X) ^ backwardExponent151) ^ backwardExponent151 ≤
      (2 * X) ^ backwardExponent151 :=
    Real.rpow_le_rpow (by positivity) hy (by norm_num [backwardExponent151])
  have hforward : (2 * X) ^ backwardExponent151 ≤ x ^ realForwardExponent150 :=
    hscale.trans (Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) (le_of_not_ge hsmall)
      (by norm_num [realForwardExponent150]))
  exact ⟨p, hp, by linarith, by linarith⟩

theorem forward_measure_bound151 {X : ℝ} (hX : 1 ≤ X)
    (hL : (2 * X) ^ backwardExponent151 ≤ X)
    (hscale : (2 * X) ^ backwardExponent151 ≤
      (X ^ initialExponent151) ^ realForwardExponent150) :
    volume.real (realForwardBad150 ∩ Set.Icc 1 X) ≤
      X ^ initialExponent151 + volume.real (realBackwardBad151 ∩ Set.Icc 1 (2 * X)) := by
  have hshift : volume ((fun x : ℝ => x + (2 * X) ^ backwardExponent151) ⁻¹'
      (realBackwardBad151 ∩ Set.Icc 1 (2 * X))) =
      volume (realBackwardBad151 ∩ Set.Icc 1 (2 * X)) :=
    measure_preimage_add_right _ _ _
  have hfinite : volume (Set.Icc 1 (X ^ initialExponent151) ∪
      (fun x : ℝ => x + (2 * X) ^ backwardExponent151) ⁻¹'
        (realBackwardBad151 ∩ Set.Icc 1 (2 * X))) ≠ ⊤ :=
    measure_union_ne_top (by simp) (by rw [hshift]; exact bounded_backward_measure_finite151 _)
  have hrealshift : volume.real ((fun x : ℝ => x + (2 * X) ^ backwardExponent151) ⁻¹'
      (realBackwardBad151 ∩ Set.Icc 1 (2 * X))) =
      volume.real (realBackwardBad151 ∩ Set.Icc 1 (2 * X)) := by
    simp only [measureReal_def, hshift]
  have hI : volume.real (Set.Icc 1 (X ^ initialExponent151)) ≤ X ^ initialExponent151 := by
    rw [Real.volume_real_Icc]
    exact max_le (by linarith) (Real.rpow_nonneg (zero_le_one.trans hX) _)
  calc
    _ ≤ volume.real (Set.Icc 1 (X ^ initialExponent151) ∪
          (fun x : ℝ => x + (2 * X) ^ backwardExponent151) ⁻¹'
            (realBackwardBad151 ∩ Set.Icc 1 (2 * X))) :=
      measureReal_mono (forward_bad_subset151 hX hL hscale) hfinite
    _ ≤ volume.real (Set.Icc 1 (X ^ initialExponent151)) +
          volume.real ((fun x : ℝ => x + (2 * X) ^ backwardExponent151) ⁻¹'
            (realBackwardBad151 ∩ Set.Icc 1 (2 * X))) := measureReal_union_le _ _
    _ ≤ _ := by rw [hrealshift]; exact add_le_add hI le_rfl

theorem real_forward_from_backward151
    (H : RealBackwardExceptionalMeasure151) : RealForwardExceptionalMeasure150 := by
  intro ε hε
  obtain ⟨Yb, hb⟩ := H (ε / 4) (by positivity)
  obtain ⟨Ys, hs⟩ := orientation_scale151
  obtain ⟨Yi, hi⟩ := eventual_small_power151
    (d := initialExponent151) (by norm_num [initialExponent151])
    (η := ε / 2) (by positivity)
  refine ⟨max (max Yb Ys) Yi, ?_⟩
  intro X hX
  have hXs : Ys ≤ X := (le_max_right Yb Ys).trans ((le_max_left _ _).trans hX)
  obtain ⟨hX1, hL, hscale⟩ := hs X hXs
  have hXb : Yb ≤ 2 * X := by
    have := (le_max_left Yb Ys).trans ((le_max_left _ _).trans hX)
    linarith
  have hXi := hi X ((le_max_right _ _).trans hX)
  have hback := hb (2 * X) hXb
  have hbound := forward_measure_bound151 hX1 hL hscale
  linarith

end Erdos374.HarmanAnalytic151Orientation
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanAnalytic151Orientation.backwardExponent151,
    ``Erdos374.HarmanAnalytic151Orientation.initialExponent151,
    ``Erdos374.HarmanAnalytic151Orientation.realBackwardBad151,
    ``Erdos374.HarmanAnalytic151Orientation.RealBackwardExceptionalMeasure151,
    ``Erdos374.HarmanAnalytic151Orientation.bounded_backward_measure_finite151,
    ``Erdos374.HarmanAnalytic151Orientation.eventual_power_dominance151,
    ``Erdos374.HarmanAnalytic151Orientation.eventual_small_power151,
    ``Erdos374.HarmanAnalytic151Orientation.orientation_scale151,
    ``Erdos374.HarmanAnalytic151Orientation.forward_bad_subset151,
    ``Erdos374.HarmanAnalytic151Orientation.forward_measure_bound151,
    ``Erdos374.HarmanAnalytic151Orientation.real_forward_from_backward151]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanAnalytic151Orientation.real_forward_from_backward151
#eval "HARMAN ANALYTIC 151: backward-to-forward exceptional-measure adapter checked"

end Update151_Component_23
/- END COMPONENT: HarmanAnalytic151Orientation.lean -/

/- BEGIN COMPONENT: HarmanDyadic151.lean -/
section Update151_Component_24



/-! Dyadic exceptional-measure estimates imply prefix exceptional-measure
estimates. This is an unconditional adapter, not Harman's analytic theorem. -/

noncomputable section
open MeasureTheory

namespace Erdos374.HarmanDyadic151
open HarmanAnalytic151Orientation

def DyadicExceptionalMeasure151 (E : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ X : ℝ, Y ≤ X →
    volume.real (E ∩ Set.Icc X (2 * X)) ≤ ε * X

def RealBackwardDyadicExceptionalMeasure151 : Prop :=
  DyadicExceptionalMeasure151 realBackwardBad151

theorem bounded_exception_measure_finite151 (E : Set ℝ) (a b : ℝ) :
    volume (E ∩ Set.Icc a b) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_right)

theorem prefix_measure_le_endpoint151 (E : Set ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    volume.real (E ∩ Set.Icc 1 Y) ≤ Y := by
  calc
    _ ≤ volume.real (Set.Icc 1 Y) := measureReal_mono Set.inter_subset_right (by simp)
    _ ≤ Y := by rw [Real.volume_real_Icc]; exact max_le (by linarith) (by linarith)

theorem prefix_measure_doubling151 (E : Set ℝ) (X : ℝ) :
    volume.real (E ∩ Set.Icc 1 (2 * X)) ≤
      volume.real (E ∩ Set.Icc 1 X) + volume.real (E ∩ Set.Icc X (2 * X)) := by
  have hsub : E ∩ Set.Icc 1 (2 * X) ⊆
      (E ∩ Set.Icc 1 X) ∪ (E ∩ Set.Icc X (2 * X)) := by
    rintro x ⟨hxE, hx⟩
    rcases Set.Icc_subset_Icc_union_Icc (a := (1 : ℝ)) (b := X) (c := 2 * X) hx with h | h
    · exact Or.inl ⟨hxE, h⟩
    · exact Or.inr ⟨hxE, h⟩
  exact (measureReal_mono hsub (measure_union_ne_top
    (bounded_exception_measure_finite151 E 1 X)
    (bounded_exception_measure_finite151 E X (2 * X)))).trans (measureReal_union_le _ _)

theorem dyadic_prefix_bound151 (E : Set ℝ) {Y η : ℝ} (hY : 1 ≤ Y) (hη : 0 ≤ η)
    (H : ∀ X : ℝ, Y ≤ X → volume.real (E ∩ Set.Icc X (2 * X)) ≤ η * X) :
    ∀ n : ℕ, volume.real (E ∩ Set.Icc 1 ((2 : ℝ) ^ n * Y)) ≤
      Y + η * ((2 : ℝ) ^ n * Y) := by
  intro n
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact (prefix_measure_le_endpoint151 E hY).trans
      (le_add_of_nonneg_right (mul_nonneg hη (zero_le_one.trans hY)))
  | succ n ih =>
    have hscale : Y ≤ (2 : ℝ) ^ n * Y := by
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith [zero_le_one.trans hY]
    have hsplit := prefix_measure_doubling151 E ((2 : ℝ) ^ n * Y)
    have hblock := H _ hscale
    have heq : (2 : ℝ) ^ (n + 1) * Y = 2 * ((2 : ℝ) ^ n * Y) := by rw [pow_succ]; ring
    rw [heq]
    nlinarith

theorem covering_dyadic_scale151 {Y X : ℝ} (hY : 0 < Y) (hYX : Y ≤ X) :
    ∃ n : ℕ, X ≤ (2 : ℝ) ^ n * Y ∧ (2 : ℝ) ^ n * Y ≤ 2 * X := by
  have hratio : 1 ≤ X / Y := (le_div_iff₀ hY).mpr (by simpa using hYX)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, ?_, ?_⟩
  · exact ((div_lt_iff₀ hY).mp hnhi).le
  · have h := (le_div_iff₀ hY).mp hnlo
    rw [pow_succ]
    nlinarith

/-- No measurability assumption on the exceptional set is needed: all uses
of real-valued measure are on sets with explicitly finite outer measure. -/
theorem prefix_from_dyadic151 (E : Set ℝ) (H : DyadicExceptionalMeasure151 E) :
    ∀ ε : ℝ, 0 < ε → ∃ Z : ℝ, ∀ X : ℝ, Z ≤ X →
      volume.real (E ∩ Set.Icc 1 X) < ε * X := by
  intro ε hε
  obtain ⟨Y₀, hY₀⟩ := H (ε / 4) (by positivity)
  let Y : ℝ := max Y₀ 1
  have hY : 1 ≤ Y := le_max_right _ _
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hblock : ∀ X : ℝ, Y ≤ X →
      volume.real (E ∩ Set.Icc X (2 * X)) ≤ (ε / 4) * X := by
    intro X hX
    exact hY₀ X ((le_max_left Y₀ 1).trans hX)
  refine ⟨max Y (4 * Y / ε), ?_⟩
  intro X hX
  have hYX : Y ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := hY0.trans_le hYX
  have hlarge : 4 * Y ≤ ε * X := by
    have h := (div_le_iff₀ hε).mp ((le_max_right Y (4 * Y / ε)).trans hX)
    simpa only [mul_comm] using h
  obtain ⟨n, hnlo, hnhi⟩ := covering_dyadic_scale151 hY0 hYX
  have hmono : volume.real (E ∩ Set.Icc 1 X) ≤
      volume.real (E ∩ Set.Icc 1 ((2 : ℝ) ^ n * Y)) :=
    measureReal_mono (Set.inter_subset_inter_right E (Set.Icc_subset_Icc_right hnlo))
      (bounded_exception_measure_finite151 E 1 _)
  have hbound := dyadic_prefix_bound151 E hY (by positivity : 0 ≤ ε / 4) hblock n
  have hscale := mul_le_mul_of_nonneg_left hnhi (by positivity : 0 ≤ ε / 4)
  have hpos : 0 < ε * X := mul_pos hε hX0
  nlinarith

theorem backward_prefix_from_dyadic151 (H : RealBackwardDyadicExceptionalMeasure151) :
    RealBackwardExceptionalMeasure151 :=
  prefix_from_dyadic151 realBackwardBad151 H

theorem real_forward_from_backward_dyadic151 (H : RealBackwardDyadicExceptionalMeasure151) :
    HarmanBoundary150.RealForwardExceptionalMeasure150 :=
  real_forward_from_backward151 (backward_prefix_from_dyadic151 H)

end Erdos374.HarmanDyadic151
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanDyadic151.DyadicExceptionalMeasure151,
    ``Erdos374.HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151,
    ``Erdos374.HarmanDyadic151.bounded_exception_measure_finite151,
    ``Erdos374.HarmanDyadic151.prefix_measure_le_endpoint151,
    ``Erdos374.HarmanDyadic151.prefix_measure_doubling151,
    ``Erdos374.HarmanDyadic151.dyadic_prefix_bound151,
    ``Erdos374.HarmanDyadic151.covering_dyadic_scale151,
    ``Erdos374.HarmanDyadic151.prefix_from_dyadic151,
    ``Erdos374.HarmanDyadic151.backward_prefix_from_dyadic151,
    ``Erdos374.HarmanDyadic151.real_forward_from_backward_dyadic151]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanDyadic151.real_forward_from_backward_dyadic151
#eval "HARMAN DYADIC 151: source-facing dyadic-to-prefix exceptional-measure adapter checked"

end Update151_Component_24
/- END COMPONENT: HarmanDyadic151.lean -/

/- BEGIN COMPONENT: HarmanAnalytic151MeanSquare.lean -/
section Update151_Component_25




/-! Finite exponential-polynomial mean squares with explicit off-diagonal
bounds. These are unconditional analytic lemmas, not exceptional-set axioms. -/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Erdos374.HarmanAnalytic151MeanSquare

def exponentialKernel151 (ω t : ℝ) : ℂ :=
  Complex.exp ((Complex.I * (ω : ℂ)) * (t : ℂ))

def exponentialSum151 {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ξ : ι → ℝ) (t : ℝ) : ℂ := ∑ n ∈ s, a n * exponentialKernel151 (ξ n) t

theorem continuous_kernel151 (ω : ℝ) : Continuous (exponentialKernel151 ω) := by
  unfold exponentialKernel151
  fun_prop

theorem norm_kernel151 (ω t : ℝ) : ‖exponentialKernel151 ω t‖ = 1 := by
  simp [exponentialKernel151, Complex.norm_exp]

theorem kernel_zero151 (t : ℝ) : exponentialKernel151 0 t = 1 := by
  simp [exponentialKernel151]

theorem kernel_mul_conj151 (ω ν t : ℝ) :
    exponentialKernel151 ω t * conj (exponentialKernel151 ν t) =
      exponentialKernel151 (ω - ν) t := by
  unfold exponentialKernel151
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

theorem integral_kernel151 (ω A B : ℝ) (hω : ω ≠ 0) :
    (∫ t in A..B, exponentialKernel151 ω t) =
      (exponentialKernel151 ω B - exponentialKernel151 ω A) /
        (Complex.I * (ω : ℂ)) := by
  exact integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hω))

theorem norm_integral_kernel_le151 (ω A B : ℝ) (hω : ω ≠ 0) :
    ‖∫ t in A..B, exponentialKernel151 ω t‖ ≤ 2 / |ω| := by
  rw [integral_kernel151 ω A B hω, norm_div]
  have hnum : ‖exponentialKernel151 ω B - exponentialKernel151 ω A‖ ≤ 2 := by
    simpa only [norm_kernel151, one_add_one_eq_two] using
      norm_sub_le (exponentialKernel151 ω B) (exponentialKernel151 ω A)
  simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using
    div_le_div_of_nonneg_right hnum (norm_nonneg (Complex.I * (ω : ℂ)))

theorem continuous_sum151 {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ξ : ι → ℝ) :
    Continuous (exponentialSum151 s a ξ) := by
  unfold exponentialSum151
  exact continuous_finsetSum s (fun n _ => continuous_const.mul (continuous_kernel151 _))

theorem norm_square_expansion151 {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) :
    ((‖exponentialSum151 s a ξ t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) * exponentialKernel151 (ξ m - ξ n) t := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [exponentialSum151, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [← kernel_mul_conj151]
  ring

theorem mean_square_expansion151 {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ) :
    ((∫ t in A..B, ‖exponentialSum151 s a ξ t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel151 (ξ m - ξ n) t := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [norm_square_expansion151]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro n hn
      exact (continuous_const.mul (continuous_kernel151 _)).intervalIntegrable _ _
  · intro m hm
    exact (continuous_finsetSum s fun n _ =>
      continuous_const.mul (continuous_kernel151 _)).intervalIntegrable _ _

theorem mean_square_diagonal151 {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ) :
    ((∫ t in A..B, ‖exponentialSum151 s a ξ t‖ ^ 2 : ℝ) : ℂ) -
        ((B - A) * ∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) =
      ∑ m ∈ s, ∑ n ∈ s.erase m, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel151 (ξ m - ξ n) t := by
  rw [mean_square_expansion151]
  have hsplit :
      (∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel151 (ξ m - ξ n) t) =
      ((B - A) * ∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) +
        ∑ m ∈ s, ∑ n ∈ s.erase m, a m * conj (a n) *
          ∫ t in A..B, exponentialKernel151 (ξ m - ξ n) t := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.add_sum_erase s
      (fun n => a m * conj (a n) * ∫ t in A..B, exponentialKernel151 (ξ m - ξ n) t) hm]
    congr 1
    simp [kernel_zero151, Complex.mul_conj', Complex.real_smul, mul_comm]
  rw [hsplit]
  ring

theorem mean_square_error_le151 {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ)
    (hξ : Set.InjOn ξ (s : Set ι)) :
    |(∫ t in A..B, ‖exponentialSum151 s a ξ t‖ ^ 2) -
      (B - A) * ∑ n ∈ s, ‖a n‖ ^ 2| ≤
      ∑ m ∈ s, ∑ n ∈ s.erase m, 2 * ‖a m‖ * ‖a n‖ / |ξ m - ξ n| := by
  have hdiag := mean_square_diagonal151 s a ξ A B
  have hnorm := congrArg norm hdiag
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [hnorm]
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro m hm
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro n hn
  have hnm := Finset.mem_erase.mp hn
  have hne : ξ m - ξ n ≠ 0 := sub_ne_zero.mpr fun h =>
    hnm.1 (hξ hnm.2 hm h.symm)
  have hbound := mul_le_mul_of_nonneg_left (norm_integral_kernel_le151 (ξ m - ξ n) A B hne)
    (mul_nonneg (norm_nonneg (a m)) (norm_nonneg (a n)))
  simp only [norm_mul, RCLike.norm_conj]
  calc
    _ ≤ ‖a m‖ * ‖a n‖ * (2 / |ξ m - ξ n|) := hbound
    _ = _ := by ring

end Erdos374.HarmanAnalytic151MeanSquare
end

#print axioms Erdos374.HarmanAnalytic151MeanSquare.mean_square_error_le151

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151,
    ``Erdos374.HarmanAnalytic151MeanSquare.exponentialSum151,
    ``Erdos374.HarmanAnalytic151MeanSquare.continuous_kernel151,
    ``Erdos374.HarmanAnalytic151MeanSquare.norm_kernel151,
    ``Erdos374.HarmanAnalytic151MeanSquare.kernel_zero151,
    ``Erdos374.HarmanAnalytic151MeanSquare.kernel_mul_conj151,
    ``Erdos374.HarmanAnalytic151MeanSquare.integral_kernel151,
    ``Erdos374.HarmanAnalytic151MeanSquare.norm_integral_kernel_le151,
    ``Erdos374.HarmanAnalytic151MeanSquare.continuous_sum151,
    ``Erdos374.HarmanAnalytic151MeanSquare.norm_square_expansion151,
    ``Erdos374.HarmanAnalytic151MeanSquare.mean_square_expansion151,
    ``Erdos374.HarmanAnalytic151MeanSquare.mean_square_diagonal151,
    ``Erdos374.HarmanAnalytic151MeanSquare.mean_square_error_le151]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#eval "HARMAN ANALYTIC 151: finite mean-square expansion and kernel bounds checked"


end Update151_Component_25
/- END COMPONENT: HarmanAnalytic151MeanSquare.lean -/

/- BEGIN COMPONENT: HarmanAnalytic151LogRows.lean -/
section Update151_Component_26


noncomputable section
open scoped BigOperators

namespace Erdos374.HarmanAnalytic151MeanSquare

theorem log_difference_lower151 {x y N : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hyN : y ≤ N) : (y - x) / N ≤ Real.log y - Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : 0 < N := hy.trans_le hyN
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [inv_div, Real.log_div hy.ne' hx.ne'] at hlog
  have hdiv : (y - x) / y ≤ Real.log y - Real.log x := by
    convert hlog using 1 <;> field_simp <;> ring
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hyN).trans hdiv

theorem inverse_log_difference_le151 {m n N : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmN : m ≤ N) (hnN : n ≤ N) (hmn : m ≠ n) :
    1 / |Real.log m - Real.log n| ≤ (N : ℝ) / |(m : ℝ) - n| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hN0 : (0 : ℝ) < N := hm0.trans_le (by exact_mod_cast hmN)
  have hdist : 0 < |(m : ℝ) - n| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hmn))
  have hgap : |(m : ℝ) - n| / N ≤ |Real.log m - Real.log n| := by
    rcases le_total m n with hle | hle
    · have h := log_difference_lower151 (y := (n : ℝ)) (N := (N : ℝ))
        hm0 (by exact_mod_cast hle) (by exact_mod_cast hnN)
      rw [abs_sub_comm (m : ℝ) n,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle : (m : ℝ) ≤ n)),
        abs_sub_comm (Real.log m) (Real.log n),
        abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 (by exact_mod_cast hle)))]
      exact h
    · have h := log_difference_lower151 (y := (m : ℝ)) (N := (N : ℝ))
        hn0 (by exact_mod_cast hle) (by exact_mod_cast hmN)
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℝ) ≤ m)),
        abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast hle)))]
      exact h
  have hlog : 0 < |Real.log m - Real.log n| := (div_pos hdist hN0).trans_le hgap
  apply (div_le_div_iff₀ hlog hdist).mpr
  simpa only [one_mul, mul_one, mul_comm] using (div_le_iff₀ hN0).mp hgap

theorem inverse_distance_row151 (s : Finset ℕ) (m N : ℕ)
    (hmN : m ≤ N) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) :
    (∑ n ∈ s.erase m, 1 / |(m : ℝ) - n|) ≤ 2 * (harmonic N : ℝ) := by
  let lo := (s.erase m).filter (· < m)
  let hi := (s.erase m).filter (fun n => ¬ n < m)
  have hlo_mem : ∀ n ∈ lo, n < m ∧ n ≤ N := by
    intro n hn
    exact ⟨(Finset.mem_filter.mp hn).2,
      (hs n (Finset.mem_erase.mp (Finset.mem_filter.mp hn).1).2).2⟩
  have hhi_mem : ∀ n ∈ hi, m < n ∧ n ≤ N := by
    intro n hn
    have h := Finset.mem_filter.mp hn
    have hne := (Finset.mem_erase.mp h.1).1
    exact ⟨by omega, (hs n (Finset.mem_erase.mp h.1).2).2⟩
  have hlo_image : lo.image (fun n => m - n) ⊆ Finset.Icc 1 N := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have := hlo_mem n hn
    simp only [Finset.mem_Icc]
    omega
  have hhi_image : hi.image (fun n => n - m) ⊆ Finset.Icc 1 N := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have := hhi_mem n hn
    simp only [Finset.mem_Icc]
    omega
  have hlo : (∑ n ∈ lo, 1 / |(m : ℝ) - n|) ≤ (harmonic N : ℝ) := by
    have heq : (∑ n ∈ lo, 1 / |(m : ℝ) - n|) =
        ∑ k ∈ lo.image (fun n => m - n), (k : ℝ)⁻¹ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        have hnm := (hlo_mem n hn).1.le
        rw [Nat.cast_sub hnm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm)), one_div]
      · intro n hn k hk heq
        dsimp at heq
        have := hlo_mem n hn
        have := hlo_mem k hk
        omega
    rw [heq]
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hlo_image (fun k _ _ => by positivity)
      _ = _ := by simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hhi : (∑ n ∈ hi, 1 / |(m : ℝ) - n|) ≤ (harmonic N : ℝ) := by
    have heq : (∑ n ∈ hi, 1 / |(m : ℝ) - n|) =
        ∑ k ∈ hi.image (fun n => n - m), (k : ℝ)⁻¹ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        have hmn := (hhi_mem n hn).1.le
        rw [Nat.cast_sub hmn, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn)), one_div]
      · intro n hn k hk heq
        dsimp at heq
        have := hhi_mem n hn
        have := hhi_mem k hk
        omega
    rw [heq]
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hhi_image (fun k _ _ => by positivity)
      _ = _ := by simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s.erase m)
    (· < m) (fun n => 1 / |(m : ℝ) - n|)
  change (∑ n ∈ lo, 1 / |(m : ℝ) - n|) +
    (∑ n ∈ hi, 1 / |(m : ℝ) - n|) = _ at hsplit
  linarith

theorem inverse_log_row151 (s : Finset ℕ) (m N : ℕ) (hm : m ∈ s)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) :
    (∑ n ∈ s, 1 / |Real.log m - Real.log n|) ≤ 2 * N * (harmonic N : ℝ) := by
  rw [← Finset.sum_erase (a := m) (s := s) (by simp : 1 / |Real.log m - Real.log m| = (0 : ℝ))]
  calc
    _ ≤ ∑ n ∈ s.erase m, (N : ℝ) / |(m : ℝ) - n| := by
      apply Finset.sum_le_sum
      intro n hn
      have hnm := Finset.mem_erase.mp hn
      exact inverse_log_difference_le151 (hs m hm).1 (hs n hnm.2).1
        (hs m hm).2 (hs n hnm.2).2 hnm.1.symm
    _ = (N : ℝ) * ∑ n ∈ s.erase m, 1 / |(m : ℝ) - n| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (N : ℝ) * (2 * (harmonic N : ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_distance_row151 s m N (hs m hm).2 hs) (Nat.cast_nonneg _)
    _ = _ := by ring

end Erdos374.HarmanAnalytic151MeanSquare
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanAnalytic151MeanSquare.log_difference_lower151,
    ``Erdos374.HarmanAnalytic151MeanSquare.inverse_log_difference_le151,
    ``Erdos374.HarmanAnalytic151MeanSquare.inverse_distance_row151,
    ``Erdos374.HarmanAnalytic151MeanSquare.inverse_log_row151]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanAnalytic151MeanSquare.inverse_log_row151

end Update151_Component_26
/- END COMPONENT: HarmanAnalytic151LogRows.lean -/

/- BEGIN COMPONENT: HarmanAnalytic151Dirichlet.lean -/
section Update151_Component_27


noncomputable section
open scoped BigOperators

namespace Erdos374.HarmanAnalytic151MeanSquare

theorem quadratic_pair_bound151 {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (W : ι → ι → ℝ) (R : ℝ)
    (hW : ∀ m ∈ s, ∀ n ∈ s, 0 ≤ W m n)
    (hSym : ∀ m ∈ s, ∀ n ∈ s, W m n = W n m)
    (hRow : ∀ m ∈ s, (∑ n ∈ s, W m n) ≤ R) :
    (∑ m ∈ s, ∑ n ∈ s, 2 * u m * u n * W m n) ≤
      2 * R * ∑ m ∈ s, u m ^ 2 := by
  have hstep : (∑ m ∈ s, ∑ n ∈ s, 2 * u m * u n * W m n) ≤
      ∑ m ∈ s, ∑ n ∈ s, (u m ^ 2 + u n ^ 2) * W m n := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (u m - u n)]) (hW m hm n hn)
  have hswap : (∑ m ∈ s, ∑ n ∈ s, u n ^ 2 * W m n) =
      ∑ m ∈ s, ∑ n ∈ s, u m ^ 2 * W m n := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    rw [hSym n hn m hm]
  calc
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, (u m ^ 2 + u n ^ 2) * W m n := hstep
    _ = 2 * ∑ m ∈ s, u m ^ 2 * ∑ n ∈ s, W m n := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [hswap]
      simp_rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * ∑ m ∈ s, u m ^ 2 * R := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (hRow m hm) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem dirichlet_mean_square_error151 (s : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (A B : ℝ) :
    |(∫ t in A..B, ‖exponentialSum151 s a (fun n => Real.log n) t‖ ^ 2) -
        (B - A) * ∑ n ∈ s, ‖a n‖ ^ 2| ≤
      4 * N * (harmonic N : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have hInj : Set.InjOn (fun n : ℕ => Real.log n) (s : Set ℕ) := by
    intro m hm n hn heq
    dsimp at heq
    apply Nat.cast_injective (R := ℝ)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt (hs m hm).1)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt (hs n hn).1)
    rw [← Real.exp_log hm0, ← Real.exp_log hn0, heq]
  have hpair := quadratic_pair_bound151 s (fun n => ‖a n‖)
    (fun m n => 1 / |Real.log m - Real.log n|) (2 * N * (harmonic N : ℝ))
    (fun m _ n _ => by positivity)
    (fun m _ n _ => by rw [abs_sub_comm])
    (fun m hm => inverse_log_row151 s m N hm hs)
  calc
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
        2 * ‖a m‖ * ‖a n‖ / |Real.log m - Real.log n| :=
      mean_square_error_le151 s a (fun n => Real.log n) A B hInj
    _ = ∑ m ∈ s, ∑ n ∈ s,
        2 * ‖a m‖ * ‖a n‖ * (1 / |Real.log m - Real.log n|) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.sum_erase (a := m) (s := s)
        (by simp : 2 * ‖a m‖ * ‖a m‖ * (1 / |Real.log m - Real.log m|) = (0 : ℝ))]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 2 * (2 * N * (harmonic N : ℝ)) * ∑ n ∈ s, ‖a n‖ ^ 2 := hpair
    _ = _ := by ring

/-- An unconditional finite Dirichlet-polynomial mean-square estimate, with
an explicit logarithmic loss and arbitrary complex coefficients. -/
theorem dirichlet_mean_square_le151 (s : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (A B : ℝ) :
    (∫ t in A..B, ‖exponentialSum151 s a (fun n => Real.log n) t‖ ^ 2) ≤
      (B - A + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have herr := dirichlet_mean_square_error151 s a N hs A B
  have hsum : 0 ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound : 4 * N * (harmonic N : ℝ) * (∑ n ∈ s, ‖a n‖ ^ 2) ≤
      4 * N * (1 + Real.log N) * (∑ n ∈ s, ‖a n‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)) hsum
  have habs := le_abs_self ((∫ t in A..B, ‖exponentialSum151 s a (fun n => Real.log n) t‖ ^ 2) -
      (B - A) * ∑ n ∈ s, ‖a n‖ ^ 2)
  nlinarith

end Erdos374.HarmanAnalytic151MeanSquare
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanAnalytic151MeanSquare.quadratic_pair_bound151,
    ``Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_error151,
    ``Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_le151]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_le151
#eval "HARMAN ANALYTIC 151: unconditional finite Dirichlet-polynomial mean-square bound checked"

end Update151_Component_27
/- END COMPONENT: HarmanAnalytic151Dirichlet.lean -/

/- BEGIN COMPONENT: HarmanAnalytic151Sampling.lean -/
section Update151_Component_28




noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.HarmanAnalytic151MeanSquare

theorem sample_point_le_integral151 (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hfd : Differentiable ℝ f)
    (hd : ∀ t, |deriv f t| ≤ g t) (hg0 : ∀ t, 0 ≤ g t) (r : ℝ) :
    f r ≤ ∫ t in r..r + 1, f t + g t := by
  have hpoint : ∀ t ∈ Set.Icc r (r + 1), f r ≤ f t + ∫ u in r..r + 1, g u := by
    intro t ht
    have hsub := norm_sub_le_integral_of_norm_deriv_le_of_le ht.1
      hf.continuousOn hfd.differentiableOn
      (Filter.Eventually.of_forall (fun u _ => by simpa only [Real.norm_eq_abs] using hd u))
      (hg.intervalIntegrable r t)
    have hmono := intervalIntegral.integral_mono_interval (μ := volume) (a := r) (b := t)
      (c := r) (d := r + 1) le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall hg0) (hg.intervalIntegrable _ _)
    rw [Real.norm_eq_abs] at hsub
    have hneg := neg_abs_le (f t - f r)
    linarith
  have hint := intervalIntegral.integral_mono_on (μ := volume) (a := r) (b := r + 1)
    (by linarith) (f := fun _ => f r)
    (g := fun t => f t + ∫ u in r..r + 1, g u)
    (continuous_const.intervalIntegrable _ _)
    ((hf.add continuous_const).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  simpa only [intervalIntegral.integral_add (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const,
      add_sub_cancel_left, one_smul] using hint

theorem separated_sampling151 (r : Finset ℝ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hfd : Differentiable ℝ f)
    (hd : ∀ t, |deriv f t| ≤ g t) (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (A B : ℝ) (hAB : A ≤ B) (hr : ∀ t ∈ r, A ≤ t ∧ t ≤ B) :
    (∑ t ∈ r, f t) ≤ ∫ t in A..B + 1, f t + g t := by
  have hdis : Set.Pairwise (r : Set ℝ)
      (fun x y => Disjoint (Set.Ioc x (x + 1)) (Set.Ioc y (y + 1))) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hxz hyz
    have hlt : |x - y| < 1 := abs_lt.mpr ⟨by linarith [hxz.2, hyz.1], by linarith [hxz.1, hyz.2]⟩
    exact (not_lt_of_ge (hsep x hx y hy hxy)) hlt
  have hsubset : (⋃ t ∈ r, Set.Ioc t (t + 1)) ⊆ Set.Ioc A (B + 1) := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    have htr := hr t ht
    exact ⟨lt_of_le_of_lt htr.1 hxt.1, by linarith [hxt.2]⟩
  have hc : Continuous (fun t => f t + g t) := hf.add hg
  calc
    _ ≤ ∑ t ∈ r, ∫ x in t..t + 1, f x + g x :=
      Finset.sum_le_sum (fun t _ => sample_point_le_integral151 f g hf hg hfd hd hg0 t)
    _ = ∑ t ∈ r, ∫ x in Set.Ioc t (t + 1), f x + g x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact intervalIntegral.integral_of_le (by linarith)
    _ = ∫ x in ⋃ t ∈ r, Set.Ioc t (t + 1), f x + g x :=
      (integral_biUnion_finset r (fun _ _ => measurableSet_Ioc) hdis
        (fun t _ => (hc.intervalIntegrable t (t + 1)).1)).symm
    _ ≤ ∫ x in Set.Ioc A (B + 1), f x + g x :=
      setIntegral_mono_set (hc.intervalIntegrable A (B + 1)).1
        (Filter.Eventually.of_forall (fun x => add_nonneg (hf0 x) (hg0 x))) hsubset.eventuallySubset
    _ = _ := (intervalIntegral.integral_of_le (by linarith)).symm

end Erdos374.HarmanAnalytic151MeanSquare
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanAnalytic151MeanSquare.sample_point_le_integral151,
    ``Erdos374.HarmanAnalytic151MeanSquare.separated_sampling151]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanAnalytic151MeanSquare.separated_sampling151

end Update151_Component_28
/- END COMPONENT: HarmanAnalytic151Sampling.lean -/

/- BEGIN COMPONENT: HarmanAnalytic151LargeValues.lean -/
section Update151_Component_29


noncomputable section
open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace Erdos374.HarmanAnalytic151MeanSquare

theorem hasDerivAt_kernel151 (ω t : ℝ) :
    HasDerivAt (exponentialKernel151 ω)
      ((Complex.I * (ω : ℂ)) * exponentialKernel151 ω t) t := by
  unfold exponentialKernel151
  have h : HasDerivAt (fun t : ℝ => (Complex.I * (ω : ℂ)) * (t : ℂ))
      (Complex.I * (ω : ℂ)) t := by
    simpa only [mul_one] using!
      ((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * (ω : ℂ))).comp_ofReal
  simpa [mul_comm] using! h.cexp

def derivativeCoefficients151 {ι : Type*} (a : ι → ℂ) (ξ : ι → ℝ) : ι → ℂ :=
  fun n => a n * (Complex.I * (ξ n : ℂ))

theorem hasDerivAt_sum151 {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ξ : ι → ℝ) (t : ℝ) :
    HasDerivAt (exponentialSum151 s a ξ)
      (exponentialSum151 s (derivativeCoefficients151 a ξ) ξ t) t := by
  unfold exponentialSum151
  have h := HasDerivAt.fun_sum (u := s)
    (fun n _ => (hasDerivAt_kernel151 (ξ n) t).const_mul (a n))
  simpa only [derivativeCoefficients151, mul_assoc] using! h

theorem complex_separated_sampling151 (r : Finset ℝ) (D D' : ℝ → ℂ)
    (hD : ∀ t, HasDerivAt D (D' t) t) (hC : Continuous D) (hC' : Continuous D')
    (L : ℝ) (hL : 0 < L)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (A B : ℝ) (hAB : A ≤ B) (hr : ∀ t ∈ r, A ≤ t ∧ t ≤ B) :
    (∑ t ∈ r, ‖D t‖ ^ 2) ≤
      (1 + L) * (∫ t in A..B + 1, ‖D t‖ ^ 2) +
        (1 / L) * (∫ t in A..B + 1, ‖D' t‖ ^ 2) := by
  have hF : Continuous (fun t => ‖D t‖ ^ 2) := hC.norm.pow 2
  have hF' : Continuous (fun t => ‖D' t‖ ^ 2) := hC'.norm.pow 2
  have hG : Continuous (fun t => L * ‖D t‖ ^ 2 + ‖D' t‖ ^ 2 / L) :=
    (continuous_const.mul hF).add (hF'.div_const L)
  have hderiv : ∀ t, |deriv (fun t => ‖D t‖ ^ 2) t| ≤
      L * ‖D t‖ ^ 2 + ‖D' t‖ ^ 2 / L := by
    intro t
    rw [(hD t).norm_sq.deriv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hinner := abs_real_inner_le_norm (D t) (D' t)
    have hsq := sq_nonneg (L * ‖D t‖ - ‖D' t‖)
    have hdiv : ‖D' t‖ ^ 2 / L * L = ‖D' t‖ ^ 2 := div_mul_cancel₀ _ hL.ne'
    nlinarith
  have hsamp := separated_sampling151 r (fun t => ‖D t‖ ^ 2)
    (fun t => L * ‖D t‖ ^ 2 + ‖D' t‖ ^ 2 / L)
    hF hG (fun t => (hD t).norm_sq.differentiableAt) hderiv
    (fun _ => sq_nonneg _) (fun _ => by positivity) hsep A B hAB hr
  calc
    _ ≤ ∫ t in A..B + 1, ‖D t‖ ^ 2 + (L * ‖D t‖ ^ 2 + ‖D' t‖ ^ 2 / L) := hsamp
    _ = _ := by
      rw [intervalIntegral.integral_add (hF.intervalIntegrable _ _) (hG.intervalIntegrable _ _),
        intervalIntegral.integral_add (f := fun t => L * ‖D t‖ ^ 2)
          (g := fun t => ‖D' t‖ ^ 2 / L) ((continuous_const.mul hF).intervalIntegrable _ _)
          ((hF'.div_const L).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
      ring

theorem derivative_coefficients_energy151 (s : Finset ℕ) (a : ℕ → ℂ)
    (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) :
    (∑ n ∈ s, ‖derivativeCoefficients151 a (fun n => Real.log n) n‖ ^ 2) ≤
      (max 1 (Real.log N)) ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hs n hn).1
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog : Real.log n ≤ max 1 (Real.log N) :=
    (Real.log_le_log hn0 (by exact_mod_cast (hs n hn).2)).trans (le_max_right _ _)
  have hmax0 : 0 ≤ max 1 (Real.log N) := zero_le_one.trans (le_max_left _ _)
  simp only [derivativeCoefficients151, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0, mul_pow]
  nlinarith [sq_nonneg ‖a n‖, mul_le_mul_of_nonneg_right
    (sq_le_sq₀ hlog0 hmax0 |>.mpr hlog) (sq_nonneg ‖a n‖)]

/-- Elementary separated-point mean square. This supplies a V^(-2)
large-value estimate, not the stronger Halász–Huxley V^(-6) term. -/
theorem dirichlet_separated_mean_square151 (s : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (r : Finset ℝ)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (A B : ℝ) (hAB : A ≤ B) (hr : ∀ t ∈ r, A ≤ t ∧ t ≤ B) :
    (∑ t ∈ r, ‖exponentialSum151 s a (fun n => Real.log n) t‖ ^ 2) ≤
      (1 + 2 * max 1 (Real.log N)) *
        (B + 1 - A + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  let L : ℝ := max 1 (Real.log N)
  let Q : ℝ := B + 1 - A + 4 * N * (1 + Real.log N)
  let E : ℝ := ∑ n ∈ s, ‖a n‖ ^ 2
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hBA : 0 ≤ B + 1 - A := by linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hfirst := dirichlet_mean_square_le151 s a N hs A (B + 1)
  have hsecond := dirichlet_mean_square_le151 s
    (derivativeCoefficients151 a (fun n => Real.log n)) N hs A (B + 1)
  have henergy := derivative_coefficients_energy151 s a N hs
  have hsamp := complex_separated_sampling151 r
    (exponentialSum151 s a (fun n => Real.log n))
    (exponentialSum151 s (derivativeCoefficients151 a (fun n => Real.log n)) (fun n => Real.log n))
    (hasDerivAt_sum151 s a _) (continuous_sum151 _ _ _) (continuous_sum151 _ _ _)
    L hL hsep A B hAB hr
  have hsecond' :
      (∫ t in A..B + 1,
        ‖exponentialSum151 s (derivativeCoefficients151 a (fun n => Real.log n))
          (fun n => Real.log n) t‖ ^ 2) ≤ Q * (L ^ 2 * E) :=
    hsecond.trans (mul_le_mul_of_nonneg_left henergy hQ)
  calc
    _ ≤ (1 + L) * (∫ t in A..B + 1, ‖exponentialSum151 s a (fun n => Real.log n) t‖ ^ 2) +
        (1 / L) * (∫ t in A..B + 1,
          ‖exponentialSum151 s (derivativeCoefficients151 a (fun n => Real.log n))
            (fun n => Real.log n) t‖ ^ 2) := hsamp
    _ ≤ (1 + L) * (Q * E) + (1 / L) * (Q * (L ^ 2 * E)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by positivity))
        (mul_le_mul_of_nonneg_left hsecond' (by positivity))
    _ = _ := by change _ = (1 + 2 * L) * Q * E; field_simp; ring

end Erdos374.HarmanAnalytic151MeanSquare
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanAnalytic151MeanSquare.hasDerivAt_kernel151,
    ``Erdos374.HarmanAnalytic151MeanSquare.derivativeCoefficients151,
    ``Erdos374.HarmanAnalytic151MeanSquare.hasDerivAt_sum151,
    ``Erdos374.HarmanAnalytic151MeanSquare.complex_separated_sampling151,
    ``Erdos374.HarmanAnalytic151MeanSquare.derivative_coefficients_energy151,
    ``Erdos374.HarmanAnalytic151MeanSquare.dirichlet_separated_mean_square151]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanAnalytic151MeanSquare.dirichlet_separated_mean_square151

end Update151_Component_29
/- END COMPONENT: HarmanAnalytic151LargeValues.lean -/

/- BEGIN COMPONENT: Erdos374_AnalyticClosure151.lean -/
section Update151_Component_30




/-! Current candidate endpoints. The two deep analytic inputs are still explicit.
The backward-real endpoint now matches the orientation of Harman's analytic source. -/
namespace Erdos374.AnalyticClosure151
open SamplingPolynomial149
open RemainingAnalytic115.RemainingAnalytic141
open HarmanAnalytic151Orientation

theorem candidate_main151
    (HF : DensityZero forwardBadIntervals141)
    (HS : PolynomialReciprocalPrimeSampling) : MainStatement :=
  candidate_main_from_polynomial_sampling149 ExternalInputs149.psiMediumPNT
    ExternalInputs149.coarseHyperellipticCount HF HS

theorem positive_lower_density151
    (HF : DensityZero forwardBadIntervals141)
    (HS : PolynomialReciprocalPrimeSampling) : PositiveLowerDensity D6 :=
  positive_lower_density_from_polynomial_sampling149 ExternalInputs149.psiMediumPNT
    ExternalInputs149.coarseHyperellipticCount HF HS

theorem candidate_main_from_backward151
    (HF : RealBackwardExceptionalMeasure151)
    (HS : PolynomialReciprocalPrimeSampling) : MainStatement :=
  candidate_main151
    (HarmanBoundary150.forward_density_from_real_measure150
      (real_forward_from_backward151 HF)) HS

theorem positive_lower_density_from_backward151
    (HF : RealBackwardExceptionalMeasure151)
    (HS : PolynomialReciprocalPrimeSampling) : PositiveLowerDensity D6 :=
  positive_lower_density151
    (HarmanBoundary150.forward_density_from_real_measure150
      (real_forward_from_backward151 HF)) HS

#check candidate_main151
#check candidate_main_from_backward151
#print axioms candidate_main151
#print axioms candidate_main_from_backward151
run_cmd do
  for target in [``candidate_main151, ``positive_lower_density151,
      ``candidate_main_from_backward151, ``positive_lower_density_from_backward151] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
end Erdos374.AnalyticClosure151

end Update151_Component_30
/- END COMPONENT: Erdos374_AnalyticClosure151.lean -/

/- BEGIN COMPONENT: FourierCandidate151.lean -/
section Update151_Component_31



namespace Erdos374.AnalyticClosure151

/-- The candidate's remaining inputs are now the backward real exceptional-set
estimate and the explicitly finite nonzero-character estimate. -/
theorem candidate_main_from_backward_and_finite_characters151
    (HF : HarmanAnalytic151Orientation.RealBackwardExceptionalMeasure151)
    (HS : FourierSampling151.FiniteNonzeroCharacterSampling) : MainStatement :=
  candidate_main_from_backward151 HF
    (FourierSampling151.polynomial_sampling_of_finite_nonzero HS)

theorem positive_lower_density_from_backward_and_finite_characters151
    (HF : HarmanAnalytic151Orientation.RealBackwardExceptionalMeasure151)
    (HS : FourierSampling151.FiniteNonzeroCharacterSampling) : PositiveLowerDensity D6 :=
  positive_lower_density_from_backward151 HF
    (FourierSampling151.polynomial_sampling_of_finite_nonzero HS)

#print axioms candidate_main_from_backward_and_finite_characters151
#print axioms positive_lower_density_from_backward_and_finite_characters151

run_cmd do
  for target in [``candidate_main_from_backward_and_finite_characters151,
      ``positive_lower_density_from_backward_and_finite_characters151] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.AnalyticClosure151

end Update151_Component_31
/- END COMPONENT: FourierCandidate151.lean -/

/- BEGIN COMPONENT: FourierLargePhase151.lean -/
section Update151_Component_32




/-! The unconditional small-phase theorem removes that regime from the final
oscillatory obligation. The large-phase estimate below remains unproved. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators

namespace Erdos374.FourierLargePhase151
open FourierSampling151 ReciprocalCharacter151 SamplingClosure147

/-- Only large phase variation remains. The splitting exponent B may depend on
gamma, but must be fixed before P,b and the Fourier frequency. -/
def LargePhaseCharacterSampling : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ P b : ℕ,
    P₀ ≤ P → 2 ≤ P → 1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) →
    ∀ n m : ℤ, 0 < n.natAbs + m.natAbs →
      n.natAbs + m.natAbs ≤ ⌈(Real.log (P : ℝ)) ^ 6⌉₊ →
      (Real.log (P : ℝ)) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
      ‖characterDiscrepancy P b n m‖ ≤ C * (P : ℝ) / (Real.log (P : ℝ)) ^ 6

theorem curveCharacter_eq_character (b : ℝ) (n m : ℤ) (t : ℝ) :
    curveCharacter b n m t = character ((n : ℝ) * b) ((m : ℝ) * b) t := by
  rw [curveCharacter_eq_exp]
  rfl

theorem finite_nonzero_of_large_phase (HL : LargePhaseCharacterSampling) :
    FiniteNonzeroCharacterSampling := by
  intro γ hγ
  obtain ⟨B, C, hC, N, hN⟩ := HL γ hγ
  obtain ⟨NS, hNS⟩ := ReciprocalSamplingSmall151.small_phase_sampling 6 B
  refine ⟨max C (6 + 4 * Real.pi), lt_of_lt_of_le hC (le_max_left _ _), max N NS, ?_⟩
  intro P b hP hP2 hb hPb n m hnm hfreq
  have hPN : N ≤ P := (le_max_left _ _).trans hP
  have hPS : NS ≤ P := (le_max_right _ _).trans hP
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hL0 : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  by_cases hsmall : amplitude ((n : ℝ) * b) ((m : ℝ) * b) P ≤ (Real.log (P : ℝ)) ^ B
  · have hs := hNS P hPS ((n : ℝ) * b) ((m : ℝ) * b) hsmall
    have heq : characterDiscrepancy P b n m =
        (∑ p ∈ openPrimeBand P, character ((n : ℝ) * b) ((m : ℝ) * b) (p : ℝ)) -
          ∫ t in (P : ℝ)..(2 * (P : ℝ)),
            character ((n : ℝ) * b) ((m : ℝ) * b) t / (Real.log t : ℂ) := by
      simp only [characterDiscrepancy, curveCharacter_eq_character]
    rw [heq]
    apply hs.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hP0) (by positivity)
  · apply (hN P b hPN hP2 hb hPb n m hnm hfreq (lt_of_not_ge hsmall)).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0) (by positivity)

theorem polynomial_sampling_of_large_phase (HL : LargePhaseCharacterSampling) :
    SamplingPolynomial149.PolynomialReciprocalPrimeSampling :=
  polynomial_sampling_of_finite_nonzero (finite_nonzero_of_large_phase HL)

theorem candidate_main_from_large_phase151
    (HF : HarmanAnalytic151Orientation.RealBackwardExceptionalMeasure151)
    (HL : LargePhaseCharacterSampling) : MainStatement :=
  AnalyticClosure151.candidate_main_from_backward151 HF (polynomial_sampling_of_large_phase HL)

theorem positive_lower_density_from_large_phase151
    (HF : HarmanAnalytic151Orientation.RealBackwardExceptionalMeasure151)
    (HL : LargePhaseCharacterSampling) : PositiveLowerDensity D6 :=
  AnalyticClosure151.positive_lower_density_from_backward151 HF (polynomial_sampling_of_large_phase HL)

#check candidate_main_from_large_phase151
#print axioms polynomial_sampling_of_large_phase
#print axioms candidate_main_from_large_phase151
run_cmd do
  for target in [``curveCharacter_eq_character, ``finite_nonzero_of_large_phase,
      ``polynomial_sampling_of_large_phase, ``candidate_main_from_large_phase151,
      ``positive_lower_density_from_large_phase151] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.FourierLargePhase151
end

end Update151_Component_32
/- END COMPONENT: FourierLargePhase151.lean -/

/- BEGIN COMPONENT: Erdos374_SourceBoundary151.lean -/
section Update151_Component_33



/-! The narrowest current source-facing candidate endpoint. Both analytic
estimates remain explicit hypotheses. This is not an unconditional main proof. -/
namespace Erdos374.SourceBoundary151

theorem candidate_main151
    (HF : HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151)
    (HL : FourierLargePhase151.LargePhaseCharacterSampling) : MainStatement :=
  FourierLargePhase151.candidate_main_from_large_phase151
    (HarmanDyadic151.backward_prefix_from_dyadic151 HF) HL

theorem positive_lower_density151
    (HF : HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151)
    (HL : FourierLargePhase151.LargePhaseCharacterSampling) : PositiveLowerDensity D6 :=
  FourierLargePhase151.positive_lower_density_from_large_phase151
    (HarmanDyadic151.backward_prefix_from_dyadic151 HF) HL

#check candidate_main151
#check positive_lower_density151
#print axioms candidate_main151
#print axioms positive_lower_density151
run_cmd do
  for target in [``candidate_main151, ``positive_lower_density151] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.SourceBoundary151

end Update151_Component_33
/- END COMPONENT: Erdos374_SourceBoundary151.lean -/

#check Erdos374.SourceBoundary151.candidate_main151
#print axioms Erdos374.SourceBoundary151.candidate_main151
#print axioms Erdos374.SourceBoundary151.positive_lower_density151
#check Erdos374.AnalyticClosure151.candidate_main151
#check Erdos374.AnalyticClosure151.candidate_main_from_backward151
#print axioms Erdos374.AnalyticClosure151.candidate_main151
#print axioms Erdos374.AnalyticClosure151.candidate_main_from_backward151
run_cmd do
  for target in [``Erdos374.SourceBoundary151.candidate_main151,
      ``Erdos374.SourceBoundary151.positive_lower_density151,
      ``Erdos374.FourierLargePhase151.polynomial_sampling_of_large_phase,
      ``Erdos374.FourierSampling151.polynomial_sampling_of_finite_nonzero,
      ``Erdos374.AnalyticClosure151.candidate_main151,
      ``Erdos374.AnalyticClosure151.positive_lower_density151,
      ``Erdos374.AnalyticClosure151.candidate_main_from_backward151,
      ``Erdos374.SmoothSamplingSmall151.smooth_small_sampling_real,
      ``Erdos374.MangoldtToPrimes151.prime_sum_of_mangoldt_prefix_bound,
      ``Erdos374.KusminLandau151.kusmin_landau_integer,
      ``Erdos374.SecondDerivativeOptimized151.second_difference_optimized,
      ``Erdos374.ReciprocalIntegral151.positive_character_integral,
      ``Erdos374.HarmanAnalytic151Orientation.real_forward_from_backward151] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "UPDATE 151 FINAL AXIOM AUDIT PASSED: analytic prerequisites proved; TWO main analytic premises remain"

end Update152_Component_1
/- END COMPONENT: Erdos374_Update151.lean -/

/- BEGIN COMPONENT: VaughanBilinear152.lean -/
section Update152_Component_2



/-! Exact weighted Type I/II sum forms for the actual Vaughan decomposition. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace Erdos374.VaughanBilinear152
open Vaughan145

theorem weighted_convolution_pairs (f g : ArithmeticFunction ℝ) (P M : ℕ) (w : ℕ → ℂ) :
    phaseSum (Finset.Ioc P M) w (f * g) =
      ∑ x ∈ (Finset.Ioc 0 M ×ˢ Finset.Ioc 0 M) with P < x.1 * x.2 ∧ x.1 * x.2 ≤ M,
        (f x.1 : ℂ) * (g x.2 : ℂ) * w (x.1 * x.2) := by
  classical
  unfold phaseSum
  simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  trans ∑ n ∈ Finset.Ioc P M,
    ∑ x ∈ (Finset.Ioc 0 M ×ˢ Finset.Ioc 0 M) with x.1 * x.2 = n,
      (f x.1 : ℂ) * (g x.2 : ℂ) * w (x.1 * x.2)
  · apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (show n ≠ 0 by omega) hn'.2]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  · simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp [Finset.mem_Ioc]

theorem inner_product_filter (P M d : ℕ) (hd : 0 < d) :
    {k ∈ Finset.Ioc 0 M | P < d * k ∧ d * k ≤ M} =
      Finset.Ioc (P / d) (M / d) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · intro ⟨⟨_, _⟩, hlow, hhigh⟩
    exact ⟨(Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [Nat.mul_comm] using hlow),
      (Nat.le_div_iff_mul_le hd).mpr (by simpa only [Nat.mul_comm] using hhigh)⟩
  · intro ⟨hlow, hhigh⟩
    refine ⟨⟨(Nat.zero_le _).trans_lt hlow, hhigh.trans (Nat.div_le_self M d)⟩, ?_, ?_⟩
    · simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hlow
    · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hhigh

theorem weighted_convolution_sum (f g : ArithmeticFunction ℝ) (P M : ℕ) (w : ℕ → ℂ) :
    phaseSum (Finset.Ioc P M) w (f * g) =
      ∑ d ∈ Finset.Ioc 0 M, (f d : ℂ) *
        ∑ k ∈ Finset.Ioc (P / d) (M / d), (g k : ℂ) * w (d * k) := by
  classical
  rw [weighted_convolution_pairs, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter, inner_product_filter P M d (Finset.mem_Ioc.mp hd).1,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A norm estimate with the actual inner sums retained, ready for phase cancellation. -/
theorem weighted_convolution_norm_le (f g : ArithmeticFunction ℝ) (P M : ℕ) (w : ℕ → ℂ) :
    ‖phaseSum (Finset.Ioc P M) w (f * g)‖ ≤
      ∑ d ∈ Finset.Ioc 0 M, |f d| *
        ‖∑ k ∈ Finset.Ioc (P / d) (M / d), (g k : ℂ) * w (d * k)‖ := by
  rw [weighted_convolution_sum]
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    norm_sum_le (Finset.Ioc 0 M)
      (fun d => (f d : ℂ) * ∑ k ∈ Finset.Ioc (P / d) (M / d), (g k : ℂ) * w (d * k))

/-- The first Type I term only uses outer indices at most U. -/
theorem typeI_low_sum (U P M : ℕ) (g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    phaseSum (Finset.Ioc P M) w (low U muR * g) =
      ∑ d ∈ Finset.Ioc 0 (min U M), (muR d : ℂ) *
        ∑ k ∈ Finset.Ioc (P / d) (M / d), (g k : ℂ) * w (d * k) := by
  classical
  rw [weighted_convolution_sum]
  simp only [low_apply, apply_ite, Complex.ofReal_zero, ite_mul, zero_mul,
    ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d; simp only [Finset.mem_filter, Finset.mem_Ioc, le_min_iff]; omega
  · intro d _; rfl

/-- All three surviving Vaughan terms are exact bilinear sums on the truncated band. -/
theorem vaughan_bilinear_identity (U V P M : ℕ) (w : ℕ → ℂ) (hV : V ≤ P) :
    phaseSum (Finset.Ioc P M) w lam =
      (∑ d ∈ Finset.Ioc 0 (min U M), (muR d : ℂ) *
        ∑ k ∈ Finset.Ioc (P / d) (M / d), (Real.log (k : ℝ) : ℂ) * w (d * k)) -
      (∑ d ∈ Finset.Ioc 0 M, (Vaughan145.alpha U V d : ℂ) *
        ∑ k ∈ Finset.Ioc (P / d) (M / d), (zetaR k : ℂ) * w (d * k)) +
      (∑ d ∈ Finset.Ioc 0 M, (high U muR d : ℂ) *
        ∑ k ∈ Finset.Ioc (P / d) (M / d), (beta V k : ℂ) * w (d * k)) := by
  rw [phaseSum_vaughan_above U V _ w (by intro n hn; exact hV.trans_lt (Finset.mem_Ioc.mp hn).1),
    typeI_low_sum, weighted_convolution_sum, weighted_convolution_sum]
  rfl

#print axioms weighted_convolution_sum
#print axioms vaughan_bilinear_identity
run_cmd do
  for target in [``weighted_convolution_pairs, ``inner_product_filter,
      ``weighted_convolution_sum, ``weighted_convolution_norm_le,
      ``typeI_low_sum, ``vaughan_bilinear_identity] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.VaughanBilinear152
end

end Update152_Component_2
/- END COMPONENT: VaughanBilinear152.lean -/

/- BEGIN COMPONENT: BilinearCorrelation152.lean -/
section Update152_Component_3




/-! Finite bilinear Cauchy–Schwarz, with the actual hyperbolic truncations.
The diagonal is retained. No cancellation estimate is postulated here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.BilinearCorrelation152
open ReciprocalCharacter151

theorem weighted_cauchy {ι : Type*} (s : Finset ι) (a z : ι → ℂ) :
    ‖∑ d ∈ s, a d * z d‖ ^ 2 ≤
      (∑ d ∈ s, ‖a d‖ ^ 2) * (∑ d ∈ s, ‖z d‖ ^ 2) := by
  have h := norm_sum_le s (fun d => a d * z d)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun d => ‖a d‖) (fun d => ‖z d‖))

theorem bilinear_energy {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (b : κ → ℂ) (z : ι → κ → ℂ) :
    (∑ d ∈ s, ‖∑ k ∈ t, b k * z d k‖ ^ 2) =
      ∑ k ∈ t, ∑ l ∈ t,
        (b k * conj (b l) * (∑ d ∈ s, z d k * conj (z d l))).re := by
  simp_rw [ExponentialSum151.norm_sum_sq_eq_correlations]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finset.mul_sum, Complex.re_sum, map_mul]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  ring

theorem bilinear_correlation_bound {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (z : ι → κ → ℂ) :
    ‖∑ d ∈ s, a d * ∑ k ∈ t, b k * z d k‖ ^ 2 ≤
      (∑ d ∈ s, ‖a d‖ ^ 2) *
        ∑ k ∈ t, ∑ l ∈ t, ‖b k‖ * ‖b l‖ * ‖∑ d ∈ s, z d k * conj (z d l)‖ := by
  apply (weighted_cauchy s a (fun d => ∑ k ∈ t, b k * z d k)).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [bilinear_energy]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  simpa only [norm_mul, Complex.norm_conj] using
    Complex.re_le_norm (b k * conj (b l) * (∑ d ∈ s, z d k * conj (z d l)))

theorem character_mul_conj (u v u' v' t : ℝ) :
    character u v t * conj (character u' v' t) = character (u - u') (v - v') t := by
  unfold character
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [← sub_eq_add_neg, ← sub_mul, ← Complex.ofReal_sub]
  congr 2
  unfold phase
  ring

theorem character_dilation (u v d t : ℝ) :
    character u v (d * t) = character (u / d) (v / d ^ 2) t := by
  unfold character phase
  congr 3
  simp only [mul_pow, div_mul_eq_div_div]

theorem dilated_character_correlation (u v d k l : ℝ) :
    character u v (d * k) * conj (character u v (d * l)) =
      character (u * (1 / k - 1 / l)) (v * (1 / k ^ 2 - 1 / l ^ 2)) d := by
  rw [mul_comm d k, mul_comm d l, character_dilation, character_dilation,
    character_mul_conj]
  congr 1 <;> ring

/-- Zero extension carries exactly the hyperbolic interval endpoints. -/
def bandCharacter (P M : ℕ) (u v : ℝ) (d k : ℕ) : ℂ :=
  if P < d * k ∧ d * k ≤ M then character u v ((d : ℝ) * k) else 0

theorem band_correlation (s : Finset ℕ) (P M k l : ℕ) (u v : ℝ) :
    (∑ d ∈ s, bandCharacter P M u v d k * conj (bandCharacter P M u v d l)) =
      ∑ d ∈ s with (P < d * k ∧ d * k ≤ M) ∧ (P < d * l ∧ d * l ≤ M),
        character (u * (1 / (k : ℝ) - 1 / (l : ℝ)))
          (v * (1 / (k : ℝ) ^ 2 - 1 / (l : ℝ) ^ 2)) d := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hk : P < d * k ∧ d * k ≤ M
  · by_cases hl : P < d * l ∧ d * l ≤ M
    · simp only [bandCharacter, hk, hl, ↓reduceIte, and_self]
      exact dilated_character_correlation u v d k l
    · simp [bandCharacter, hk, hl]
  · simp [bandCharacter, hk]

theorem band_diagonal (s : Finset ℕ) (P M k : ℕ) (u v : ℝ) :
    (∑ d ∈ s, bandCharacter P M u v d k * conj (bandCharacter P M u v d k)) =
      ((s.filter (fun d => P < d * k ∧ d * k ≤ M)).card : ℂ) := by
  rw [band_correlation]
  simp [character, phase]

theorem band_intersection (s : Finset ℕ) (P M k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (s.filter (fun d => (P < d * k ∧ d * k ≤ M) ∧ (P < d * l ∧ d * l ≤ M))) =
      s ∩ Finset.Ioc (max (P / k) (P / l)) (min (M / k) (M / l)) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_Ioc,
    max_lt_iff, le_min_iff, Nat.div_lt_iff_lt_mul hk, Nat.div_lt_iff_lt_mul hl,
    Nat.le_div_iff_mul_le hk, Nat.le_div_iff_mul_le hl]
  tauto

/-- The Type II diagonal is explicit and has not been discarded as an
oscillatory term. Off-diagonal correlations have their original endpoints. -/
theorem band_bilinear_bound (s t : Finset ℕ) (P M : ℕ) (u v : ℝ)
    (a b : ℕ → ℂ) :
    ‖∑ d ∈ s, a d * ∑ k ∈ t, b k * bandCharacter P M u v d k‖ ^ 2 ≤
      (∑ d ∈ s, ‖a d‖ ^ 2) *
        ((∑ k ∈ t, ‖b k‖ ^ 2 * ((s.filter (fun d => P < d * k ∧ d * k ≤ M)).card : ℝ)) +
          ∑ k ∈ t, ∑ l ∈ t.erase k, ‖b k‖ * ‖b l‖ *
            ‖∑ d ∈ s, bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖) := by
  classical
  apply (bilinear_correlation_bound s t a b (bandCharacter P M u v)).trans
  apply le_of_eq
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.add_sum_erase t (fun l => ‖b k‖ * ‖b l‖ *
    ‖∑ d ∈ s, bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖) hk]
  rw [band_diagonal, Complex.norm_natCast]
  ring

#print axioms bilinear_correlation_bound
#print axioms band_correlation
run_cmd do
  for target in [``weighted_cauchy, ``bilinear_energy, ``bilinear_correlation_bound,
      ``character_mul_conj, ``character_dilation, ``dilated_character_correlation,
      ``band_correlation, ``band_diagonal, ``band_intersection, ``band_bilinear_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.BilinearCorrelation152
end

end Update152_Component_3
/- END COMPONENT: BilinearCorrelation152.lean -/

/- BEGIN COMPONENT: ReciprocalPhaseShape152.lean -/
section Update152_Component_4




/-! Actual reciprocal-phase shape estimates. No exponential-sum estimate is
postulated here; all phase-shape hypotheses in the exported results are explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
open scoped BigOperators ContDiff

namespace Erdos374.ReciprocalPhaseShape152
open ReciprocalPhase147 SecondDerivative151

theorem affine_dominance (u v c t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hdom : 2 * c * |v| ≤ |u| * t) :
    |u| * t / 2 ≤ |u * t + c * v| := by
  have htri : |u * t| ≤ |u * t + c * v| + |c * v| := by
    simpa only [add_neg_cancel_right, abs_neg] using abs_add_le (u * t + c * v) (-(c * v))
  rw [abs_mul, abs_of_nonneg ht, abs_mul, abs_of_nonneg hc] at htri
  linarith

/-- Every retained integer frequency off the square axis is uniformly far
from the zero of the j-th derivative on a sufficiently late band. -/
theorem integer_numerator_dominance (j : ℕ) (n m : ℤ) (H P t : ℝ)
    (hn : n ≠ 0) (hm : |(m : ℝ)| ≤ H)
    (hP : 2 * ((j + 1 : ℕ) : ℝ) * H ≤ P) (ht : P ≤ t) :
    |(n : ℝ)| * t / 2 ≤ |(n : ℝ) * t + ((j + 1 : ℕ) : ℝ) * (m : ℝ)| := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hH : 0 ≤ H := (abs_nonneg _).trans hm
  have ht0 : 0 ≤ t := (by positivity : 0 ≤ 2 * ((j + 1 : ℕ) : ℝ) * H).trans (hP.trans ht)
  apply affine_dominance _ _ _ _ (by positivity) ht0
  calc
    _ ≤ 2 * ((j + 1 : ℕ) : ℝ) * H := mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ t := hP.trans ht
    _ ≤ |(n : ℝ)| * t := by nlinarith

theorem affine_abs_upper (u v c t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hdom : 2 * c * |v| ≤ |u| * t) :
    |u * t + c * v| ≤ 3 * |u| * t / 2 := by
  have h := abs_add_le (u * t) (c * v)
  rw [abs_mul, abs_of_nonneg ht, abs_mul, abs_of_nonneg hc] at h
  linarith

theorem normalized_bounds (j : ℕ) (u v t : ℝ) (ht : 0 < t)
    (hdom : 2 * ((j + 1 : ℕ) : ℝ) * |v| ≤ |u| * t) :
    |u| / 2 ≤ |normalized j u v t| ∧ |normalized j u v t| ≤ 3 * |u| / 2 := by
  have heq : normalized j u v t = (u * t + ((j + 1 : ℕ) : ℝ) * v) / t := by
    unfold normalized
    field_simp
  rw [heq, abs_div, abs_of_pos ht]
  constructor
  · apply (le_div_iff₀ ht).mpr
    convert affine_dominance u v ((j + 1 : ℕ) : ℝ) t (by positivity) ht.le hdom using 1 <;> ring
  · apply (div_le_iff₀ ht).mpr
    convert affine_abs_upper u v ((j + 1 : ℕ) : ℝ) t (by positivity) ht.le hdom using 1 <;> ring

/-- Two-sided derivative bounds with the exact factorial and power scaling. -/
theorem iteratedDeriv_bounds (j : ℕ) (u v t : ℝ) (ht : 0 < t)
    (hdom : 2 * ((j + 1 : ℕ) : ℝ) * |v| ≤ |u| * t) :
    (j.factorial : ℝ) * |u| / (2 * t ^ (j + 1)) ≤ |iteratedDeriv j (phase u v) t| ∧
      |iteratedDeriv j (phase u v) t| ≤ 3 * (j.factorial : ℝ) * |u| / (2 * t ^ (j + 1)) := by
  rw [iteratedDeriv_phase j u v ht.ne', derivativeFormula_factor j u v t ht.ne']
  simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg j.factorial : (0 : ℝ) ≤ j.factorial), abs_of_pos ht]
  have h := normalized_bounds j u v t ht hdom
  constructor
  · convert mul_le_mul_of_nonneg_left h.1 (by positivity : 0 ≤ (j.factorial : ℝ) / t ^ (j + 1)) using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (j.factorial : ℝ) / t ^ (j + 1)) using 1 <;> ring

def realIncrement (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + 1) - f x

theorem realIncrement_hasDerivAt {f g : ℝ → ℝ} {a x : ℝ}
    (hd : ∀ t ∈ Ici a, HasDerivAt f (g t) t) (hx : a ≤ x) :
    HasDerivAt (realIncrement f) (realIncrement g x) x := by
  have h1 := (hd (x + 1) (by change a ≤ x + 1; linarith)).comp x
    ((hasDerivAt_id x).add_const 1)
  change HasDerivAt (fun t : ℝ => f (t + 1) - f t) (g (x + 1) - g x) x
  convert h1.sub (hd x hx) using 1 <;> simp
  funext t
  rfl

theorem realIncrement_antitone_of_deriv_antitone {f g : ℝ → ℝ} {a : ℝ}
    (hd : ∀ t ∈ Ici a, HasDerivAt f (g t) t) (hg : AntitoneOn g (Ici a)) :
    AntitoneOn (realIncrement f) (Ici a) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici a)
  · intro x hx
    exact (realIncrement_hasDerivAt hd hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (realIncrement_hasDerivAt hd (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxa : a ≤ x := interior_subset hx
    rw [(realIncrement_hasDerivAt hd hxa).deriv]
    exact sub_nonpos.mpr (hg hxa (by change a ≤ x + 1; linarith) (by linarith))

theorem realSecondDifference_antitone {f g h : ℝ → ℝ} {a : ℝ}
    (hd : ∀ t ∈ Ici a, HasDerivAt f (g t) t)
    (hd' : ∀ t ∈ Ici a, HasDerivAt g (h t) t) (hh : AntitoneOn h (Ici a)) :
    AntitoneOn (realIncrement (realIncrement f)) (Ici a) :=
  realIncrement_antitone_of_deriv_antitone
    (fun _ hx => realIncrement_hasDerivAt hd hx)
    (realIncrement_antitone_of_deriv_antitone hd' hh)

/-- A unit second difference equals an actual second derivative at some point
of its two-unit supporting interval. -/
theorem exists_realSecondDifference_eq {f g h : ℝ → ℝ} {a x : ℝ}
    (hd : ∀ t ∈ Ici a, HasDerivAt f (g t) t)
    (hd' : ∀ t ∈ Ici a, HasDerivAt g (h t) t) (hx : a ≤ x) :
    ∃ z ∈ Ioo x (x + 2), realIncrement (realIncrement f) x = h z := by
  obtain ⟨y, hy, hey⟩ := exists_hasDerivAt_eq_slope (realIncrement f) (realIncrement g)
    (show x < x + 1 by linarith)
    (fun t ht => (realIncrement_hasDerivAt hd (hx.trans ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => realIncrement_hasDerivAt hd (hx.trans ht.1.le))
  have hy' : a ≤ y := hx.trans hy.1.le
  obtain ⟨z, hz, hez⟩ := exists_hasDerivAt_eq_slope g h
    (show y < y + 1 by linarith)
    (fun t ht => (hd' t (hy'.trans ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => hd' t (hy'.trans ht.1.le))
  refine ⟨z, ⟨by linarith [hz.1, hy.1], by linarith [hz.2, hy.2]⟩, ?_⟩
  simp only [show x + 1 - x = 1 by ring, show y + 1 - y = 1 by ring, div_one] at hey hez
  exact hey.symm.trans hez.symm

theorem normalized_signed_bounds (j : ℕ) (u v t : ℝ) (ht : 0 < t)
    (hdom : 2 * ((j + 1 : ℕ) : ℝ) * |v| ≤ u * t) :
    u / 2 ≤ normalized j u v t ∧ normalized j u v t ≤ 3 * u / 2 := by
  have hb : |((j + 1 : ℕ) : ℝ) * v / t| ≤ u / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j + 1 : ℕ)), abs_of_pos ht]
    apply (div_le_iff₀ ht).mpr
    linarith
  unfold normalized
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

theorem normalized_nonneg (j : ℕ) (u v t : ℝ) (ht : 0 < t)
    (hdom : ((j + 1 : ℕ) : ℝ) * |v| ≤ u * t) : 0 ≤ normalized j u v t := by
  have heq : normalized j u v t = (u * t + ((j + 1 : ℕ) : ℝ) * v) / t := by
    unfold normalized
    field_simp
  rw [heq]
  apply div_nonneg _ ht.le
  have hv := mul_le_mul_of_nonneg_left (neg_abs_le v)
    (by positivity : (0 : ℝ) ≤ (j + 1 : ℕ))
  linarith

theorem phase_hasDerivAt (u v t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (phase u v) (derivativeFormula 1 u v t) t := by
  have heq : derivativeFormula 0 u v = phase u v := by
    funext x
    simp [derivativeFormula, phase]
  rw [← heq]
  exact derivativeFormula_hasDerivAt 0 u v t ht

theorem secondDerivative_bounds (a u v t : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (ht : a ≤ t) (hdom : 6 * |v| ≤ u * a) :
    u / t ^ 3 ≤ derivativeFormula 2 u v t ∧ derivativeFormula 2 u v t ≤ 3 * u / t ^ 3 := by
  have ht0 : 0 < t := ha.trans_le ht
  have hdomt : 6 * |v| ≤ u * t := hdom.trans (mul_le_mul_of_nonneg_left ht hu)
  have hnorm := normalized_signed_bounds 2 u v t ht0 (by norm_num; exact hdomt)
  rw [derivativeFormula_factor 2 u v t ht0.ne']
  norm_num only [even_two, Even.neg_pow, one_pow, Nat.factorial, Nat.cast_ofNat, one_mul]
  constructor
  · convert mul_le_mul_of_nonneg_left hnorm.1 (by positivity : 0 ≤ (2 : ℝ) / t ^ 3) using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hnorm.2 (by positivity : 0 ≤ (2 : ℝ) / t ^ 3) using 1 <;> ring

theorem thirdDerivative_nonpos (a u v t : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (ht : a ≤ t) (hdom : 6 * |v| ≤ u * a) : derivativeFormula 3 u v t ≤ 0 := by
  have ht0 : 0 < t := ha.trans_le ht
  have hdomt : 6 * |v| ≤ u * t := hdom.trans (mul_le_mul_of_nonneg_left ht hu)
  have hn : 0 ≤ normalized 3 u v t :=
    normalized_nonneg 3 u v t ht0 (by norm_num; linarith [abs_nonneg v])
  rw [derivativeFormula_factor 3 u v t ht0.ne']
  apply mul_nonpos_of_nonpos_of_nonneg _ hn
  apply div_nonpos_of_nonpos_of_nonneg
  · norm_num
  · positivity

theorem secondDerivative_antitone (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 6 * |v| ≤ u * a) : AntitoneOn (derivativeFormula 2 u v) (Ici a) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici a)
  · intro t ht
    exact (derivativeFormula_hasDerivAt 2 u v t (ha.trans_le ht).ne').continuousAt.continuousWithinAt
  · intro t ht
    exact (derivativeFormula_hasDerivAt 2 u v t (ha.trans_le (interior_subset ht)).ne').differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(derivativeFormula_hasDerivAt 2 u v t (ha.trans_le (interior_subset ht)).ne').deriv]
    exact thirdDerivative_nonpos a u v t ha hu (interior_subset ht) hdom

def sequencePhase (a u v : ℝ) (n : ℕ) : ℝ := phase u v (a + n)

theorem secondDifference_eq_real (a u v : ℝ) (n : ℕ) :
    secondDifference (sequencePhase a u v) n =
      realIncrement (realIncrement (phase u v)) (a + n) := by
  unfold secondDifference increment sequencePhase realIncrement
  push_cast
  simp only [← add_assoc]

theorem secondDifference_antitone (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 6 * |v| ≤ u * a) : Antitone (secondDifference (sequencePhase a u v)) := by
  have hm := realSecondDifference_antitone
    (fun t ht => phase_hasDerivAt u v t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 1 u v t (ha.trans_le ht).ne')
    (secondDerivative_antitone a u v ha hu hdom)
  intro m n hmn
  rw [secondDifference_eq_real, secondDifference_eq_real]
  exact hm (by change a ≤ a + m; linarith [Nat.cast_nonneg (α := ℝ) m]) (by change a ≤ a + n; linarith [Nat.cast_nonneg (α := ℝ) n])
    (add_le_add (le_refl a) (Nat.cast_le.mpr hmn))

theorem secondDifference_bounds (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 6 * |v| ≤ u * a) (N n : ℕ) (hn : n < N) :
    u / (a + (N : ℝ) + 2) ^ 3 ≤ secondDifference (sequencePhase a u v) n ∧
      secondDifference (sequencePhase a u v) n ≤ 3 * u / a ^ 3 := by
  obtain ⟨z, hz, heq⟩ := exists_realSecondDifference_eq
    (fun t ht => phase_hasDerivAt u v t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 1 u v t (ha.trans_le ht).ne')
    (show a ≤ a + n by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [secondDifference_eq_real, heq]
  have haz : a ≤ z := by linarith [hz.1, Nat.cast_nonneg (α := ℝ) n]
  have hz0 : 0 < z := ha.trans_le haz
  have hzN : z ≤ a + (N : ℝ) + 2 := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    linarith [hz.2]
  have hb := secondDerivative_bounds a u v z ha hu haz hdom
  constructor
  · exact (div_le_div_of_nonneg_left hu (pow_pos hz0 3)
      (pow_le_pow_left₀ hz0.le hzN 3)).trans hb.1
  · exact hb.2.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos ha 3)
      (pow_le_pow_left₀ ha.le haz 3))

#print axioms integer_numerator_dominance
#print axioms iteratedDeriv_bounds
#print axioms exists_realSecondDifference_eq
#print axioms realSecondDifference_antitone
#print axioms secondDifference_bounds
#print axioms secondDifference_antitone

run_cmd do
  for target in [``integer_numerator_dominance, ``iteratedDeriv_bounds,
      ``exists_realSecondDifference_eq, ``realSecondDifference_antitone,
      ``secondDifference_bounds, ``secondDifference_antitone] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end





end Update152_Component_4
/- END COMPONENT: ReciprocalPhaseShape152.lean -/

/- BEGIN COMPONENT: ReciprocalSquareShape152.lean -/
section Update152_Component_5


set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
open scoped BigOperators ComplexConjugate

namespace Erdos374.ReciprocalPhaseShape152
open ReciprocalPhase147 SecondDerivative151

theorem square_secondDerivative (v t : ℝ) : derivativeFormula 2 0 v t = 6 * v / t ^ 4 := by
  norm_num [derivativeFormula, Nat.factorial]
  ring

theorem square_secondDerivative_antitone (a v : ℝ) (ha : 0 < a) (hv : 0 ≤ v) :
    AntitoneOn (derivativeFormula 2 0 v) (Ici a) := by
  intro x hx y hy hxy
  rw [square_secondDerivative, square_secondDerivative]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos (ha.trans_le hx) 4)
    (pow_le_pow_left₀ (ha.trans_le hx).le hxy 4)

theorem square_secondDifference_antitone (a v : ℝ) (ha : 0 < a) (hv : 0 ≤ v) :
    Antitone (secondDifference (sequencePhase a 0 v)) := by
  have hm := realSecondDifference_antitone
    (fun t ht => phase_hasDerivAt 0 v t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 1 0 v t (ha.trans_le ht).ne')
    (square_secondDerivative_antitone a v ha hv)
  intro m n hmn
  rw [secondDifference_eq_real, secondDifference_eq_real]
  exact hm (by change a ≤ a + m; linarith [Nat.cast_nonneg (α := ℝ) m])
    (by change a ≤ a + n; linarith [Nat.cast_nonneg (α := ℝ) n])
    (add_le_add (le_refl a) (Nat.cast_le.mpr hmn))

theorem square_secondDifference_bounds (a v : ℝ) (ha : 0 < a) (hv : 0 ≤ v)
    (N n : ℕ) (hn : n < N) :
    6 * v / (a + (N : ℝ) + 2) ^ 4 ≤ secondDifference (sequencePhase a 0 v) n ∧
      secondDifference (sequencePhase a 0 v) n ≤ 6 * v / a ^ 4 := by
  obtain ⟨z, hz, heq⟩ := exists_realSecondDifference_eq
    (fun t ht => phase_hasDerivAt 0 v t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 1 0 v t (ha.trans_le ht).ne')
    (show a ≤ a + n by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [secondDifference_eq_real, heq, square_secondDerivative]
  have haz : a ≤ z := by linarith [hz.1, Nat.cast_nonneg (α := ℝ) n]
  have hz0 : 0 < z := ha.trans_le haz
  have hzN : z ≤ a + (N : ℝ) + 2 := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    linarith [hz.2]
  constructor
  · exact div_le_div_of_nonneg_left (by positivity) (pow_pos hz0 4)
      (pow_le_pow_left₀ hz0.le hzN 4)
  · exact div_le_div_of_nonneg_left (by positivity) (pow_pos ha 4)
      (pow_le_pow_left₀ ha.le haz 4)

theorem sequencePhase_neg (a u v : ℝ) :
    sequencePhase a (-u) (-v) = fun n => -sequencePhase a u v n := by
  funext n
  unfold sequencePhase phase
  ring

theorem norm_sum_e_neg (N : ℕ) (f : ℕ → ℝ) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (-f n)‖ =
      ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ := by
  have he (x : ℝ) : KusminLandau151.e (-x) = conj (KusminLandau151.e x) := by
    unfold KusminLandau151.e
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  simp_rw [he]
  rw [← map_sum, Complex.norm_conj]

/-- Sign normalization preserves the actual exponential-sum norm. -/
theorem norm_sum_sequencePhase_neg (a u v : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a (-u) (-v) n)‖ =
      ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a u v n)‖ := by
  rw [sequencePhase_neg]
  exact norm_sum_e_neg N _

#print axioms square_secondDifference_bounds
#print axioms square_secondDifference_antitone
#print axioms norm_sum_sequencePhase_neg

run_cmd do
  for target in [``square_secondDifference_bounds, ``square_secondDifference_antitone,
      ``norm_sum_sequencePhase_neg] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end

end Update152_Component_5
/- END COMPONENT: ReciprocalSquareShape152.lean -/

/- BEGIN COMPONENT: ReciprocalCancellation152.lean -/
section Update152_Component_6


set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Set
open scoped BigOperators

namespace Erdos374.ReciprocalPhaseShape152
open SecondDerivative151 SecondDerivativeOptimized151

theorem interval_shape_ratio_ge_one (a K : ℝ) (ha : 0 < a) (hK : 1 ≤ K) (N r : ℕ) :
    1 ≤ K * (a + (N : ℝ) + 2) ^ r / a ^ r := by
  have he : a ≤ a + (N : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hp := pow_le_pow_left₀ ha.le he r
  apply (le_div_iff₀ (pow_pos ha r)).mpr
  have ht : 0 ≤ (a + (N : ℝ) + 2) ^ r := by positivity
  nlinarith

theorem dominant_positive_second_order (a u v : ℝ) (N : ℕ) (ha : 0 < a) (hu : 0 < u)
    (hdom : 6 * |v| ≤ u * a) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a u v n)‖ ^ 2 ≤
      32 * (3 * (a + (N : ℝ) + 2) ^ 3 / a ^ 3) * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * (u / (a + (N : ℝ) + 2) ^ 3) +
          1 / (u / (a + (N : ℝ) + 2) ^ 3)) := by
  apply second_difference_optimized N (sequencePhase a u v)
    (u / (a + (N : ℝ) + 2) ^ 3) (3 * (a + (N : ℝ) + 2) ^ 3 / a ^ 3)
    (by positivity) (interval_shape_ratio_ge_one a 3 ha (by norm_num) N 3)
  · intro n hn
    have hb := secondDifference_bounds a u v ha hu.le hdom N n hn
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    have he : a + (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  · right
    intro m _ n _ hmn
    exact secondDifference_antitone a u v ha hu.le hdom hmn

/-- Actual two-term reciprocal cancellation, with all finite-difference and
monotonicity premises discharged. Both signs of u and v are allowed. -/
theorem dominant_signed_second_order (a u v : ℝ) (N : ℕ) (ha : 0 < a) (hu : u ≠ 0)
    (hdom : 6 * |v| ≤ |u| * a) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a u v n)‖ ^ 2 ≤
      32 * (3 * (a + (N : ℝ) + 2) ^ 3 / a ^ 3) * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * (|u| / (a + (N : ℝ) + 2) ^ 3) +
          1 / (|u| / (a + (N : ℝ) + 2) ^ 3)) := by
  by_cases hpos : 0 ≤ u
  · have hu0 : 0 < u := lt_of_le_of_ne hpos hu.symm
    simpa only [abs_of_nonneg hpos] using
      dominant_positive_second_order a u v N ha hu0 (by simpa only [abs_of_nonneg hpos] using hdom)
  · have hneg : u < 0 := lt_of_not_ge hpos
    have hb := dominant_positive_second_order a (-u) (-v) N ha (by linarith)
      (by simpa only [abs_neg, abs_of_neg hneg] using hdom)
    rw [norm_sum_sequencePhase_neg] at hb
    simpa only [abs_of_neg hneg] using hb

theorem square_positive_second_order (a v : ℝ) (N : ℕ) (ha : 0 < a) (hv : 0 < v) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a 0 v n)‖ ^ 2 ≤
      32 * ((a + (N : ℝ) + 2) ^ 4 / a ^ 4) * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * (6 * v / (a + (N : ℝ) + 2) ^ 4) +
          1 / (6 * v / (a + (N : ℝ) + 2) ^ 4)) := by
  apply second_difference_optimized N (sequencePhase a 0 v)
    (6 * v / (a + (N : ℝ) + 2) ^ 4) ((a + (N : ℝ) + 2) ^ 4 / a ^ 4)
    (by positivity)
    (by simpa only [one_mul] using interval_shape_ratio_ge_one a 1 ha (by norm_num) N 4)
  · intro n hn
    have hb := square_secondDifference_bounds a v ha hv.le N n hn
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    have he : a + (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  · right
    intro m _ n _ hmn
    exact square_secondDifference_antitone a v ha hv.le hmn

/-- The pure reciprocal-square axis, including both signs of its coefficient. -/
theorem square_signed_second_order (a v : ℝ) (N : ℕ) (ha : 0 < a) (hv : v ≠ 0) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a 0 v n)‖ ^ 2 ≤
      32 * ((a + (N : ℝ) + 2) ^ 4 / a ^ 4) * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * (6 * |v| / (a + (N : ℝ) + 2) ^ 4) +
          1 / (6 * |v| / (a + (N : ℝ) + 2) ^ 4)) := by
  by_cases hpos : 0 ≤ v
  · simpa only [abs_of_nonneg hpos] using
      square_positive_second_order a v N ha (lt_of_le_of_ne hpos hv.symm)
  · have hneg : v < 0 := lt_of_not_ge hpos
    have hb := square_positive_second_order a (-v) N ha (by linarith)
    have he := norm_sum_sequencePhase_neg a 0 v N
    simp only [neg_zero] at he
    rw [he] at hb
    simpa only [abs_of_neg hneg] using hb

#print axioms dominant_signed_second_order
#print axioms square_signed_second_order

run_cmd do
  for target in [``dominant_signed_second_order, ``square_signed_second_order] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end

end Update152_Component_6
/- END COMPONENT: ReciprocalCancellation152.lean -/

/- BEGIN COMPONENT: ReciprocalBilinearShape152.lean -/
section Update152_Component_7


set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set

namespace Erdos374.ReciprocalPhaseShape152
open ReciprocalPhase147

/-- The dominance needed for a derivative test is invariant under the Type I
dilation t ↦ d*t, including the accompanying dilation of the interval start. -/
theorem dilation_dominance (u v P d K : ℝ) (hd : 0 < d)
    (hdom : K * |v| ≤ |u| * P) :
    K * |v / d ^ 2| ≤ |u / d| * (P / d) := by
  rw [abs_div, abs_div, abs_pow, abs_of_pos hd]
  convert div_le_div_of_nonneg_right hdom (sq_nonneg d) using 1 <;>
    field_simp <;> ring

/-- Exact coefficient relation after taking an off-diagonal Type II difference.
No lower bound on the difference d-e is required for this identity. -/
theorem typeII_coefficient_relation (u v d e : ℝ) (hu : u ≠ 0) :
    v * (1 / d ^ 2 - 1 / e ^ 2) =
      ((v / u) * (1 / d + 1 / e)) * (u * (1 / d - 1 / e)) := by
  have hid : 1 / d ^ 2 - 1 / e ^ 2 = (1 / d + 1 / e) * (1 / d - 1 / e) := by
    simp only [one_div, inv_pow]
    ring
  rw [hid]
  calc
    _ = ((v / u) * u) * (1 / d + 1 / e) * (1 / d - 1 / e) := by
      rw [div_mul_cancel₀ v hu]
      ring
    _ = _ := by ring

theorem typeII_coefficient_ratio (u v d e : ℝ) (hu : u ≠ 0)
    (hde : d ≠ e) :
    (v * (1 / d ^ 2 - 1 / e ^ 2)) / (u * (1 / d - 1 / e)) =
      (v / u) * (1 / d + 1 / e) := by
  have hdiff : 1 / d - 1 / e ≠ 0 := by
    apply sub_ne_zero.mpr
    simp only [one_div]
    intro h
    apply hde
    have hh := congrArg (fun x : ℝ => x⁻¹) h
    simpa only [inv_inv] using hh
  rw [typeII_coefficient_relation u v d e hu, mul_div_cancel_right₀ _ (mul_ne_zero hu hdiff)]

theorem typeII_abs_relation (u v d e : ℝ) (hu : u ≠ 0) (hd : 0 < d) (he : 0 < e) :
    |v * (1 / d ^ 2 - 1 / e ^ 2)| =
      (|v| / |u|) * (1 / d + 1 / e) * |u * (1 / d - 1 / e)| := by
  rw [typeII_coefficient_relation u v d e hu, abs_mul, abs_mul, abs_div,
    abs_of_nonneg (by positivity : 0 ≤ 1 / d + 1 / e)]

/-- Explicit sufficient shape condition for every off-diagonal Type II phase.
The sign and size of d-e are retained in the coefficients themselves. -/
theorem typeII_dominance (u v d e a K : ℝ) (hu : u ≠ 0)
    (hd : 0 < d) (he : 0 < e)
    (ha : K * (|v| / |u|) * (1 / d + 1 / e) ≤ a) :
    K * |v * (1 / d ^ 2 - 1 / e ^ 2)| ≤
      |u * (1 / d - 1 / e)| * a := by
  rw [typeII_abs_relation u v d e hu hd he]
  have h := mul_le_mul_of_nonneg_right ha (abs_nonneg (u * (1 / d - 1 / e)))
  nlinarith only [h]

theorem integer_coefficient_ratio_le (n m : ℤ) (b H : ℝ)
    (hn : n ≠ 0) (hb : b ≠ 0) (hm : |(m : ℝ)| ≤ H) :
    |(m : ℝ) * b| / |(n : ℝ) * b| ≤ H := by
  have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  rw [abs_mul, abs_mul, mul_div_mul_right _ _ (abs_ne_zero.mpr hb)]
  exact (div_le_self (abs_nonneg _) hn1).trans hm

theorem typeII_integer_dominance (n m : ℤ) (b H D d e a K : ℝ)
    (hn : n ≠ 0) (hb : b ≠ 0) (hm : |(m : ℝ)| ≤ H)
    (hD : 0 < D) (hd : D ≤ d) (he : D ≤ e) (hK : 0 ≤ K)
    (ha : 2 * K * H / D ≤ a) :
    K * |((m : ℝ) * b) * (1 / d ^ 2 - 1 / e ^ 2)| ≤
      |((n : ℝ) * b) * (1 / d - 1 / e)| * a := by
  apply typeII_dominance _ _ _ _ _ _ (mul_ne_zero (Int.cast_ne_zero.mpr hn) hb)
    (hD.trans_le hd) (hD.trans_le he)
  have hH : 0 ≤ H := (abs_nonneg _).trans hm
  have hr := integer_coefficient_ratio_le n m b H hn hb hm
  have hd' : 1 / d ≤ 1 / D := one_div_le_one_div_of_le hD hd
  have he' : 1 / e ≤ 1 / D := one_div_le_one_div_of_le hD he
  have hdpos : 0 < d := hD.trans_le hd
  have hepos : 0 < e := hD.trans_le he
  have hs : 0 ≤ 1 / d + 1 / e := by positivity
  calc
    _ ≤ K * H * (1 / D + 1 / D) := by
      gcongr
    _ = 2 * K * H / D := by ring
    _ ≤ a := ha

#print axioms dilation_dominance
#print axioms typeII_coefficient_ratio
#print axioms typeII_integer_dominance

run_cmd do
  for target in [``dilation_dominance, ``typeII_coefficient_relation,
      ``typeII_coefficient_ratio, ``typeII_abs_relation, ``typeII_dominance,
      ``integer_coefficient_ratio_le, ``typeII_integer_dominance] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end


end Update152_Component_7
/- END COMPONENT: ReciprocalBilinearShape152.lean -/

/- BEGIN COMPONENT: BilinearCancellation152.lean -/
section Update152_Component_8




/-! Actual truncated Type II correlations bounded by the proved reciprocal
second-difference test. The shape hypotheses below are numerical inequalities,
not assumptions that an exponential sum cancels. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.BilinearCancellation152
open ReciprocalCharacter151 BilinearCorrelation152

theorem character_Ioc_eq (A B : ℕ) (u v : ℝ) :
    (∑ d ∈ Finset.Ioc A B, character u v d) =
      ∑ n ∈ Finset.range (B - A),
        KusminLandau151.e (ReciprocalPhaseShape152.sequencePhase ((A : ℝ) + 1) u v n) := by
  have hset : Finset.Ioc A B = Finset.Ico (A + 1) (B + 1) := by
    ext d; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_add_right]
  apply Finset.sum_congr rfl
  intro n hn
  unfold character KusminLandau151.e ReciprocalPhaseShape152.sequencePhase
    ReciprocalPhase147.phase phase
  push_cast
  congr 3 <;> ring

def intervalSecondBound (A B : ℕ) (u : ℝ) : ℝ :=
  let a := (A : ℝ) + 1
  let N := (B - A : ℕ)
  Real.sqrt (32 * (3 * (a + (N : ℝ) + 2) ^ 3 / a ^ 3) *
    (1 + Real.log ((N : ℝ) + 1)) *
      ((N : ℝ) ^ 2 * (|u| / (a + (N : ℝ) + 2) ^ 3) +
        1 / (|u| / (a + (N : ℝ) + 2) ^ 3)))

theorem interval_character_bound (A B : ℕ) (u v : ℝ) (hu : u ≠ 0)
    (hdom : 6 * |v| ≤ |u| * ((A : ℝ) + 1)) :
    ‖∑ d ∈ Finset.Ioc A B, character u v d‖ ≤ intervalSecondBound A B u := by
  rw [character_Ioc_eq]
  apply Real.le_sqrt_of_sq_le
  exact ReciprocalPhaseShape152.dominant_signed_second_order ((A : ℝ) + 1) u v
    (B - A) (by positivity) hu hdom

def intervalSquareBound (A B : ℕ) (v : ℝ) : ℝ :=
  let a := (A : ℝ) + 1
  let N := (B - A : ℕ)
  Real.sqrt (32 * ((a + (N : ℝ) + 2) ^ 4 / a ^ 4) *
    (1 + Real.log ((N : ℝ) + 1)) *
      ((N : ℝ) ^ 2 * (6 * |v| / (a + (N : ℝ) + 2) ^ 4) +
        1 / (6 * |v| / (a + (N : ℝ) + 2) ^ 4)))

theorem interval_character_square_bound (A B : ℕ) (v : ℝ) (hv : v ≠ 0) :
    ‖∑ d ∈ Finset.Ioc A B, character 0 v d‖ ≤ intervalSquareBound A B v := by
  rw [character_Ioc_eq]
  apply Real.le_sqrt_of_sq_le
  exact ReciprocalPhaseShape152.square_signed_second_order ((A : ℝ) + 1) v
    (B - A) (by positivity) hv

def correlationLower (D P k l : ℕ) : ℕ := max D (max (P / k) (P / l))
def correlationUpper (E M k l : ℕ) : ℕ := min E (min (M / k) (M / l))

theorem interval_band_correlation (D E P M k l : ℕ) (u v : ℝ)
    (hk : 0 < k) (hl : 0 < l) :
    (∑ d ∈ Finset.Ioc D E,
      bandCharacter P M u v d k * conj (bandCharacter P M u v d l)) =
      ∑ d ∈ Finset.Ioc (correlationLower D P k l) (correlationUpper E M k l),
        character (u * (1 / (k : ℝ) - 1 / (l : ℝ)))
          (v * (1 / (k : ℝ) ^ 2 - 1 / (l : ℝ) ^ 2)) d := by
  rw [band_correlation, band_intersection _ _ _ _ _ hk hl]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_inter, Finset.mem_Ioc, correlationLower, correlationUpper,
      max_lt_iff, le_min_iff]
    tauto
  · intro d hd; rfl

/-- Nonzero Type II differences retain both signed coefficients. -/
theorem off_diagonal_correlation_bound (D E P M k l : ℕ) (u v : ℝ)
    (hu : u ≠ 0) (hk : 0 < k) (hl : 0 < l) (hkl : k ≠ l)
    (hshape : 6 * (|v| / |u|) * (1 / (k : ℝ) + 1 / (l : ℝ)) ≤
      (correlationLower D P k l : ℝ) + 1) :
    ‖∑ d ∈ Finset.Ioc D E,
      bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖ ≤
      intervalSecondBound (correlationLower D P k l) (correlationUpper E M k l)
        (u * (1 / (k : ℝ) - 1 / (l : ℝ))) := by
  rw [interval_band_correlation _ _ _ _ _ _ _ _ hk hl]
  apply interval_character_bound
  · apply mul_ne_zero hu
    apply sub_ne_zero.mpr
    simp only [one_div, ne_eq, inv_inj, Nat.cast_inj]
    exact hkl
  · exact ReciprocalPhaseShape152.typeII_dominance u v k l _ 6 hu
      (Nat.cast_pos.mpr hk) (Nat.cast_pos.mpr hl) hshape

/-- The pure reciprocal-square Fourier axis has its own actual correlation
bound. It is not excluded by the nonzero-reciprocal-coefficient hypothesis. -/
theorem off_diagonal_square_correlation_bound (D E P M k l : ℕ) (v : ℝ)
    (hv : v ≠ 0) (hk : 0 < k) (hl : 0 < l) (hkl : k ≠ l) :
    ‖∑ d ∈ Finset.Ioc D E,
      bandCharacter P M 0 v d k * conj (bandCharacter P M 0 v d l)‖ ≤
      intervalSquareBound (correlationLower D P k l) (correlationUpper E M k l)
        (v * (1 / (k : ℝ) ^ 2 - 1 / (l : ℝ) ^ 2)) := by
  rw [interval_band_correlation _ _ _ _ _ _ _ _ hk hl]
  simp only [zero_mul]
  apply interval_character_square_bound
  apply mul_ne_zero hv
  apply sub_ne_zero.mpr
  intro h
  have he : (k : ℝ) ^ 2 = (l : ℝ) ^ 2 := inv_inj.mp (by simpa only [one_div] using h)
  have he' := (sq_eq_sq₀ (Nat.cast_nonneg k) (Nat.cast_nonneg l)).mp he
  exact hkl (Nat.cast_inj.mp he')

#print axioms interval_character_bound
#print axioms off_diagonal_correlation_bound
run_cmd do
  for target in [``character_Ioc_eq, ``interval_character_bound, ``interval_character_square_bound,
      ``interval_band_correlation, ``off_diagonal_correlation_bound,
      ``off_diagonal_square_correlation_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.BilinearCancellation152
end

end Update152_Component_8
/- END COMPONENT: BilinearCancellation152.lean -/

/- BEGIN COMPONENT: ReciprocalIntegral152.lean -/
section Update152_Component_9




/-! Signed nonstationary reciprocal phases and their weighted reference integrals. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Erdos374.ReciprocalIntegral152
open ReciprocalCharacter151 ReciprocalIntegral151

theorem phaseD_abs_eq (u v t : ℝ) (ht : 0 < t) :
    |phaseD u v t| = |u * t + 2 * v| / t ^ 3 := by
  have he : phaseD u v t = -(u * t + 2 * v) / t ^ 3 := by
    unfold phaseD
    field_simp
    <;> ring
  rw [he, abs_div, abs_neg, abs_of_pos (pow_pos ht 3)]

theorem secondMajorant_le_amplitude (u v P : ℝ) (hP : 0 < P) :
    secondMajorant u v P ≤ 6 * amplitude u v P / P ^ 2 := by
  unfold secondMajorant amplitude
  apply (le_div_iff₀ (pow_pos hP 2)).mpr
  field_simp
  nlinarith [abs_nonneg u]

/-- Dominance controls both signs; no sign condition is imposed on u or v. -/
theorem dominant_phaseD_lower (u v P t : ℝ) (hP : 0 < P)
    (hdom : 4 * |v| ≤ P * |u|) (ht : t ∈ Icc P (2 * P)) :
    amplitude u v P / (16 * P) ≤ |phaseD u v t| := by
  have ht0 : 0 < t := hP.trans_le ht.1
  have hprod : P * |u| ≤ t * |u| := mul_le_mul_of_nonneg_right ht.1 (abs_nonneg _)
  have htri : |u| * t ≤ |u * t + 2 * v| + 2 * |v| := by
    have h := abs_add_le (u * t + 2 * v) (-(2 * v))
    rw [show (u * t + 2 * v) + -(2 * v) = u * t by ring] at h
    simpa only [abs_mul, abs_of_pos ht0, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h
  have hlin : |u| * t / 2 ≤ |u * t + 2 * v| := by nlinarith
  have hF : amplitude u v P ≤ 2 * |u| / P := by
    unfold amplitude
    apply (le_div_iff₀ hP).mpr
    field_simp
    nlinarith [abs_nonneg v]
  have ht2 : 2 * t ^ 2 ≤ 8 * P ^ 2 := by
    nlinarith [pow_le_pow_left₀ ht0.le ht.2 2]
  calc
    _ ≤ (2 * |u| / P) / (16 * P) := div_le_div_of_nonneg_right hF (by positivity)
    _ = |u| / (8 * P ^ 2) := by field_simp; ring
    _ ≤ |u| / (2 * t ^ 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ht2
    _ = (|u| * t / 2) / t ^ 3 := by field_simp <;> ring
    _ ≤ |u * t + 2 * v| / t ^ 3 := div_le_div_of_nonneg_right hlin (by positivity)
    _ = _ := (phaseD_abs_eq u v t ht0).symm

theorem pure_square_phaseD_lower (v P t : ℝ) (hP : 0 < P)
    (ht : t ∈ Icc P (2 * P)) :
    amplitude 0 v P / (16 * P) ≤ |phaseD 0 v t| := by
  have ht0 : 0 < t := hP.trans_le ht.1
  have hs := positive_phaseD_lower 0 |v| P t (by norm_num) (abs_nonneg _) hP ht
  have he : |phaseD 0 v t| = |phaseD 0 |v| t| := by
    rw [phaseD_abs_eq 0 v t ht0, phaseD_abs_eq 0 |v| t ht0]
    simp only [zero_mul, zero_add, abs_mul, abs_abs]
  have ha : amplitude 0 |v| P = amplitude 0 v P := by simp [amplitude]
  rw [ha, ← he] at hs
  apply le_trans _ hs
  exact div_le_div_of_nonneg_left (amplitude_nonneg 0 v P hP.le) (by positivity) (by linarith)

theorem signed_character_prefix (u v P x : ℝ) (hP : 0 < P)
    (hx : x ∈ Icc P (2 * P)) (hF : 0 < amplitude u v P)
    (hshape : u = 0 ∨ 4 * |v| ≤ P * |u|) :
    ‖∫ t in P..x, character u v t‖ ≤ 784 * P / (Real.pi * amplitude u v P) := by
  have haway (t : ℝ) (ht : t ∈ Icc P x) :
      amplitude u v P / (16 * P) ≤ |phaseD u v t| := by
    have ht' : t ∈ Icc P (2 * P) := ⟨ht.1, ht.2.trans hx.2⟩
    rcases hshape with hu | hd
    · subst u; exact pure_square_phaseD_lower v P t hP ht'
    · exact dominant_phaseD_lower u v P t hP hd ht'
  have hη : 0 < amplitude u v P / (16 * P) := by positivity
  have hbound := norm_integral_character_le u v P x _ hP hx.1 hη haway
  have hM := secondMajorant_le_amplitude u v P hP
  calc
    _ ≤ 1 / (Real.pi * (amplitude u v P / (16 * P))) +
        (x - P) * secondMajorant u v P /
          (2 * Real.pi * (amplitude u v P / (16 * P)) ^ 2) := hbound
    _ ≤ 1 / (Real.pi * (amplitude u v P / (16 * P))) +
        P * (6 * amplitude u v P / P ^ 2) /
          (2 * Real.pi * (amplitude u v P / (16 * P)) ^ 2) := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right
        (mul_le_mul (by linarith [hx.2]) hM
          (by unfold secondMajorant; positivity) hP.le) (by positivity))
    _ = _ := by field_simp [ne_of_gt hP, ne_of_gt hF, ne_of_gt Real.pi_pos]; ring

theorem character_continuousOn_pos (u v : ℝ) : ContinuousOn (character u v) (Ioi 0) := by
  intro t ht
  exact (character_hasDerivAt u v t (ne_of_gt ht)).continuousAt.continuousWithinAt

theorem character_primitive_deriv (u v P t : ℝ) (hP : 0 < P) (hPt : P ≤ t) :
    HasDerivAt (fun x => ∫ z in P..x, character u v z) (character u v t) t := by
  have ht : 0 < t := hP.trans_le hPt
  have hc := character_continuousOn_pos u v
  have hi : IntervalIntegrable (character u v) volume P t :=
    (hc.mono (fun z hz => hP.trans_le hz.1)).intervalIntegrable_of_Icc hPt
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hc.stronglyMeasurableAtFilter isOpen_Ioi t ht)
    (character_hasDerivAt u v t (ne_of_gt ht)).continuousAt

/-- Uniform weighted reference-integral bound, covering the pure square axis
and both signs in the dominant-reciprocal regime. -/
theorem signed_character_weighted (u v P : ℝ) (hP : 1 < P)
    (hF : 0 < amplitude u v P) (hshape : u = 0 ∨ 4 * |v| ≤ P * |u|) :
    ‖∫ t in P..(2 * P), character u v t / (Real.log t : ℂ)‖ ≤
      784 * P / (Real.pi * amplitude u v P * Real.log P) := by
  have hP0 : 0 < P := by linarith
  have hPP : P ≤ 2 * P := by linarith
  have h := ContinuousLogWeightRemoval151.continuous_log_weight_removal
    (F := fun x => ∫ z in P..x, character u v z) (f := character u v)
    (R := 784 * P / (Real.pi * amplitude u v P)) hP hPP
    (fun t ht => character_primitive_deriv u v P t hP0 ht.1)
    ((character_continuousOn_pos u v).mono (fun t ht => hP0.trans_le ht.1))
    (by simp) (fun t ht => signed_character_prefix u v P t hP0 ht hF hshape)
  simpa only [div_div] using h

#print axioms signed_character_prefix
#print axioms signed_character_weighted
run_cmd do
  for target in [``dominant_phaseD_lower, ``pure_square_phaseD_lower,
      ``signed_character_prefix, ``character_primitive_deriv, ``signed_character_weighted] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalIntegral152
end

end Update152_Component_9
/- END COMPONENT: ReciprocalIntegral152.lean -/

/- BEGIN COMPONENT: FourierReferenceIntegral152.lean -/
section Update152_Component_10



/-! The large-phase reference integral for every retained signed Fourier mode. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory

namespace Erdos374.FourierReferenceIntegral152
open ReciprocalCharacter151 ReciprocalIntegral152 FourierSampling151

theorem frequency_shape (b P : ℝ) (H : ℕ) (n m : ℤ)
    (hb : 0 ≤ b) (hP : 0 ≤ P) (hH : 4 * (H : ℝ) ≤ P)
    (hm : m.natAbs ≤ H) :
    (n : ℝ) * b = 0 ∨ 4 * |(m : ℝ) * b| ≤ P * |(n : ℝ) * b| := by
  by_cases hn : n = 0
  · left; simp [hn]
  · right
    have hmR : |(m : ℝ)| ≤ H := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (Nat.cast_le.mpr hm : (m.natAbs : ℝ) ≤ H)
    have hnN : 1 ≤ n.natAbs := (Int.natAbs_pos.mpr hn)
    have hnR : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hc : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hnN
      simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_one] using
        hc
    have hlinear : 4 * |(m : ℝ)| ≤ P * |(n : ℝ)| := by nlinarith
    simpa only [abs_mul, abs_of_nonneg hb, mul_assoc] using
      mul_le_mul_of_nonneg_right hlinear hb

theorem frequency_amplitude_pos (b P : ℝ) (n m : ℤ)
    (hb : 0 < b) (hP : 0 < P) (hnm : 0 < n.natAbs + m.natAbs) :
    0 < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P := by
  unfold amplitude
  by_cases hn : n = 0
  · have hm : m ≠ 0 := by intro hm; simp [hn, hm] at hnm
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hv : 0 < |(m : ℝ) * b| := abs_pos.mpr (mul_ne_zero hmR (ne_of_gt hb))
    simpa [hn] using div_pos hv (pow_pos hP 2)
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    exact add_pos_of_pos_of_nonneg
      (div_pos (abs_pos.mpr (mul_ne_zero hnR (ne_of_gt hb))) hP) (by positivity)

/-- One uniform threshold makes every retained Fourier phase nonstationary. -/
theorem frequency_threshold :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P →
      2 ≤ P ∧ 1 ≤ Real.log (P : ℝ) ∧
        4 * (⌈(Real.log (P : ℝ)) ^ 6⌉₊ : ℝ) ≤ P := by
  obtain ⟨N, hN⟩ := RemainingAnalytic115.RemainingAnalytic141.logPower_le_sqrt_eventually141 6
  obtain ⟨NL, hNL⟩ := RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨max N (max NL 100), ?_⟩
  intro P hP
  have hP100 : 100 ≤ P := by omega
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hlog : 1 ≤ Real.log (P : ℝ) := hNL P (by omega)
  have hs := hN P (by omega)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (Real.log (P : ℝ)) ^ 6 by positivity)
  have hs10 : (10 : ℝ) ≤ Real.sqrt (P : ℝ) := by
    simpa only [show Real.sqrt (100 : ℝ) = 10 by norm_num] using
      Real.sqrt_le_sqrt (show (100 : ℝ) ≤ P by exact_mod_cast hP100)
  refine ⟨by omega, hlog, ?_⟩
  nlinarith [Real.sq_sqrt hP0, sq_nonneg (Real.sqrt (P : ℝ) - 4)]

theorem reference_integral_le (P b : ℕ) (n m : ℤ) (hP : 2 ≤ P) (hb : 1 ≤ b)
    (hnm : 0 < n.natAbs + m.natAbs)
    (hfreq : n.natAbs + m.natAbs ≤ ⌈(Real.log (P : ℝ)) ^ 6⌉₊)
    (hcut : 4 * (⌈(Real.log (P : ℝ)) ^ 6⌉₊ : ℝ) ≤ P) :
    ‖∫ t in (P : ℝ)..(2 * (P : ℝ)), curveCharacter b n m t / (Real.log t : ℂ)‖ ≤
      784 * (P : ℝ) /
        (Real.pi * amplitude ((n : ℝ) * b) ((m : ℝ) * b) P * Real.log P) := by
  have hP1 : (1 : ℝ) < P := by exact_mod_cast (show 1 < P by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hP0 : (0 : ℝ) < P := by linarith
  have h := signed_character_weighted ((n : ℝ) * b) ((m : ℝ) * b) P hP1
    (frequency_amplitude_pos b P n m hb0 hP0 hnm)
    (frequency_shape b P _ n m hb0.le hP0.le hcut (by omega))
  simpa only [FourierLargePhase151.curveCharacter_eq_character] using h

/-- The reference integral itself has the required log-saving, uniformly in
all retained signed modes; only the prime/Mangoldt sum remains to estimate. -/
theorem large_phase_reference_integral :
    ∃ P₀ : ℕ, ∀ P b : ℕ, P₀ ≤ P → 1 ≤ b → ∀ n m : ℤ,
      0 < n.natAbs + m.natAbs →
      n.natAbs + m.natAbs ≤ ⌈(Real.log (P : ℝ)) ^ 6⌉₊ →
      ∀ B : ℕ, 5 ≤ B →
      (Real.log (P : ℝ)) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
      ‖∫ t in (P : ℝ)..(2 * (P : ℝ)), curveCharacter b n m t / (Real.log t : ℂ)‖ ≤
        784 * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 := by
  obtain ⟨N, hN⟩ := frequency_threshold
  refine ⟨N, ?_⟩
  intro P b hP hb n m hnm hfreq B hB hF
  obtain ⟨hP2, hL, hcut⟩ := hN P hP
  have hL0 : 0 < Real.log (P : ℝ) := by linarith
  have hpow : (Real.log (P : ℝ)) ^ 5 ≤ (Real.log (P : ℝ)) ^ B :=
    pow_le_pow_right₀ hL hB
  have hFL : (Real.log (P : ℝ)) ^ 6 ≤
      amplitude ((n : ℝ) * b) ((m : ℝ) * b) P * Real.log P := by
    have h := mul_le_mul_of_nonneg_right (hpow.trans hF.le) hL0.le
    simpa only [show (6 : ℕ) = 5 + 1 by rfl, pow_succ] using h
  have hden : (Real.log (P : ℝ)) ^ 6 ≤
      Real.pi * amplitude ((n : ℝ) * b) ((m : ℝ) * b) P * Real.log P := by
    have hnon : 0 ≤ amplitude ((n : ℝ) * b) ((m : ℝ) * b) P * Real.log P := by
      exact (pow_nonneg hL0.le 6).trans hFL
    have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sub_nonneg.mpr hπ) hnon]
  exact (reference_integral_le P b n m hP2 hb hnm hfreq hcut).trans
    (div_le_div_of_nonneg_left (by positivity) (pow_pos hL0 6) hden)

#print axioms large_phase_reference_integral
run_cmd do
  for target in [``frequency_shape, ``frequency_amplitude_pos, ``frequency_threshold,
      ``reference_integral_le, ``large_phase_reference_integral] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.FourierReferenceIntegral152
end

end Update152_Component_10
/- END COMPONENT: FourierReferenceIntegral152.lean -/

/- BEGIN COMPONENT: HarmanGram152.lean -/
section Update152_Component_11



/-! Finite Halász–Montgomery/Gram inequalities. These contain no analytic
large-value hypothesis: the only bounds are explicit finite Gram row sums. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.HarmanGram152
open HarmanAnalytic151MeanSquare

theorem symmetric_row_bound152 {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (W : ι → ι → ℝ) (K : ℝ)
    (hW : ∀ r ∈ s, ∀ q ∈ s, 0 ≤ W r q)
    (hSym : ∀ r ∈ s, ∀ q ∈ s, W r q = W q r)
    (hRow : ∀ r ∈ s, (∑ q ∈ s, W r q) ≤ K) :
    (∑ r ∈ s, ∑ q ∈ s, u r * u q * W r q) ≤ K * ∑ r ∈ s, u r ^ 2 := by
  have h := quadratic_pair_bound151 s u W K hW hSym hRow
  have heq : (∑ r ∈ s, ∑ q ∈ s, 2 * u r * u q * W r q) =
      2 * (∑ r ∈ s, ∑ q ∈ s, u r * u q * W r q) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [heq] at h
  nlinarith

theorem finite_gram_synthesis152 {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι → E) (c : ι → ℂ) (K : ℝ)
    (hRow : ∀ r ∈ s, (∑ q ∈ s, ‖inner ℂ (v r) (v q)‖) ≤ K) :
    ‖∑ r ∈ s, c r • v r‖ ^ 2 ≤ K * ∑ r ∈ s, ‖c r‖ ^ 2 := by
  have hSchur := symmetric_row_bound152 s (fun r => ‖c r‖)
    (fun r q => ‖inner ℂ (v r) (v q)‖) K
    (fun _ _ _ _ => norm_nonneg _) (fun r _ q _ => norm_inner_symm _ _) hRow
  calc
    _ = ‖inner ℂ (∑ r ∈ s, c r • v r) (∑ r ∈ s, c r • v r)‖ := by simp
    _ = ‖∑ r ∈ s, ∑ q ∈ s, conj (c r) * (c q * inner ℂ (v r) (v q))‖ := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ ∑ r ∈ s, ∑ q ∈ s, ‖c r‖ * ‖c q‖ * ‖inner ℂ (v r) (v q)‖ := by
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro r hr
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro q hq
      simp only [norm_mul, RCLike.norm_conj, mul_assoc, le_refl]
    _ ≤ _ := hSchur

/-- The finite Halász–Montgomery inequality in an arbitrary complex inner
product space, with an explicit upper bound on every absolute Gram row. -/
theorem finite_halasz_montgomery152 {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι → E) (a : E) (K : ℝ) (hK : 0 ≤ K)
    (hRow : ∀ r ∈ s, (∑ q ∈ s, ‖inner ℂ (v r) (v q)‖) ≤ K) :
    (∑ r ∈ s, ‖inner ℂ (v r) a‖ ^ 2) ≤ K * ‖a‖ ^ 2 := by
  let c : ι → ℂ := fun r => inner ℂ (v r) a
  let g : E := ∑ r ∈ s, c r • v r
  let energy : ℝ := ∑ r ∈ s, ‖c r‖ ^ 2
  have hE0 : 0 ≤ energy := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hg : ‖g‖ ^ 2 ≤ K * energy := finite_gram_synthesis152 s v c K hRow
  have hga : inner ℂ g a = (energy : ℂ) := by
    dsimp [g, energy]
    rw [sum_inner, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [inner_smul_left]
    change conj (c r) * c r = ((‖c r‖ ^ 2 : ℝ) : ℂ)
    rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
  have hCS : energy ≤ ‖g‖ * ‖a‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) g a
    rw [hga, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE0] at h
    exact h
  have hsq : energy ^ 2 ≤ ‖g‖ ^ 2 * ‖a‖ ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg g) (norm_nonneg a)]
  have hmul := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖a‖)
  change energy ≤ K * ‖a‖ ^ 2
  by_cases hE : energy = 0
  · rw [hE]
    exact mul_nonneg hK (sq_nonneg _)
  · have hEpos : 0 < energy := lt_of_le_of_ne hE0 (by simpa only [eq_comm] using hE)
    apply (mul_le_mul_iff_right₀ hEpos).mp
    nlinarith

/-- Diagonal plus off-diagonal form, convenient for exponential kernels. -/
theorem finite_halasz_montgomery_offDiagonal152 {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι → E) (a : E) (D R : ℝ)
    (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hDiag : ∀ r ∈ s, ‖v r‖ ^ 2 ≤ D)
    (hOff : ∀ r ∈ s, (∑ q ∈ s.erase r, ‖inner ℂ (v r) (v q)‖) ≤ R) :
    (∑ r ∈ s, ‖inner ℂ (v r) a‖ ^ 2) ≤ (D + R) * ‖a‖ ^ 2 := by
  apply finite_halasz_montgomery152 s v a (D + R) (add_nonneg hD hR)
  intro r hr
  rw [← Finset.add_sum_erase s (fun q => ‖inner ℂ (v r) (v q)‖) hr]
  have hnorm : ‖inner ℂ (v r) (v r)‖ = ‖v r‖ ^ 2 := by simp
  rw [hnorm]
  exact add_le_add (hDiag r hr) (hOff r hr)

end Erdos374.HarmanGram152
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanGram152.symmetric_row_bound152,
    ``Erdos374.HarmanGram152.finite_gram_synthesis152,
    ``Erdos374.HarmanGram152.finite_halasz_montgomery152,
    ``Erdos374.HarmanGram152.finite_halasz_montgomery_offDiagonal152]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanGram152.finite_halasz_montgomery152

end Update152_Component_11
/- END COMPONENT: HarmanGram152.lean -/

/- BEGIN COMPONENT: HarmanDirichletGram152.lean -/
section Update152_Component_12


noncomputable section
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos374.HarmanGram152
open HarmanAnalytic151MeanSquare

theorem conj_kernel152 (ω t : ℝ) :
    conj (exponentialKernel151 ω t) = exponentialKernel151 ω (-t) := by
  unfold exponentialKernel151
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem kernel_add_time152 (ω t u : ℝ) :
    exponentialKernel151 ω t * exponentialKernel151 ω u = exponentialKernel151 ω (t + u) := by
  unfold exponentialKernel151
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def coefficientVector152 (s : Finset ℕ) (a : ℕ → ℂ) : EuclideanSpace ℂ s :=
  WithLp.toLp 2 (fun n => a n)

def dirichletVector152 (s : Finset ℕ) (t : ℝ) : EuclideanSpace ℂ s :=
  coefficientVector152 s (fun n => exponentialKernel151 (Real.log n) (-t))

def dirichletGramKernel152 (s : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, exponentialKernel151 (Real.log n) t

def gramOffDiagonalBound152 (s : Finset ℕ) (r : Finset ℝ) : ℝ≥0 :=
  r.sup (fun t => ∑ u ∈ r.erase t, ‖dirichletGramKernel152 s (t - u)‖₊)

theorem coefficientVector_norm_sq152 (s : Finset ℕ) (a : ℕ → ℂ) :
    ‖coefficientVector152 s a‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [coefficientVector152, PiLp.toLp_apply]
  exact Finset.sum_coe_sort s (fun n => ‖a n‖ ^ 2)

theorem dirichletVector_norm_sq152 (s : Finset ℕ) (t : ℝ) :
    ‖dirichletVector152 s t‖ ^ 2 = (s.card : ℝ) := by
  rw [dirichletVector152, coefficientVector_norm_sq152]
  simp only [norm_kernel151, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem dirichletVector_analysis152 (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    inner ℂ (dirichletVector152 s t) (coefficientVector152 s a) =
      exponentialSum151 s a (fun n => Real.log n) t := by
  rw [PiLp.inner_apply]
  simp only [dirichletVector152, coefficientVector152, PiLp.toLp_apply,
    RCLike.inner_apply', conj_kernel152, neg_neg]
  rw [Finset.sum_coe_sort s (fun n => exponentialKernel151 (Real.log n) t * a n)]
  unfold exponentialSum151
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem dirichletVector_gram152 (s : Finset ℕ) (t u : ℝ) :
    inner ℂ (dirichletVector152 s t) (dirichletVector152 s u) =
      dirichletGramKernel152 s (t - u) := by
  rw [PiLp.inner_apply]
  simp only [dirichletVector152, coefficientVector152, PiLp.toLp_apply,
    RCLike.inner_apply', conj_kernel152, neg_neg,
    kernel_add_time152, sub_eq_add_neg, dirichletGramKernel152]
  exact Finset.sum_coe_sort s (fun n => exponentialKernel151 (Real.log n) (t + -u))

theorem gram_offDiagonal_row_le152 (s : Finset ℕ) (r : Finset ℝ) (t : ℝ) (ht : t ∈ r) :
    (∑ u ∈ r.erase t, ‖dirichletGramKernel152 s (t - u)‖) ≤ gramOffDiagonalBound152 s r := by
  have h := Finset.le_sup (f := fun t => ∑ u ∈ r.erase t, ‖dirichletGramKernel152 s (t - u)‖₊) ht
  have hh := NNReal.coe_le_coe.mpr h
  simpa only [NNReal.coe_sum, coe_nnnorm, gramOffDiagonalBound152] using hh

/-- The Dirichlet-polynomial Halász–Montgomery inequality with an actual
finite off-diagonal kernel maximum, not an assumed analytic bound. -/
theorem dirichlet_halasz_montgomery152 (s : Finset ℕ) (a : ℕ → ℂ) (r : Finset ℝ) :
    (∑ t ∈ r, ‖exponentialSum151 s a (fun n => Real.log n) t‖ ^ 2) ≤
      ((s.card : ℝ) + gramOffDiagonalBound152 s r) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have h := finite_halasz_montgomery_offDiagonal152 r (dirichletVector152 s)
    (coefficientVector152 s a) (s.card : ℝ) (gramOffDiagonalBound152 s r)
    (Nat.cast_nonneg _) (NNReal.coe_nonneg _) (fun t _ => (dirichletVector_norm_sq152 s t).le)
    (fun t ht => by
      simpa only [dirichletVector_gram152] using gram_offDiagonal_row_le152 s r t ht)
  simpa only [dirichletVector_analysis152, coefficientVector_norm_sq152] using h

theorem dirichlet_large_value_count152 (s : Finset ℕ) (a : ℕ → ℂ) (r : Finset ℝ)
    (V : ℝ) (hV : 0 < V)
    (hlarge : ∀ t ∈ r, V ≤ ‖exponentialSum151 s a (fun n => Real.log n) t‖) :
    (r.card : ℝ) ≤
      (((s.card : ℝ) + gramOffDiagonalBound152 s r) * ∑ n ∈ s, ‖a n‖ ^ 2) / V ^ 2 := by
  have hcount : (r.card : ℝ) * V ^ 2 ≤
      ∑ t ∈ r, ‖exponentialSum151 s a (fun n => Real.log n) t‖ ^ 2 := by
    calc
      _ = ∑ _ ∈ r, V ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t ht =>
        (sq_le_sq₀ hV.le (norm_nonneg _)).mpr (hlarge t ht))
  exact (le_div_iff₀ (sq_pos_of_pos hV)).mpr (hcount.trans (dirichlet_halasz_montgomery152 s a r))

end Erdos374.HarmanGram152
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanGram152.conj_kernel152,
    ``Erdos374.HarmanGram152.kernel_add_time152,
    ``Erdos374.HarmanGram152.coefficientVector152,
    ``Erdos374.HarmanGram152.dirichletVector152,
    ``Erdos374.HarmanGram152.dirichletGramKernel152,
    ``Erdos374.HarmanGram152.gramOffDiagonalBound152,
    ``Erdos374.HarmanGram152.coefficientVector_norm_sq152,
    ``Erdos374.HarmanGram152.dirichletVector_norm_sq152,
    ``Erdos374.HarmanGram152.dirichletVector_analysis152,
    ``Erdos374.HarmanGram152.dirichletVector_gram152,
    ``Erdos374.HarmanGram152.gram_offDiagonal_row_le152,
    ``Erdos374.HarmanGram152.dirichlet_halasz_montgomery152,
    ``Erdos374.HarmanGram152.dirichlet_large_value_count152]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanGram152.dirichlet_large_value_count152

end Update152_Component_12
/- END COMPONENT: HarmanDirichletGram152.lean -/

/- BEGIN COMPONENT: HarmanNormalized152.lean -/
section Update152_Component_13





noncomputable section
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos374.HarmanGram152
open HarmanAnalytic151MeanSquare

def normalizedCoefficients152 (a : ℕ → ℂ) (σ : ℝ) : ℕ → ℂ :=
  fun n => a n / (((n : ℝ) ^ σ : ℝ) : ℂ)

def verticalDirichlet152 (s : Finset ℕ) (a : ℕ → ℂ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))

theorem cpow_vertical_factor152 {n : ℕ} (hn : 0 < n) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ))) =
      ((((n : ℝ) ^ σ : ℝ) : ℂ))⁻¹ * exponentialKernel151 (Real.log n) (-t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_cpow hn0.le σ).symm
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hn0.le).symm
  rw [neg_add, Complex.cpow_add _ _ hnC, Complex.cpow_neg,
    hpow, Complex.cpow_def_of_ne_zero hnC]
  congr 1
  unfold exponentialKernel151
  rw [hlog]
  congr 1
  push_cast
  ring

theorem verticalDirichlet_eq_exponential152 (s : Finset ℕ) (a : ℕ → ℂ) (σ t : ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    verticalDirichlet152 s a σ t =
      exponentialSum151 s (normalizedCoefficients152 a σ) (fun n => Real.log n) (-t) := by
  unfold verticalDirichlet152 exponentialSum151 normalizedCoefficients152
  apply Finset.sum_congr rfl
  intro n hn
  rw [cpow_vertical_factor152 (hs n hn)]
  ring

theorem conjugate_exponential_sum152 (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    conj (exponentialSum151 s (fun n => conj (a n)) (fun n => Real.log n) t) =
      exponentialSum151 s a (fun n => Real.log n) (-t) := by
  simp only [exponentialSum151, map_sum, map_mul, conj_kernel152, starRingEnd_self_apply]

theorem verticalDirichlet_norm152 (s : Finset ℕ) (a : ℕ → ℂ) (σ t : ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    ‖verticalDirichlet152 s a σ t‖ =
      ‖exponentialSum151 s (fun n => conj (normalizedCoefficients152 a σ n))
        (fun n => Real.log n) t‖ := by
  rw [verticalDirichlet_eq_exponential152 s a σ t hs,
    ← conjugate_exponential_sum152, RCLike.norm_conj]

theorem normalized_coefficients_energy152 (s : Finset ℕ) (a : ℕ → ℂ)
    (M : ℕ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ s, M ≤ n) :
    (∑ n ∈ s, ‖normalizedCoefficients152 a σ n‖ ^ 2) ≤
      (∑ n ∈ s, ‖a n‖ ^ 2) / (M : ℝ) ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hM
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hM.trans (hs n hn)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hden : (M : ℝ) ≤ (n : ℝ) ^ σ := by
    calc
      _ ≤ (n : ℝ) := by exact_mod_cast hs n hn
      _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hσ
  have hnorm : ‖normalizedCoefficients152 a σ n‖ ≤ ‖a n‖ / (M : ℝ) := by
    simp only [normalizedCoefficients152, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn0.le σ)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hM0 hden
  have hsq := (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) hM0.le)).mpr hnorm
  simpa only [div_pow] using hsq

/-- Actual normalized Dirichlet polynomial on the vertical line Re(s)=σ.
The maximum off-diagonal kernel row is a defined finite quantity. -/
theorem normalized_halasz_montgomery152 (s : Finset ℕ) (a : ℕ → ℂ)
    (M : ℕ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ s, M ≤ n) (r : Finset ℝ) :
    (∑ t ∈ r, ‖verticalDirichlet152 s a σ t‖ ^ 2) ≤
      ((s.card : ℝ) + gramOffDiagonalBound152 s r) *
        ((∑ n ∈ s, ‖a n‖ ^ 2) / (M : ℝ) ^ 2) := by
  have hs0 : ∀ n ∈ s, 0 < n := fun n hn => Nat.zero_lt_of_lt (hM.trans (hs n hn))
  have h := dirichlet_halasz_montgomery152 s
    (fun n => conj (normalizedCoefficients152 a σ n)) r
  simp only [RCLike.norm_conj] at h
  have henergy := normalized_coefficients_energy152 s a M hM σ hσ hs
  calc
    _ = ∑ t ∈ r, ‖exponentialSum151 s (fun n => conj (normalizedCoefficients152 a σ n))
        (fun n => Real.log n) t‖ ^ 2 := by simp_rw [verticalDirichlet_norm152 s a σ _ hs0]
    _ ≤ ((s.card : ℝ) + gramOffDiagonalBound152 s r) *
        ∑ n ∈ s, ‖normalizedCoefficients152 a σ n‖ ^ 2 := h
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by positivity)

end Erdos374.HarmanGram152
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanGram152.normalizedCoefficients152,
    ``Erdos374.HarmanGram152.verticalDirichlet152,
    ``Erdos374.HarmanGram152.cpow_vertical_factor152,
    ``Erdos374.HarmanGram152.verticalDirichlet_eq_exponential152,
    ``Erdos374.HarmanGram152.conjugate_exponential_sum152,
    ``Erdos374.HarmanGram152.verticalDirichlet_norm152,
    ``Erdos374.HarmanGram152.normalized_coefficients_energy152,
    ``Erdos374.HarmanGram152.normalized_halasz_montgomery152]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanGram152.normalized_halasz_montgomery152

end Update152_Component_13
/- END COMPONENT: HarmanNormalized152.lean -/

/- BEGIN COMPONENT: HarmanRemaining152.lean -/
section Update152_Component_14



noncomputable section
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos374.HarmanGram152
open HarmanAnalytic151MeanSquare

theorem dyadic_support_card152 (s : Finset ℕ) (M : ℕ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M) : s.card ≤ M := by
  have hsub : s ⊆ Finset.Ioc M (2 * M) := fun n hn => Finset.mem_Ioc.mpr (hs n hn)
  have h := Finset.card_le_card hsub
  simp only [Nat.card_Ioc] at h
  omega

theorem normalized_energy_of_moment152 (s : Finset ℕ) (a : ℕ → ℂ)
    (M : ℕ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ s, M ≤ n) (Λ : ℝ)
    (hMoment : (∑ n ∈ s, ‖a n‖ ^ 2) ≤ (M : ℝ) * Λ) :
    (∑ n ∈ s, ‖normalizedCoefficients152 a σ n‖ ^ 2) ≤ Λ / M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hM
  calc
    _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) / (M : ℝ) ^ 2 :=
      normalized_coefficients_energy152 s a M hM σ hσ hs
    _ ≤ ((M : ℝ) * Λ) / (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hMoment (sq_nonneg _)
    _ = _ := by field_simp

/-- The source normalization with a finite coefficient second-moment bound.
The remaining kernel-row term is explicitly computed from the time points. -/
theorem normalized_dyadic_gram152 (s : Finset ℕ) (a : ℕ → ℂ)
    (M : ℕ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hMoment : (∑ n ∈ s, ‖a n‖ ^ 2) ≤ (M : ℝ) * Λ) (r : Finset ℝ) :
    (∑ t ∈ r, ‖verticalDirichlet152 s a σ t‖ ^ 2) ≤
      Λ * (1 + (gramOffDiagonalBound152 s r : ℝ) / M) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hM
  have hs0 : ∀ n ∈ s, 0 < n := fun n hn => lt_of_le_of_lt (Nat.zero_le _) (hs n hn).1
  have henergy := normalized_energy_of_moment152 s a M hM σ hσ
    (fun n hn => (hs n hn).1.le) Λ hMoment
  have h := dirichlet_halasz_montgomery152 s
    (fun n => conj (normalizedCoefficients152 a σ n)) r
  simp only [RCLike.norm_conj] at h
  have hcard : (s.card : ℝ) ≤ M := by exact_mod_cast dyadic_support_card152 s M hs
  calc
    _ = ∑ t ∈ r, ‖exponentialSum151 s (fun n => conj (normalizedCoefficients152 a σ n))
        (fun n => Real.log n) t‖ ^ 2 := by simp_rw [verticalDirichlet_norm152 s a σ _ hs0]
    _ ≤ ((s.card : ℝ) + gramOffDiagonalBound152 s r) *
        ∑ n ∈ s, ‖normalizedCoefficients152 a σ n‖ ^ 2 := h
    _ ≤ ((s.card : ℝ) + gramOffDiagonalBound152 s r) * (Λ / M) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ ≤ ((M : ℝ) + gramOffDiagonalBound152 s r) * (Λ / M) :=
      mul_le_mul_of_nonneg_right (add_le_add hcard le_rfl) (div_nonneg hΛ hM0.le)
    _ = _ := by field_simp

theorem normalized_dyadic_gram_count152 (s : Finset ℕ) (a : ℕ → ℂ)
    (M : ℕ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hMoment : (∑ n ∈ s, ‖a n‖ ^ 2) ≤ (M : ℝ) * Λ) (r : Finset ℝ)
    (V : ℝ) (hV : 0 < V) (hlarge : ∀ t ∈ r, V ≤ ‖verticalDirichlet152 s a σ t‖) :
    (r.card : ℝ) ≤ Λ * (1 + (gramOffDiagonalBound152 s r : ℝ) / M) / V ^ 2 := by
  have hcount : (r.card : ℝ) * V ^ 2 ≤ ∑ t ∈ r, ‖verticalDirichlet152 s a σ t‖ ^ 2 := by
    calc
      _ = ∑ _ ∈ r, V ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t ht => (sq_le_sq₀ hV.le (norm_nonneg _)).mpr (hlarge t ht))
  exact (le_div_iff₀ (sq_pos_of_pos hV)).mpr
    (hcount.trans (normalized_dyadic_gram152 s a M hM σ hσ hs Λ hΛ hMoment r))

/-- An explicit unconditional V^(-2) large-value bound for the actual
Dirichlet polynomial sum a_n n^(-σ-it), with the source coefficient moment.
This is weaker than the Halász–Huxley bound needed in Harman's Lemma 4. -/
theorem normalized_separated_count152 (s : Finset ℕ) (a : ℕ → ℂ)
    (M : ℕ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hMoment : (∑ n ∈ s, ‖a n‖ ^ 2) ≤ (M : ℝ) * Λ) (r : Finset ℝ)
    (hsep : ∀ t ∈ r, ∀ u ∈ r, t ≠ u → 1 ≤ |t - u|)
    (A B : ℝ) (hAB : A ≤ B) (hr : ∀ t ∈ r, A ≤ t ∧ t ≤ B)
    (V : ℝ) (hV : 0 < V) (hlarge : ∀ t ∈ r, V ≤ ‖verticalDirichlet152 s a σ t‖) :
    (r.card : ℝ) ≤
      ((1 + 2 * max 1 (Real.log (2 * M))) *
        (B + 1 - A + 4 * (2 * M) * (1 + Real.log (2 * M))) * (Λ / M)) / V ^ 2 := by
  have hs0 : ∀ n ∈ s, 0 < n := fun n hn => lt_of_le_of_lt (Nat.zero_le _) (hs n hn).1
  have hsN : ∀ n ∈ s, 1 ≤ n ∧ n ≤ 2 * M := fun n hn => ⟨hM.trans (hs n hn).1.le, (hs n hn).2⟩
  have henergy := normalized_energy_of_moment152 s a M hM σ hσ
    (fun n hn => (hs n hn).1.le) Λ hMoment
  have h := dirichlet_separated_mean_square151 s
    (fun n => conj (normalizedCoefficients152 a σ n)) (2 * M) hsN r hsep A B hAB hr
  simp only [RCLike.norm_conj, Nat.cast_mul, Nat.cast_ofNat] at h
  have hcoeff : 0 ≤ (1 + 2 * max 1 (Real.log (2 * M))) *
      (B + 1 - A + 4 * (2 * M) * (1 + Real.log (2 * M))) := by
    have hBA : 0 ≤ B + 1 - A := by linarith
    have hlog : 0 ≤ Real.log (2 * (M : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.log_natCast_nonneg (2 * M)
    have hmax : (0 : ℝ) ≤ max 1 (Real.log (2 * M)) := zero_le_one.trans (le_max_left _ _)
    positivity
  have hsample : (∑ t ∈ r, ‖verticalDirichlet152 s a σ t‖ ^ 2) ≤
      ((1 + 2 * max 1 (Real.log (2 * M))) *
        (B + 1 - A + 4 * (2 * M) * (1 + Real.log (2 * M)))) * (Λ / M) := by
    calc
      _ = ∑ t ∈ r, ‖exponentialSum151 s (fun n => conj (normalizedCoefficients152 a σ n))
          (fun n => Real.log n) t‖ ^ 2 := by simp_rw [verticalDirichlet_norm152 s a σ _ hs0]
      _ ≤ _ := h.trans (mul_le_mul_of_nonneg_left henergy hcoeff)
  have hcount : (r.card : ℝ) * V ^ 2 ≤ ∑ t ∈ r, ‖verticalDirichlet152 s a σ t‖ ^ 2 := by
    calc
      _ = ∑ _ ∈ r, V ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t ht => (sq_le_sq₀ hV.le (norm_nonneg _)).mpr (hlarge t ht))
  exact (le_div_iff₀ (sq_pos_of_pos hV)).mpr (hcount.trans hsample)

end Erdos374.HarmanGram152
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanGram152.dyadic_support_card152,
    ``Erdos374.HarmanGram152.normalized_energy_of_moment152,
    ``Erdos374.HarmanGram152.normalized_dyadic_gram152,
    ``Erdos374.HarmanGram152.normalized_dyadic_gram_count152,
    ``Erdos374.HarmanGram152.normalized_separated_count152]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanGram152.normalized_separated_count152



noncomputable section
open scoped BigOperators

namespace Erdos374.HarmanGram152

/-- The elementary separated mean square already yields the Halász–Huxley
shape in the low-amplitude regime M*V^4 ≤ 1. The complementary regime is
not asserted here. All logarithmic factors are retained explicitly. -/
theorem normalized_small_amplitude_count152 (s : Finset ℕ) (a : ℕ → ℂ)
    (M : ℕ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hMoment : (∑ n ∈ s, ‖a n‖ ^ 2) ≤ (M : ℝ) * Λ) (r : Finset ℝ)
    (hsep : ∀ t ∈ r, ∀ u ∈ r, t ≠ u → 1 ≤ |t - u|)
    (A B : ℝ) (hAB : A ≤ B) (hr : ∀ t ∈ r, A ≤ t ∧ t ≤ B)
    (V : ℝ) (hV : 0 < V) (hsmall : (M : ℝ) * V ^ 4 ≤ 1)
    (hlarge : ∀ t ∈ r, V ≤ ‖verticalDirichlet152 s a σ t‖) :
    (r.card : ℝ) ≤ (1 + 2 * max 1 (Real.log (2 * M))) * Λ *
      ((B + 1 - A) / ((M : ℝ) ^ 2 * V ^ 6) + 8 * (1 + Real.log (2 * M)) / V ^ 2) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hM
  have h := normalized_separated_count152 s a M hM σ hσ hs Λ hΛ hMoment r hsep A B hAB hr V hV hlarge
  have hT : 0 ≤ B + 1 - A := by linarith
  have hQ : 0 ≤ 1 + 2 * max 1 (Real.log (2 * M)) := by
    have : (0 : ℝ) ≤ max 1 (Real.log (2 * M)) := zero_le_one.trans (le_max_left _ _)
    positivity
  have hden : (M : ℝ) ^ 2 * V ^ 6 ≤ (M : ℝ) * V ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hM0.le (sq_nonneg V))
    convert hm using 1 <;> ring
  have hterm : (B + 1 - A) / ((M : ℝ) * V ^ 2) ≤
      (B + 1 - A) / ((M : ℝ) ^ 2 * V ^ 6) :=
    div_le_div_of_nonneg_left hT (by positivity) hden
  calc
    _ ≤ ((1 + 2 * max 1 (Real.log (2 * M))) *
        (B + 1 - A + 4 * (2 * M) * (1 + Real.log (2 * M))) * (Λ / M)) / V ^ 2 := h
    _ = (1 + 2 * max 1 (Real.log (2 * M))) * Λ *
        ((B + 1 - A) / ((M : ℝ) * V ^ 2) + 8 * (1 + Real.log (2 * M)) / V ^ 2) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hterm le_rfl) (mul_nonneg hQ hΛ)

end Erdos374.HarmanGram152
end

run_cmd do
  let axioms ← Lean.collectAxioms ``Erdos374.HarmanGram152.normalized_small_amplitude_count152
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

#print axioms Erdos374.HarmanGram152.normalized_small_amplitude_count152



noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.HarmanGram152
open HarmanAnalytic151MeanSquare

def unitPhase152 (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem unitPhase_norm_le152 (z : ℂ) : ‖unitPhase152 z‖ ≤ 1 := by
  simp only [unitPhase152, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · simp [hz]

theorem unitPhase_inner152 (z : ℂ) : conj (unitPhase152 z) * z = (‖z‖ : ℂ) := by
  simp only [unitPhase152, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div]
  rw [mul_comm (conj z), Complex.mul_conj']
  by_cases hz : (‖z‖ : ℂ) = 0
  · simp [hz]
  · field_simp

theorem unit_coefficient_gram_bound152 {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι → E) (c : ι → ℂ)
    (hc : ∀ r ∈ s, ‖c r‖ ≤ 1) :
    ‖∑ r ∈ s, c r • v r‖ ^ 2 ≤ ∑ r ∈ s, ∑ q ∈ s, ‖inner ℂ (v r) (v q)‖ := by
  calc
    _ = ‖inner ℂ (∑ r ∈ s, c r • v r) (∑ r ∈ s, c r • v r)‖ := by simp
    _ = ‖∑ r ∈ s, ∑ q ∈ s, conj (c r) * (c q * inner ℂ (v r) (v q))‖ := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ _ := by
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro r hr
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro q hq
      simp only [norm_mul, RCLike.norm_conj]
      have hcq := mul_le_mul_of_nonneg_right (hc q hq) (norm_nonneg (inner ℂ (v r) (v q)))
      have hcr := mul_le_mul_of_nonneg_right (hc r hr)
        (mul_nonneg (norm_nonneg (c q)) (norm_nonneg (inner ℂ (v r) (v q))))
      nlinarith

/-- Pair-average dual form of Halász–Montgomery. This retains the full
off-diagonal pair sum instead of bounding it by the largest row. -/
theorem finite_dual_gram152 {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι → E) (a : E) :
    (∑ r ∈ s, ‖inner ℂ (v r) a‖) ^ 2 ≤
      ‖a‖ ^ 2 * ∑ r ∈ s, ∑ q ∈ s, ‖inner ℂ (v r) (v q)‖ := by
  let c : ι → ℂ := fun r => unitPhase152 (inner ℂ (v r) a)
  let g : E := ∑ r ∈ s, c r • v r
  let S : ℝ := ∑ r ∈ s, ‖inner ℂ (v r) a‖
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hga : inner ℂ g a = (S : ℂ) := by
    dsimp [g, S]
    rw [sum_inner, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [inner_smul_left]
    exact unitPhase_inner152 _
  have hCS : S ≤ ‖g‖ * ‖a‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) g a
    rw [hga, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0] at h
    exact h
  have hsq : S ^ 2 ≤ ‖g‖ ^ 2 * ‖a‖ ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg g) (norm_nonneg a)]
  have hgram := unit_coefficient_gram_bound152 s v c (fun r _ => unitPhase_norm_le152 _)
  have hmul := mul_le_mul_of_nonneg_right hgram (sq_nonneg ‖a‖)
  change S ^ 2 ≤ _
  nlinarith

theorem dirichlet_dual_pair152 (s : Finset ℕ) (a : ℕ → ℂ) (r : Finset ℝ) :
    (∑ t ∈ r, ‖exponentialSum151 s a (fun n => Real.log n) t‖) ^ 2 ≤
      (∑ n ∈ s, ‖a n‖ ^ 2) * ∑ t ∈ r, ∑ u ∈ r, ‖dirichletGramKernel152 s (t - u)‖ := by
  have h := finite_dual_gram152 r (dirichletVector152 s) (coefficientVector152 s a)
  simpa only [dirichletVector_analysis152, coefficientVector_norm_sq152, dirichletVector_gram152] using h

theorem dirichlet_large_values_pair152 (s : Finset ℕ) (a : ℕ → ℂ) (r : Finset ℝ)
    (V : ℝ) (hV : 0 ≤ V)
    (hlarge : ∀ t ∈ r, V ≤ ‖exponentialSum151 s a (fun n => Real.log n) t‖) :
    (r.card : ℝ) ^ 2 * V ^ 2 ≤
      (∑ n ∈ s, ‖a n‖ ^ 2) * ∑ t ∈ r, ∑ u ∈ r, ‖dirichletGramKernel152 s (t - u)‖ := by
  have hsum : (r.card : ℝ) * V ≤ ∑ t ∈ r, ‖exponentialSum151 s a (fun n => Real.log n) t‖ := by
    calc
      _ = ∑ _ ∈ r, V := by simp
      _ ≤ _ := Finset.sum_le_sum hlarge
  have hsq := (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) hV)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr hsum
  rw [mul_pow] at hsq
  exact hsq.trans (dirichlet_dual_pair152 s a r)

theorem dirichlet_gram_pair_decomposition152 (s : Finset ℕ) (r : Finset ℝ) :
    (∑ t ∈ r, ∑ u ∈ r, ‖dirichletGramKernel152 s (t - u)‖) =
      (r.card : ℝ) * s.card + ∑ t ∈ r, ∑ u ∈ r.erase t, ‖dirichletGramKernel152 s (t - u)‖ := by
  classical
  have hk0 : ‖dirichletGramKernel152 s 0‖ = (s.card : ℝ) := by
    simp [dirichletGramKernel152, exponentialKernel151]
  calc
    _ = ∑ t ∈ r, ((s.card : ℝ) + ∑ u ∈ r.erase t, ‖dirichletGramKernel152 s (t - u)‖) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.add_sum_erase r (fun u => ‖dirichletGramKernel152 s (t - u)‖) ht]
      rw [sub_self, hk0]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- Normalized dual reduction retaining the actual off-diagonal pair sum.
An analytic bound for that sum is still needed in the high-amplitude range. -/
theorem normalized_dual_large_value152 (s : Finset ℕ) (a : ℕ → ℂ)
    (M : ℕ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hMoment : (∑ n ∈ s, ‖a n‖ ^ 2) ≤ (M : ℝ) * Λ)
    (r : Finset ℝ) (V : ℝ) (hV : 0 ≤ V)
    (hlarge : ∀ t ∈ r, V ≤ ‖verticalDirichlet152 s a σ t‖) :
    (r.card : ℝ) ^ 2 * V ^ 2 ≤ Λ * ((r.card : ℝ) +
      (∑ t ∈ r, ∑ u ∈ r.erase t, ‖dirichletGramKernel152 s (t - u)‖) / M) := by
  classical
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hM
  have hs0 : ∀ n ∈ s, 0 < n := fun n hn => lt_of_le_of_lt (Nat.zero_le _) (hs n hn).1
  have henergy := normalized_energy_of_moment152 s a M hM σ hσ
    (fun n hn => (hs n hn).1.le) Λ hMoment
  have h := dirichlet_large_values_pair152 s
    (fun n => conj (normalizedCoefficients152 a σ n)) r V hV (fun t ht => by
      rw [← verticalDirichlet_norm152 s a σ t hs0]
      exact hlarge t ht)
  simp only [RCLike.norm_conj] at h
  have hcard : (s.card : ℝ) ≤ M := by exact_mod_cast dyadic_support_card152 s M hs
  calc
    _ ≤ (∑ n ∈ s, ‖normalizedCoefficients152 a σ n‖ ^ 2) *
        ∑ t ∈ r, ∑ u ∈ r, ‖dirichletGramKernel152 s (t - u)‖ := h
    _ ≤ (Λ / M) * ∑ t ∈ r, ∑ u ∈ r, ‖dirichletGramKernel152 s (t - u)‖ :=
      mul_le_mul_of_nonneg_right henergy (Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    _ = (Λ / M) * ((r.card : ℝ) * s.card +
        ∑ t ∈ r, ∑ u ∈ r.erase t, ‖dirichletGramKernel152 s (t - u)‖) := by
      rw [dirichlet_gram_pair_decomposition152]
    _ ≤ (Λ / M) * ((r.card : ℝ) * M +
        ∑ t ∈ r, ∑ u ∈ r.erase t, ‖dirichletGramKernel152 s (t - u)‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)) le_rfl)
        (div_nonneg hΛ hM0.le)
    _ = _ := by field_simp

end Erdos374.HarmanGram152
end

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanGram152.unitPhase152,
    ``Erdos374.HarmanGram152.unitPhase_norm_le152,
    ``Erdos374.HarmanGram152.unitPhase_inner152,
    ``Erdos374.HarmanGram152.unit_coefficient_gram_bound152,
    ``Erdos374.HarmanGram152.finite_dual_gram152,
    ``Erdos374.HarmanGram152.dirichlet_dual_pair152,
    ``Erdos374.HarmanGram152.dirichlet_large_values_pair152,
    ``Erdos374.HarmanGram152.dirichlet_gram_pair_decomposition152,
    ``Erdos374.HarmanGram152.normalized_dual_large_value152]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Erdos374.HarmanGram152.dirichlet_large_values_pair152
#print axioms Erdos374.HarmanGram152.normalized_dual_large_value152

end Update152_Component_14
/- END COMPONENT: HarmanRemaining152.lean -/

/- BEGIN COMPONENT: HigherDifference152.lean -/
section Update152_Component_15


/-! Exact finite-difference identities and a third-order cancellation ingredient.
All ranges are finite; the values needed at the upper boundary are explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.HigherDifference152
open SecondDerivative151 SecondDerivativeVdC151 SecondDerivativeOptimized151

def difference : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, f => f
  | r + 1, f => increment (difference r f)

lemma difference_two (f : ℕ → ℝ) : difference 2 f = secondDifference f := rfl

lemma difference_shift (r : ℕ) (f : ℕ → ℝ) (h n : ℕ) :
    difference r (shiftedPhase f h) n = shiftedPhase (difference r f) h n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    change difference r (shiftedPhase f h) (n + 1) - difference r (shiftedPhase f h) n = _
    rw [ih, ih]
    unfold shiftedPhase
    change (difference r f (n + 1 + h) - difference r f (n + 1)) -
      (difference r f (n + h) - difference r f n) =
        (difference r f (n + h + 1) - difference r f (n + h)) -
          (difference r f (n + 1) - difference r f n)
    rw [show n + 1 + h = n + h + 1 by omega]
    ring

/-- Differencing a shift difference lowers its order by one, at the cost of
a sum over the actual shift length. No endpoint term is discarded. -/
lemma shifted_difference_eq_sum (r : ℕ) (f : ℕ → ℝ) (h n : ℕ) :
    difference r (shiftedPhase f h) n =
      ∑ j ∈ Finset.range h, difference (r + 1) f (n + j) := by
  rw [difference_shift]
  have ht := Finset.sum_range_sub (fun j => difference r f (n + j)) h
  symm
  simpa only [difference, increment, shiftedPhase, Nat.add_assoc, Nat.add_zero] using ht

lemma shifted_difference_bounds (r : ℕ) (f : ℕ → ℝ) (N h n : ℕ) (L U : ℝ)
    (hn : n < N - h)
    (hd : ∀ m < N, L ≤ difference (r + 1) f m ∧ difference (r + 1) f m ≤ U) :
    (h : ℝ) * L ≤ difference r (shiftedPhase f h) n ∧
      difference r (shiftedPhase f h) n ≤ (h : ℝ) * U := by
  rw [shifted_difference_eq_sum]
  constructor
  · calc
      _ = ∑ _j ∈ Finset.range h, L := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjh := Finset.mem_range.mp hj
        exact (hd (n + j) (by omega)).1
  · calc
      _ ≤ ∑ _j ∈ Finset.range h, U := by
        apply Finset.sum_le_sum
        intro j hj
        have hjh := Finset.mem_range.mp hj
        exact (hd (n + j) (by omega)).2
      _ = _ := by simp

lemma shifted_difference_monotone (r : ℕ) (f : ℕ → ℝ) (N h : ℕ)
    (hm : MonotoneOn (difference (r + 1) f) (Set.Iio N) ∨
      AntitoneOn (difference (r + 1) f) (Set.Iio N)) :
    MonotoneOn (difference r (shiftedPhase f h)) (Set.Iio (N - h)) ∨
      AntitoneOn (difference r (shiftedPhase f h)) (Set.Iio (N - h)) := by
  rcases hm with hm | hm
  · left
    intro m hmN n hnN hmn
    rw [shifted_difference_eq_sum, shifted_difference_eq_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjh := Finset.mem_range.mp hj
    exact hm (by simp only [Set.mem_Iio] at *; omega)
      (by simp only [Set.mem_Iio] at *; omega) (by omega)
  · right
    intro m hmN n hnN hmn
    rw [shifted_difference_eq_sum, shifted_difference_eq_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjh := Finset.mem_range.mp hj
    exact hm (by simp only [Set.mem_Iio] at *; omega)
      (by simp only [Set.mem_Iio] at *; omega) (by omega)

/-- A genuine second-order bound for each correlation of a third-order phase.
The bound is deduced from the checked order-two theorem, not assumed. -/
theorem third_difference_shifted_cancellation (N h : ℕ) (f : ℕ → ℝ) (L C : ℝ)
    (hh : 0 < h) (hL : 0 < L) (hC : 1 ≤ C)
    (hd : ∀ m < N, L ≤ difference 3 f m ∧ difference 3 f m ≤ C * L)
    (hm : MonotoneOn (difference 3 f) (Set.Iio N) ∨
      AntitoneOn (difference 3 f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range (N - h), KusminLandau151.e (shiftedPhase f h n)‖ ^ 2 ≤
      32 * C * (1 + Real.log ((N - h : ℕ) + 1 : ℝ)) *
        (((N - h : ℕ) : ℝ) ^ 2 * ((h : ℝ) * L) + 1 / ((h : ℝ) * L)) := by
  apply second_difference_optimized (N - h) (shiftedPhase f h) ((h : ℝ) * L) C
    (mul_pos (Nat.cast_pos.mpr hh) hL) hC
  · intro n hn
    have hb := shifted_difference_bounds 2 f N h n L (C * L) hn hd
    change (h : ℝ) * L ≤ difference 2 (shiftedPhase f h) n ∧
      difference 2 (shiftedPhase f h) n ≤ C * ((h : ℝ) * L)
    constructor
    · exact hb.1
    · calc
        _ ≤ (h : ℝ) * (C * L) := hb.2
        _ = _ := by ring
  · exact shifted_difference_monotone 2 f N h hm

theorem third_difference_shifted_cancellation_coarse (N h : ℕ) (f : ℕ → ℝ) (L C : ℝ)
    (hh : 0 < h) (hL : 0 < L) (hC : 1 ≤ C)
    (hd : ∀ m < N, L ≤ difference 3 f m ∧ difference 3 f m ≤ C * L)
    (hm : MonotoneOn (difference 3 f) (Set.Iio N) ∨
      AntitoneOn (difference 3 f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range (N - h), KusminLandau151.e (shiftedPhase f h n)‖ ^ 2 ≤
      32 * C * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * ((h : ℝ) * L) + 1 / ((h : ℝ) * L)) := by
  have hC0 : 0 ≤ C := by linarith
  have hhl : 0 < (h : ℝ) * L := mul_pos (Nat.cast_pos.mpr hh) hL
  have hΓ : 1 + Real.log (((N - h : ℕ) : ℝ) + 1) ≤ 1 + Real.log ((N : ℝ) + 1) := by
    apply add_le_add le_rfl
    exact Real.log_le_log (by positivity) (by exact_mod_cast (show N - h + 1 ≤ N + 1 by omega))
  have hΓ0 : 0 ≤ 1 + Real.log (((N - h : ℕ) : ℝ) + 1) := by
    have h := Real.log_nonneg (show 1 ≤ (((N - h : ℕ) : ℝ) + 1) by
      linarith [Nat.cast_nonneg (α := ℝ) (N - h)])
    linarith
  have hQ : (((N - h : ℕ) : ℝ) ^ 2 * ((h : ℝ) * L) + 1 / ((h : ℝ) * L)) ≤
      (N : ℝ) ^ 2 * ((h : ℝ) * L) + 1 / ((h : ℝ) * L) := by
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_right _ hhl.le
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le N h) 2
  have hΓN0 : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := hΓ0.trans hΓ
  apply (third_difference_shifted_cancellation N h f L C hh hL hC hd hm).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hΓ (by positivity)) hQ
    (by positivity) (by positivity)

#print axioms third_difference_shifted_cancellation
#print axioms third_difference_shifted_cancellation_coarse
run_cmd do
  for target in [``difference_shift, ``shifted_difference_eq_sum,
      ``shifted_difference_bounds, ``shifted_difference_monotone,
      ``third_difference_shifted_cancellation, ``third_difference_shifted_cancellation_coarse] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.HigherDifference152
end

end Update152_Component_15
/- END COMPONENT: HigherDifference152.lean -/

/- BEGIN COMPONENT: HigherDifferenceVdC152.lean -/
section Update152_Component_16


/-! Third-order cancellation by actual finite differencing, Cauchy--Schwarz,
the checked second-order test, and an explicit harmonic loss. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.HigherDifferenceVdC152
open ExponentialSum151 SecondDerivative151 SecondDerivativeVdC151 HigherDifference152

lemma third_correlation_sq_le_forward (N H : ℕ) (f : ℕ → ℝ) (h k : ℤ) (L C : ℝ)
    (hk0 : 0 ≤ k) (hkH : k < (H : ℤ)) (hkh : k < h)
    (hL : 0 < L) (hC : 1 ≤ C)
    (hd : ∀ m < N, L ≤ difference 3 f m ∧ difference 3 f m ≤ C * L)
    (hm : MonotoneOn (difference 3 f) (Set.Iio N) ∨
      AntitoneOn (difference 3 f) (Set.Iio N)) :
    ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖ ^ 2 ≤
      32 * C * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * |((h - k : ℤ) : ℝ)| * L + 1 / (|((h - k : ℤ) : ℝ)| * L)) := by
  rw [phase_correlation_forward N H f h k hk0 hkH hkh.le]
  have hdpos : 0 < (h - k).toNat := by omega
  have hdreal : ((h - k).toNat : ℝ) = |((h - k : ℤ) : ℝ)| := by
    rw [abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ h - k by omega))]
    exact_mod_cast (show (((h - k).toNat : ℕ) : ℤ) = h - k by omega)
  simpa only [hdreal, mul_assoc] using
    third_difference_shifted_cancellation_coarse N (h - k).toNat f L C hdpos hL hC hd hm

lemma third_correlation_sq_le (N H : ℕ) (f : ℕ → ℝ) (h k : ℤ) (L C : ℝ)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ)) (hk : k ∈ Finset.Ico (0 : ℤ) (H : ℤ))
    (hne : h ≠ k) (hL : 0 < L) (hC : 1 ≤ C)
    (hd : ∀ m < N, L ≤ difference 3 f m ∧ difference 3 f m ≤ C * L)
    (hm : MonotoneOn (difference 3 f) (Set.Iio N) ∨
      AntitoneOn (difference 3 f) (Set.Iio N)) :
    ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖ ^ 2 ≤
      32 * C * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * |((h - k : ℤ) : ℝ)| * L + 1 / (|((h - k : ℤ) : ℝ)| * L)) := by
  have hh' := Finset.mem_Ico.mp hh
  have hk' := Finset.mem_Ico.mp hk
  rcases lt_or_gt_of_ne hne with hhk | hkh
  · rw [norm_correlation_swap]
    have he : |((k - h : ℤ) : ℝ)| = |((h - k : ℤ) : ℝ)| := by
      push_cast
      exact abs_sub_comm _ _
    simpa only [he] using third_correlation_sq_le_forward N H f k h L C
      hh'.1 hh'.2 hhk hL hC hd hm
  · exact third_correlation_sq_le_forward N H f h k L C hk'.1 hk'.2 hkh hL hC hd hm

lemma distance_row_sum_le (H : ℕ) (h : ℤ)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ)) :
    (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h, |((h - k : ℤ) : ℝ)|) ≤ (H : ℝ) ^ 2 := by
  have hh' := Finset.mem_Ico.mp hh
  have hcard : ((Finset.Ico (0 : ℤ) (H : ℤ)).erase h).card ≤ H := by
    simpa only [card_integer_interval] using
      Finset.card_le_card (Finset.erase_subset h (Finset.Ico (0 : ℤ) (H : ℤ)))
  calc
    _ ≤ ∑ _k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h, (H : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_Ico.mp (Finset.mem_erase.mp hk).2
      have hh0 : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh'.1
      have hhH : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hh'.2.le
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk'.1
      have hkH : (k : ℝ) ≤ (H : ℝ) := by exact_mod_cast hk'.2.le
      rw [Int.cast_sub]
      apply abs_le.mpr
      constructor <;> linarith
    _ ≤ (H : ℝ) * H := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (Nat.cast_nonneg H)
    _ = _ := by ring

lemma inverse_distance_row_sum_le (H : ℕ) (h : ℤ) (L : ℝ) (hL : 0 < L)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ)) :
    (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
      1 / (|((h - k : ℤ) : ℝ)| * L)) ≤ (2 / L) * (1 + Real.log (H : ℝ)) := by
  have hd := distance_row_le H h L hL hh
  have he : (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h, distanceCost L (h - k)) =
      2 * ∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
        1 / (|((h - k : ℤ) : ℝ)| * L) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    unfold distanceCost
    ring
  rw [he, distanceCost_sum_eq_harmonic] at hd
  have hharm : (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
      1 / (|((h - k : ℤ) : ℝ)| * L)) ≤ (2 / L) * (harmonic H : ℝ) := by linarith
  exact hharm.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log H) (by positivity))

def rowBound (N H : ℕ) (L C : ℝ) : ℝ :=
  32 * C * (1 + Real.log ((N : ℝ) + 1)) *
    ((N : ℝ) ^ 2 * L * (H : ℝ) ^ 2 + (2 / L) * (1 + Real.log (H : ℝ)))

lemma rowBound_nonneg (N H : ℕ) (L C : ℝ) (hH : 0 < H) (hL : 0 < L) (hC : 1 ≤ C) :
    0 ≤ rowBound N H L C := by
  have hC0 : 0 ≤ C := by linarith
  have hΓN : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
    linarith [Nat.cast_nonneg (α := ℝ) N])
  have hΓH : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  unfold rowBound
  positivity

lemma third_correlation_row_sq_le (N H : ℕ) (f : ℕ → ℝ) (h : ℤ) (L C : ℝ)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ)) (hL : 0 < L) (hC : 1 ≤ C)
    (hd : ∀ m < N, L ≤ difference 3 f m ∧ difference 3 f m ≤ C * L)
    (hm : MonotoneOn (difference 3 f) (Set.Iio N) ∨
      AntitoneOn (difference 3 f) (Set.Iio N)) :
    (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
      ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖ ^ 2) ≤
        rowBound N H L C := by
  have hC0 : 0 ≤ C := by linarith
  have hΓN : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
    linarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    _ ≤ ∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
        32 * C * (1 + Real.log ((N : ℝ) + 1)) *
          ((N : ℝ) ^ 2 * |((h - k : ℤ) : ℝ)| * L + 1 / (|((h - k : ℤ) : ℝ)| * L)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact third_correlation_sq_le N H f h k L C hh (Finset.mem_erase.mp hk).2
        (Ne.symm (Finset.mem_erase.mp hk).1) hL hC hd hm
    _ = 32 * C * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * L * (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
          |((h - k : ℤ) : ℝ)|) + ∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
            1 / (|((h - k : ℤ) : ℝ)| * L)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (distance_row_sum_le H h hh) (by positivity))
        (inverse_distance_row_sum_le H h L hL hh)

lemma sum_sq_le_card_sum_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (a i) ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) a
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using hc

/-- A genuine third-order exponential-sum estimate with an explicit positive
integer shift parameter. The logarithmic loss is entirely accounted for. -/
theorem third_difference_vdc (N H : ℕ) (f : ℕ → ℝ) (L C : ℝ)
    (hH : 0 < H) (hL : 0 < L) (hC : 1 ≤ C)
    (hd : ∀ m < N, L ≤ difference 3 f m ∧ difference 3 f m ≤ C * L)
    (hm : MonotoneOn (difference 3 f) (Set.Iio N) ∨
      AntitoneOn (difference 3 f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      (((N : ℝ) + H) / H) * ((N : ℝ) + Real.sqrt ((H : ℝ) * rowBound N H L C)) := by
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hR0 := rowBound_nonneg N H L C hH hL hC
  have hr : ∀ h ∈ Finset.Ico (0 : ℤ) (H : ℤ),
      (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
        ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖) ≤
          Real.sqrt ((H : ℝ) * rowBound N H L C) := by
    intro h hh
    have hcard : (((Finset.Ico (0 : ℤ) (H : ℤ)).erase h).card : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast (show ((Finset.Ico (0 : ℤ) (H : ℤ)).erase h).card ≤ H from
        by simpa only [card_integer_interval] using
          Finset.card_le_card (Finset.erase_subset h (Finset.Ico (0 : ℤ) (H : ℤ))))
    have hs := sum_sq_le_card_sum_sq ((Finset.Ico (0 : ℤ) (H : ℤ)).erase h)
      (fun k => ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖)
    have hs' := hs.trans (mul_le_mul hcard (third_correlation_row_sq_le N H f h L C hh hL hC hd hm)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hHr.le)
    apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt (mul_nonneg hHr.le hR0)]
  have hv := van_der_corput_interval_supported N H (phaseSequence N f)
    (phaseSequence_support N f) (fun n hn => by simp [phaseSequence, hn, KusminLandau151.norm_e])
  rw [sum_phaseSequence] at hv
  have hv' : (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      ((N : ℝ) + H) * ((H : ℝ) * N + (H : ℝ) * Real.sqrt ((H : ℝ) * rowBound N H L C)) := by
    apply hv.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ _h ∈ Finset.Ico (0 : ℤ) (H : ℤ), Real.sqrt ((H : ℝ) * rowBound N H L C) :=
        Finset.sum_le_sum hr
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_integer_interval]
  have he : ((N : ℝ) + H) * ((H : ℝ) * N + (H : ℝ) * Real.sqrt ((H : ℝ) * rowBound N H L C)) =
      (H : ℝ) ^ 2 * ((((N : ℝ) + H) / H) *
        ((N : ℝ) + Real.sqrt ((H : ℝ) * rowBound N H L C))) := by field_simp
  rw [he] at hv'
  exact le_of_mul_le_mul_left hv' (pow_pos hHr 2)

#print axioms third_difference_vdc
run_cmd do
  for target in [``third_correlation_sq_le, ``third_correlation_row_sq_le,
      ``third_difference_vdc] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.HigherDifferenceVdC152
end

end Update152_Component_16
/- END COMPONENT: HigherDifferenceVdC152.lean -/

/- BEGIN COMPONENT: HigherDifferenceBulk152.lean -/
section Update152_Component_17


/-! A coarse differencing step that discards small shifts explicitly.
This is intended for iterating fixed derivative orders with logarithmic losses. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Erdos374.HigherDifferenceBulk152
open ExponentialSum151 SecondDerivative151 SecondDerivativeVdC151 SecondDerivativeOptimized151

lemma even_weight_row_le (H : ℕ) (h : ℤ) (g : ℤ → ℝ)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ))
    (hg : ∀ d, 0 ≤ g d) (hsym : ∀ d, g (-d) = g d) :
    (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h, g (h - k)) ≤
      2 * ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), g d := by
  let S := (Finset.Ico (0 : ℤ) (H : ℤ)).erase h
  have hh' := Finset.mem_Ico.mp hh
  have hlow : (∑ k ∈ S.filter (fun k => k < h), g (h - k)) ≤
      ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), g d := by
    apply sum_injective_le _ _ (fun k => h - k) g _ _ hg
    · intro a ha b hb he
      dsimp only at he
      omega
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkS := Finset.mem_erase.mp hk'.1
      have hkI := Finset.mem_Ico.mp hkS.2
      simp only [Finset.mem_Icc]
      omega
  have hupp : (∑ k ∈ S.filter (fun k => ¬ k < h), g (h - k)) ≤
      ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), g d := by
    calc
      _ = ∑ k ∈ S.filter (fun k => ¬ k < h), g (k - h) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show k - h = -(h - k) by ring, hsym]
      _ ≤ _ := by
        apply sum_injective_le _ _ (fun k => k - h) g _ _ hg
        · intro a ha b hb he
          dsimp only at he
          omega
        · intro k hk
          have hk' := Finset.mem_filter.mp hk
          have hkS := Finset.mem_erase.mp hk'.1
          have hkI := Finset.mem_Ico.mp hkS.2
          simp only [Finset.mem_Icc]
          omega
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun k => k < h) (fun k => g (h - k))
  change (∑ k ∈ S, g (h - k)) ≤ _
  rw [← hsplit]
  linarith

def thresholdWeight (N Q : ℕ) (B : ℝ) (d : ℤ) : ℝ :=
  if |d| < (Q : ℤ) then (N : ℝ) else B

lemma threshold_weight_sum_le (N H Q : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    (∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), thresholdWeight N Q B d) ≤
      (Q : ℝ) * N + (H : ℝ) * B := by
  have hsmall : (∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ),
      if d < (Q : ℤ) then (N : ℝ) else 0) ≤ (Q : ℝ) * N := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
    have hs : (Finset.Icc (1 : ℤ) (H : ℤ)).filter (fun d => d < (Q : ℤ)) ⊆
        Finset.Ico (0 : ℤ) (Q : ℤ) := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hdI := Finset.mem_Icc.mp hd'.1
      simp only [Finset.mem_Ico]
      omega
    exact_mod_cast (show ((Finset.Icc (1 : ℤ) (H : ℤ)).filter (fun d => d < (Q : ℤ))).card ≤ Q from
      by simpa only [card_integer_interval] using Finset.card_le_card hs)
  have hcard : (Finset.Icc (1 : ℤ) (H : ℤ)).card = H := by rw [Int.card_Icc]; omega
  calc
    _ ≤ ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), ((if d < (Q : ℤ) then (N : ℝ) else 0) + B) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' := Finset.mem_Icc.mp hd
      unfold thresholdWeight
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ d)]
      split_ifs <;> linarith
    _ = (∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), if d < (Q : ℤ) then (N : ℝ) else 0) +
        (H : ℝ) * B := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ _ := add_le_add hsmall le_rfl

lemma phase_correlation_norm_le (N H : ℕ) (f : ℕ → ℝ) (h k : ℤ)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ)) (hk : k ∈ Finset.Ico (0 : ℤ) (H : ℤ)) :
    ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖ ≤ (N : ℝ) := by
  have hh' := Finset.mem_Ico.mp hh
  have hk' := Finset.mem_Ico.mp hk
  by_cases hkh : k ≤ h
  · rw [phase_correlation_forward N H f h k hk'.1 hk'.2 hkh]
    exact (norm_phase_sum_le (N - (h - k).toNat) (shiftedPhase f (h - k).toNat)).trans
      (by exact_mod_cast Nat.sub_le N (h - k).toNat)
  · rw [norm_correlation_swap, phase_correlation_forward N H f k h hh'.1 hh'.2 (by omega)]
    exact (norm_phase_sum_le (N - (k - h).toNat) (shiftedPhase f (k - h).toNat)).trans
      (by exact_mod_cast Nat.sub_le N (k - h).toNat)

lemma bulk_correlation_bound_forward (N H Q : ℕ) (f : ℕ → ℝ) (h k : ℤ) (B : ℝ)
    (hh : h ∈ Finset.Ico (0 : ℤ) (H : ℤ)) (hk : k ∈ Finset.Ico (0 : ℤ) (H : ℤ))
    (hkh : k < h)
    (hgood : ∀ d : ℕ, Q ≤ d → d < H →
      ‖∑ n ∈ Finset.range (N - d), KusminLandau151.e (shiftedPhase f d n)‖ ≤ B) :
    ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖ ≤
      thresholdWeight N Q B (h - k) := by
  have hh' := Finset.mem_Ico.mp hh
  have hk' := Finset.mem_Ico.mp hk
  unfold thresholdWeight
  split_ifs with hsmall
  · exact phase_correlation_norm_le N H f h k hh hk
  · rw [phase_correlation_forward N H f h k hk'.1 hk'.2 hkh.le]
    apply hgood (h - k).toNat
    · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ h - k)] at hsmall
      omega
    · omega

/-- Small shifts are bounded trivially and explicitly counted. This generic
step is used below with a proved lower-order estimate for every retained shift. -/
theorem bulk_differencing (N H Q : ℕ) (f : ℕ → ℝ) (B : ℝ)
    (hH : 0 < H) (hB : 0 ≤ B)
    (hgood : ∀ d : ℕ, Q ≤ d → d < H →
      ‖∑ n ∈ Finset.range (N - d), KusminLandau151.e (shiftedPhase f d n)‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      (((N : ℝ) + H) / H) * ((N : ℝ) + 2 * (Q : ℝ) * N + 2 * (H : ℝ) * B) := by
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hg0 : ∀ d : ℤ, 0 ≤ thresholdWeight N Q B d := by
    intro d
    unfold thresholdWeight
    split_ifs <;> positivity
  have hgsym : ∀ d : ℤ, thresholdWeight N Q B (-d) = thresholdWeight N Q B d := by
    intro d
    simp only [thresholdWeight, abs_neg]
  have hr : ∀ h ∈ Finset.Ico (0 : ℤ) (H : ℤ),
      (∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h,
        ‖correlation (Finset.Ico (-(H : ℤ)) (N : ℤ)) (phaseSequence N f) h k‖) ≤
          2 * ((Q : ℝ) * N + (H : ℝ) * B) := by
    intro h hh
    calc
      _ ≤ ∑ k ∈ (Finset.Ico (0 : ℤ) (H : ℤ)).erase h, thresholdWeight N Q B (h - k) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkI := (Finset.mem_erase.mp hk).2
        have hne := (Finset.mem_erase.mp hk).1
        rcases lt_or_gt_of_ne hne with hkh | hhk
        · exact bulk_correlation_bound_forward N H Q f h k B hh hkI hkh hgood
        · rw [norm_correlation_swap]
          have he : thresholdWeight N Q B (h - k) = thresholdWeight N Q B (k - h) := by
            rw [show h - k = -(k - h) by ring, hgsym]
          rw [he]
          exact bulk_correlation_bound_forward N H Q f k h B hkI hh hhk hgood
      _ ≤ 2 * ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), thresholdWeight N Q B d :=
        even_weight_row_le H h (thresholdWeight N Q B) hh hg0 hgsym
      _ ≤ _ := mul_le_mul_of_nonneg_left (threshold_weight_sum_le N H Q B hB) (by norm_num)
  have hv := van_der_corput_interval_supported N H (phaseSequence N f)
    (phaseSequence_support N f) (fun n hn => by simp [phaseSequence, hn, KusminLandau151.norm_e])
  rw [sum_phaseSequence] at hv
  have hv' : (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      ((N : ℝ) + H) * ((H : ℝ) * N + (H : ℝ) * (2 * ((Q : ℝ) * N + (H : ℝ) * B))) := by
    apply hv.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ _h ∈ Finset.Ico (0 : ℤ) (H : ℤ), 2 * ((Q : ℝ) * N + (H : ℝ) * B) :=
        Finset.sum_le_sum hr
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_integer_interval]
  have he : ((N : ℝ) + H) * ((H : ℝ) * N + (H : ℝ) * (2 * ((Q : ℝ) * N + (H : ℝ) * B))) =
      (H : ℝ) ^ 2 * ((((N : ℝ) + H) / H) *
        ((N : ℝ) + 2 * (Q : ℝ) * N + 2 * (H : ℝ) * B)) := by field_simp; ring
  rw [he] at hv'
  exact le_of_mul_le_mul_left hv' (pow_pos hHr 2)

#print axioms bulk_differencing
run_cmd do
  for target in [``even_weight_row_le, ``threshold_weight_sum_le, ``phase_correlation_norm_le,
      ``bulk_differencing] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.HigherDifferenceBulk152
end

end Update152_Component_17
/- END COMPONENT: HigherDifferenceBulk152.lean -/

/- BEGIN COMPONENT: HigherDifferenceIteration152.lean -/
section Update152_Component_18


/-! A proved recursive cancellation bound at every fixed finite-difference order.
There is no assumed cancellation at any stage: the base is the checked order-two
test and the induction uses the explicit discarded-small-shift inequality. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Erdos374.HigherDifferenceIteration152
open SecondDerivative151 SecondDerivativeOptimized151 HigherDifference152 HigherDifferenceBulk152

/-- The discarded-shift inequality in relative-error form. -/
theorem bulk_relative_bound (N H Q : ℕ) (f : ℕ → ℝ) (η : ℝ)
    (hH : 0 < H) (hHN : H ≤ N) (hη : 0 ≤ η)
    (hgood : ∀ d : ℕ, Q ≤ d → d < H →
      ‖∑ n ∈ Finset.range (N - d), KusminLandau151.e (shiftedPhase f d n)‖ ≤ η * (N : ℝ)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      (2 / (H : ℝ) + 4 * (Q : ℝ) / H + 4 * η) * (N : ℝ) ^ 2 := by
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hratio : ((N : ℝ) + H) / H ≤ 2 * (N : ℝ) / H := by
    apply div_le_div_of_nonneg_right _ hHr.le
    have hHNr : (H : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hHN
    linarith
  apply (bulk_differencing N H Q f (η * (N : ℝ)) hH (by positivity) hgood).trans
  calc
    _ ≤ (2 * (N : ℝ) / H) * ((N : ℝ) + 2 * (Q : ℝ) * N + 2 * (H : ℝ) * (η * N)) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by field_simp; ring

/-- If the diagonal cost, discarded fraction, and retained correlations are
all at most `η`, one differencing step costs at most `10 η` in squared norm. -/
theorem bulk_small_error (N H Q : ℕ) (f : ℕ → ℝ) (η : ℝ)
    (hH : 0 < H) (hHN : H ≤ N) (hη : 0 ≤ η)
    (hdiag : 1 / (H : ℝ) ≤ η) (hdiscard : (Q : ℝ) / H ≤ η)
    (hgood : ∀ d : ℕ, Q ≤ d → d < H →
      ‖∑ n ∈ Finset.range (N - d), KusminLandau151.e (shiftedPhase f d n)‖ ≤ η * (N : ℝ)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ^ 2 ≤
      10 * η * (N : ℝ) ^ 2 := by
  apply (bulk_relative_bound N H Q f η hH hHN hη hgood).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have he : 2 / (H : ℝ) + 4 * (Q : ℝ) / H + 4 * η =
      2 * (1 / (H : ℝ)) + 4 * ((Q : ℝ) / H) + 4 * η := by ring
  rw [he]
  linarith

/-- A finite maximum over retained positive shifts, with zero included so the
definition is valid even when the retained interval is empty. -/
def shiftMax (Q H : ℕ) (b : ℕ → ℝ) : ℝ :=
  (insert 0 (Finset.Ico Q H)).sup' (by simp) (fun d => if d = 0 then 0 else b d)

lemma shiftMax_nonneg (Q H : ℕ) (b : ℕ → ℝ) : 0 ≤ shiftMax Q H b := by
  have hh := Finset.le_sup' (fun d => if d = 0 then (0 : ℝ) else b d)
    (Finset.mem_insert_self 0 (Finset.Ico Q H))
  simpa [shiftMax] using! hh

lemma le_shiftMax (Q H d : ℕ) (b : ℕ → ℝ) (hd0 : 0 < d) (hQ : Q ≤ d) (hH : d < H) :
    b d ≤ shiftMax Q H b := by
  have hmem : d ∈ insert 0 (Finset.Ico Q H) :=
    Finset.mem_insert_of_mem (Finset.mem_Ico.mpr ⟨hQ, hH⟩)
  have hh := Finset.le_sup' (fun d => if d = 0 then (0 : ℝ) else b d) hmem
  simpa only [shiftMax, ite_eq_right (Nat.ne_of_gt hd0)] using hh

/-- `r` counts differencing steps beyond the base order two. `H` and `Q`
are explicit numerical choices of shift length and discarded-shift cutoff. -/
def iteratedBound (H Q : ℕ → ℕ) : ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, N, L, C =>
      Real.sqrt (32 * C * (1 + Real.log ((N : ℝ) + 1)) * ((N : ℝ) ^ 2 * L + 1 / L))
  | r + 1, N, L, C =>
      Real.sqrt ((((N : ℝ) + (H r : ℝ)) / (H r : ℝ)) *
        ((N : ℝ) + 2 * (Q r : ℝ) * N + 2 * (H r : ℝ) *
          shiftMax (Q r) (H r) (fun d => iteratedBound H Q r (N - d) ((d : ℝ) * L) C)))

lemma iteratedBound_nonneg (H Q : ℕ → ℕ) (r N : ℕ) (L C : ℝ) :
    0 ≤ iteratedBound H Q r N L C := by
  cases r <;> exact Real.sqrt_nonneg _

/-- A genuine all-fixed-orders cancellation bound. The caller supplies only
finite-difference shape bounds and numerical shift choices. All lower-order
cancellation estimates in the recursive expression are proved by induction. -/
theorem iterated_cancellation (r : ℕ) (H Q : ℕ → ℕ)
    (hH : ∀ j < r, 0 < H j) (hQ : ∀ j < r, 0 < Q j)
    (N : ℕ) (f : ℕ → ℝ) (L C : ℝ) (hL : 0 < L) (hC : 1 ≤ C)
    (hd : ∀ m < N, L ≤ difference (r + 2) f m ∧ difference (r + 2) f m ≤ C * L)
    (hm : MonotoneOn (difference (r + 2) f) (Set.Iio N) ∨
      AntitoneOn (difference (r + 2) f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ≤ iteratedBound H Q r N L C := by
  induction r generalizing N f L with
  | zero =>
    apply Real.le_sqrt_of_sq_le
    exact second_difference_optimized N f L C hL hC hd hm
  | succ r ih =>
    let B := shiftMax (Q r) (H r) (fun d => iteratedBound H Q r (N - d) ((d : ℝ) * L) C)
    have hB : 0 ≤ B := shiftMax_nonneg _ _ _
    have hgood : ∀ d : ℕ, Q r ≤ d → d < H r →
        ‖∑ n ∈ Finset.range (N - d), KusminLandau151.e (shiftedPhase f d n)‖ ≤ B := by
      intro d hQd hdH
      have hdpos : 0 < d := (hQ r (by omega)).trans_le hQd
      have hdl : 0 < (d : ℝ) * L := mul_pos (Nat.cast_pos.mpr hdpos) hL
      have hshape : ∀ m < N - d,
          (d : ℝ) * L ≤ difference (r + 2) (shiftedPhase f d) m ∧
            difference (r + 2) (shiftedPhase f d) m ≤ C * ((d : ℝ) * L) := by
        intro m hmN
        have hb := shifted_difference_bounds (r + 2) f N d m L (C * L) hmN hd
        constructor
        · exact hb.1
        · calc
            _ ≤ (d : ℝ) * (C * L) := hb.2
            _ = _ := by ring
      have hmono : MonotoneOn (difference (r + 2) (shiftedPhase f d)) (Set.Iio (N - d)) ∨
          AntitoneOn (difference (r + 2) (shiftedPhase f d)) (Set.Iio (N - d)) :=
        shifted_difference_monotone (r + 2) f N d hm
      have hc := ih (fun j hj => hH j (by omega)) (fun j hj => hQ j (by omega))
        (N - d) (shiftedPhase f d) ((d : ℝ) * L) hdl hshape hmono
      exact hc.trans (le_shiftMax (Q r) (H r) d
        (fun d => iteratedBound H Q r (N - d) ((d : ℝ) * L) C) hdpos hQd hdH)
    apply Real.le_sqrt_of_sq_le
    exact bulk_differencing N (H r) (Q r) f B (hH r (by omega)) hB hgood

#print axioms iterated_cancellation
run_cmd do
  for target in [``bulk_relative_bound, ``bulk_small_error,
      ``shiftMax_nonneg, ``le_shiftMax, ``iterated_cancellation] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.HigherDifferenceIteration152
end

end Update152_Component_18
/- END COMPONENT: HigherDifferenceIteration152.lean -/

/- BEGIN COMPONENT: HigherDifferenceWindow152.lean -/
section Update152_Component_19


/-! Uniform smallness from numerical leaf windows in the all-order difference
tree. The hypotheses contain phase-shape and numerical inequalities only. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Erdos374.HigherDifferenceWindow152
open SecondDerivative151 SecondDerivativeOptimized151 HigherDifference152 HigherDifferenceBulk152

lemma squared_budget (ε : ℝ) (r : ℕ) : (ε ^ 2) ^ (2 ^ r) = ε ^ (2 ^ (r + 1)) := by
  rw [← pow_mul]
  congr 1
  rw [pow_succ]
  omega

lemma bulk_ambient (M N H Q : ℕ) (f : ℕ → ℝ) (η : ℝ)
    (hM : M ≤ N) (hH : 0 < H) (hHN : H ≤ N) (hη : 0 ≤ η)
    (hgood : ∀ d : ℕ, Q ≤ d → d < H →
      ‖∑ n ∈ Finset.range (M - d), KusminLandau151.e (shiftedPhase f d n)‖ ≤ η * (N : ℝ)) :
    ‖∑ n ∈ Finset.range M, KusminLandau151.e (f n)‖ ^ 2 ≤
      (2 / (H : ℝ) + 4 * (Q : ℝ) / H + 4 * η) * (N : ℝ) ^ 2 := by
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hMr : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hM
  have hHNr : (H : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hHN
  have hratio : ((M : ℝ) + H) / H ≤ 2 * (N : ℝ) / H := by
    apply div_le_div_of_nonneg_right _ hHr.le
    linarith
  have hbracket : (M : ℝ) + 2 * (Q : ℝ) * M + 2 * (H : ℝ) * (η * N) ≤
      (N : ℝ) + 2 * (Q : ℝ) * N + 2 * (H : ℝ) * (η * N) := by
    have hp := mul_le_mul_of_nonneg_left hMr (show 0 ≤ 2 * (Q : ℝ) by positivity)
    linarith
  apply (bulk_differencing M H Q f (η * (N : ℝ)) hH (by positivity) hgood).trans
  calc
    _ ≤ (2 * (N : ℝ) / H) * ((N : ℝ) + 2 * (Q : ℝ) * N + 2 * (H : ℝ) * (η * N)) :=
      mul_le_mul hratio hbracket (by positivity) (by positivity)
    _ = _ := by field_simp; ring

/-- At order `r+2`, a uniform numerical window for the eventual second
differences implies cancellation. `ε^(2^r)` pays for every discarded shift
and diagonal; the leaf estimate is explicitly powered to the required depth. -/
theorem cancellation_of_window (r M N H Q : ℕ) (f : ℕ → ℝ)
    (L C Llo Lhi ε : ℝ)
    (hM : M ≤ N) (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hL : 0 < L) (hC : 1 ≤ C) (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * L ≤ Lhi) (hlower : Llo ≤ (Q : ℝ) ^ r * L)
    (hbase : 32 * C * (1 + Real.log ((N : ℝ) + 1)) * ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤
      ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r)) (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r))
    (hd : ∀ m < M, L ≤ difference (r + 2) f m ∧ difference (r + 2) f m ≤ C * L)
    (hm : MonotoneOn (difference (r + 2) f) (Set.Iio M) ∨
      AntitoneOn (difference (r + 2) f) (Set.Iio M)) :
    ‖∑ n ∈ Finset.range M, KusminLandau151.e (f n)‖ ≤ 10 * ε * (N : ℝ) := by
  induction r generalizing M f L ε with
  | zero =>
    have hLLhi : L ≤ Lhi := by simpa using hupper
    have hLloL : Llo ≤ L := by simpa using hlower
    have hC0 : 0 ≤ C := by linarith
    have hΓN : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
      have := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
      linarith
    have hΓM : 1 + Real.log ((M : ℝ) + 1) ≤ 1 + Real.log ((N : ℝ) + 1) := by
      apply add_le_add le_rfl
      exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hM 1)
    have hT : (M : ℝ) ^ 2 * L + 1 / L ≤ (N : ℝ) ^ 2 * Lhi + 1 / Llo := by
      apply add_le_add
      · exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg M) (Nat.cast_le.mpr hM) 2)
          hLLhi hL.le (sq_nonneg _)
      · exact div_le_div_of_nonneg_left (by norm_num) hlo hLloL
    have hs := second_difference_optimized M f L C hL hC hd hm
    have hs' : ‖∑ n ∈ Finset.range M, KusminLandau151.e (f n)‖ ^ 2 ≤ ε ^ 2 * (N : ℝ) ^ 2 := by
      have hb := hs.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hΓM (by positivity)) hT
        (by positivity) (by positivity)).trans hbase)
      simpa only [Nat.zero_add, pow_one] using hb
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    exact hs'.trans (by nlinarith [sq_nonneg (ε * (N : ℝ))])
  | succ r ih =>
    have hgood : ∀ d : ℕ, Q ≤ d → d < H →
        ‖∑ n ∈ Finset.range (M - d), KusminLandau151.e (shiftedPhase f d n)‖ ≤
          (10 * ε ^ 2) * (N : ℝ) := by
      intro d hQd hdH
      have hd0 : 0 < d := hQ.trans_le hQd
      have hdl : 0 < (d : ℝ) * L := mul_pos (Nat.cast_pos.mpr hd0) hL
      have hupper' : (H : ℝ) ^ r * ((d : ℝ) * L) ≤ Lhi := by
        calc
          _ = ((H : ℝ) ^ r * L) * d := by ring
          _ ≤ ((H : ℝ) ^ r * L) * H :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdH.le) (by positivity)
          _ = (H : ℝ) ^ (r + 1) * L := by rw [pow_succ]; ring
          _ ≤ _ := hupper
      have hlower' : Llo ≤ (Q : ℝ) ^ r * ((d : ℝ) * L) := by
        calc
          _ ≤ (Q : ℝ) ^ (r + 1) * L := hlower
          _ = ((Q : ℝ) ^ r * L) * Q := by rw [pow_succ]; ring
          _ ≤ ((Q : ℝ) ^ r * L) * d :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hQd) (by positivity)
          _ = _ := by ring
      have hbase' : 32 * C * (1 + Real.log ((N : ℝ) + 1)) * ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤
          (ε ^ 2) ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2 := by
        rw [squared_budget]
        exact hbase
      have hdiag' : 1 / (H : ℝ) ≤ (ε ^ 2) ^ (2 ^ r) := by rw [squared_budget]; exact hdiag
      have hdiscard' : (Q : ℝ) / H ≤ (ε ^ 2) ^ (2 ^ r) := by rw [squared_budget]; exact hdiscard
      have hd' : ∀ m < M - d,
          (d : ℝ) * L ≤ difference (r + 2) (shiftedPhase f d) m ∧
            difference (r + 2) (shiftedPhase f d) m ≤ C * ((d : ℝ) * L) := by
        intro m hmM
        have hb := shifted_difference_bounds (r + 2) f M d m L (C * L) hmM hd
        exact ⟨hb.1, by simpa only [mul_left_comm (d : ℝ) C L] using hb.2⟩
      have hm' := shifted_difference_monotone (r + 2) f M d hm
      exact ih (M - d) (shiftedPhase f d) ((d : ℝ) * L) (ε ^ 2)
        ((Nat.sub_le M d).trans hM) hdl (pow_pos hε 2) (pow_le_one₀ hε.le hε1)
        hupper' hlower' hbase' hdiag' hdiscard' hd' hm'
    have hexp : 2 ≤ 2 ^ (r + 1) := by
      have hh : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    have hbudget : ε ^ (2 ^ (r + 1)) ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 hexp
    have hdiag2 : 1 / (H : ℝ) ≤ ε ^ 2 := hdiag.trans hbudget
    have hdiscard2 : (Q : ℝ) / H ≤ ε ^ 2 := hdiscard.trans hbudget
    have hs := bulk_ambient M N H Q f (10 * ε ^ 2) hM hH hHN (by positivity) hgood
    have hcoef : 2 / (H : ℝ) + 4 * (Q : ℝ) / H + 4 * (10 * ε ^ 2) ≤ 100 * ε ^ 2 := by
      have he : 2 / (H : ℝ) + 4 * (Q : ℝ) / H + 4 * (10 * ε ^ 2) =
          2 * (1 / (H : ℝ)) + 4 * ((Q : ℝ) / H) + 40 * ε ^ 2 := by ring
      rw [he]
      nlinarith [sq_nonneg ε]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      _ ≤ (100 * ε ^ 2) * (N : ℝ) ^ 2 :=
        hs.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
      _ = _ := by ring

/-- A concrete logarithmic-saving corollary. All extra premises are numerical
shift/window conditions; there is no exponential-sum premise. -/
theorem cancellation_log_power (r N H Q A : ℕ) (f : ℕ → ℝ) (L C Llo Lhi : ℝ)
    (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hL : 0 < L) (hC : 1 ≤ C) (hlo : 0 < Llo)
    (hupper : (H : ℝ) ^ r * L ≤ Lhi) (hlower : Llo ≤ (Q : ℝ) ^ r * L)
    (hbase : 32 * C * (1 + Real.log ((N : ℝ) + 1)) * ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤
      (1 / (Real.log (N : ℝ)) ^ A) ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ (1 / (Real.log (N : ℝ)) ^ A) ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ (1 / (Real.log (N : ℝ)) ^ A) ^ (2 ^ r))
    (hd : ∀ m < N, L ≤ difference (r + 2) f m ∧ difference (r + 2) f m ≤ C * L)
    (hm : MonotoneOn (difference (r + 2) f) (Set.Iio N) ∨
      AntitoneOn (difference (r + 2) f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ≤ 10 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  have hp : 0 < (Real.log (N : ℝ)) ^ A := pow_pos (by linarith) A
  have hp1 : 1 ≤ (Real.log (N : ℝ)) ^ A := one_le_pow₀ hlog
  have he : 1 / (Real.log (N : ℝ)) ^ A ≤ 1 := (div_le_one hp).mpr hp1
  have hs := cancellation_of_window r N N H Q f L C Llo Lhi (1 / (Real.log (N : ℝ)) ^ A)
    le_rfl hH hQ hHN hL hC hlo (by positivity) he hupper hlower hbase hdiag hdiscard hd hm
  convert hs using 1 <;> ring

#print axioms cancellation_of_window
#print axioms cancellation_log_power
run_cmd do
  for target in [``bulk_ambient, ``cancellation_of_window, ``cancellation_log_power] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.HigherDifferenceWindow152
end

end Update152_Component_19
/- END COMPONENT: HigherDifferenceWindow152.lean -/

/- BEGIN COMPONENT: HigherDifferenceChoice152.lean -/
section Update152_Component_20


/-! Rounding continuous shift scales to admissible integer shifts. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Erdos374.HigherDifferenceChoice152
open HigherDifference152 HigherDifferenceWindow152

lemma floor_half_bounds (x : ℝ) (hx : 2 ≤ x) :
    0 < ⌊x⌋₊ ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by norm_num; linarith)
  have h2 := Nat.lt_floor_add_one x
  exact ⟨by omega, by linarith, Nat.floor_le hx0⟩

/-- Explicit integer choices `H=floor T` and `Q=floor(H/K)`.
Their rounding losses are included in both the leaf window and discarded fraction. -/
theorem rounded_shift_parameters (N : ℕ) (T K : ℝ)
    (hK : 1 ≤ K) (hTK : 4 * K ≤ T) (hTN : T ≤ (N : ℝ)) :
    ∃ H Q : ℕ, 0 < H ∧ 0 < Q ∧ H ≤ N ∧
      (H : ℝ) ≤ T ∧ T / (4 * K) ≤ (Q : ℝ) ∧
        1 / (H : ℝ) ≤ 2 / T ∧ (Q : ℝ) / H ≤ 1 / K := by
  have hK0 : 0 < K := by linarith
  have hT0 : 0 < T := by linarith
  let H : ℕ := ⌊T⌋₊
  have hHb := floor_half_bounds T (by linarith)
  have hH : 0 < H := hHb.1
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hHK : 2 ≤ (H : ℝ) / K := by
    apply (le_div_iff₀ hK0).mpr
    have hhalf : T / 2 ≤ (H : ℝ) := hHb.2.1
    linarith
  let Q : ℕ := ⌊(H : ℝ) / K⌋₊
  have hQb := floor_half_bounds ((H : ℝ) / K) hHK
  refine ⟨H, Q, hH, hQb.1, ?_, hHb.2.2, ?_, ?_, ?_⟩
  · exact_mod_cast hHb.2.2.trans hTN
  · calc
      _ = (T / 2) / K / 2 := by ring
      _ ≤ ((H : ℝ) / K) / 2 :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hHb.2.1 hK0.le) (by norm_num)
      _ ≤ _ := hQb.2.1
  · apply (div_le_div_iff₀ hHr hT0).mpr
    have hhalf : T / 2 ≤ (H : ℝ) := hHb.2.1
    linarith
  · apply (div_le_iff₀ hHr).mpr
    calc
      (Q : ℝ) ≤ (H : ℝ) / K := hQb.2.2
      _ = (1 / K) * (H : ℝ) := by ring

/-- All integer-shift choices are constructed. Remaining hypotheses specify
only a continuous numerical scale, its leaf window, and actual phase shape. -/
theorem cancellation_real_parameters (r N : ℕ) (f : ℕ → ℝ) (L C ε T K : ℝ)
    (hL : 0 < L) (hC : 1 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hK : 1 ≤ K) (hTK : 4 * K ≤ T) (hTN : T ≤ (N : ℝ))
    (hdiag : 2 / T ≤ ε ^ (2 ^ r)) (hdiscard : 1 / K ≤ ε ^ (2 ^ r))
    (hbase : 32 * C * (1 + Real.log ((N : ℝ) + 1)) *
      ((N : ℝ) ^ 2 * (T ^ r * L) + 1 / ((T / (4 * K)) ^ r * L)) ≤
        ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hd : ∀ m < N, L ≤ difference (r + 2) f m ∧ difference (r + 2) f m ≤ C * L)
    (hm : MonotoneOn (difference (r + 2) f) (Set.Iio N) ∨
      AntitoneOn (difference (r + 2) f) (Set.Iio N)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (f n)‖ ≤ 10 * ε * (N : ℝ) := by
  obtain ⟨H, Q, hH, hQ, hHN, hHT, hTQ, hdi, hdis⟩ := rounded_shift_parameters N T K hK hTK hTN
  have hK0 : 0 < K := by linarith
  have hT0 : 0 < T := by linarith
  apply cancellation_of_window r N N H Q f L C ((T / (4 * K)) ^ r * L) (T ^ r * L) ε
    le_rfl hH hQ hHN hL hC (by positivity) hε hε1
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg H) hHT r) hL.le
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hTQ r) hL.le
  · exact hbase
  · exact hdi.trans hdiag
  · exact hdis.trans hdiscard
  · exact hd
  · exact hm

/-- The same constructed parameters work uniformly on every shortened
interval of length `M≤N`, with the error measured on the ambient scale `N`. -/
theorem cancellation_real_parameters_on_prefix (r M N : ℕ) (f : ℕ → ℝ) (L C ε T K : ℝ)
    (hM : M ≤ N) (hL : 0 < L) (hC : 1 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hK : 1 ≤ K) (hTK : 4 * K ≤ T) (hTN : T ≤ (N : ℝ))
    (hdiag : 2 / T ≤ ε ^ (2 ^ r)) (hdiscard : 1 / K ≤ ε ^ (2 ^ r))
    (hbase : 32 * C * (1 + Real.log ((N : ℝ) + 1)) *
      ((N : ℝ) ^ 2 * (T ^ r * L) + 1 / ((T / (4 * K)) ^ r * L)) ≤
        ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hd : ∀ m < M, L ≤ difference (r + 2) f m ∧ difference (r + 2) f m ≤ C * L)
    (hm : MonotoneOn (difference (r + 2) f) (Set.Iio M) ∨
      AntitoneOn (difference (r + 2) f) (Set.Iio M)) :
    ‖∑ n ∈ Finset.range M, KusminLandau151.e (f n)‖ ≤ 10 * ε * (N : ℝ) := by
  obtain ⟨H, Q, hH, hQ, hHN, hHT, hTQ, hdi, hdis⟩ := rounded_shift_parameters N T K hK hTK hTN
  have hK0 : 0 < K := by linarith
  have hT0 : 0 < T := by linarith
  apply cancellation_of_window r M N H Q f L C ((T / (4 * K)) ^ r * L) (T ^ r * L) ε
    hM hH hQ hHN hL hC (by positivity) hε hε1
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg H) hHT r) hL.le
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hTQ r) hL.le
  · exact hbase
  · exact hdi.trans hdiag
  · exact hdis.trans hdiscard
  · exact hd
  · exact hm

#print axioms cancellation_real_parameters
#print axioms cancellation_real_parameters_on_prefix
run_cmd do
  for target in [``rounded_shift_parameters, ``cancellation_real_parameters,
      ``cancellation_real_parameters_on_prefix] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.HigherDifferenceChoice152
end

end Update152_Component_20
/- END COMPONENT: HigherDifferenceChoice152.lean -/

/- BEGIN COMPONENT: LogWeightInsertion152.lean -/
section Update152_Component_21


/-! Inserting the logarithmic Type I weight using bounds on every prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Erdos374.LogWeightInsertion152
open LogWeightRemoval151

theorem log_weight_insertion (P N : ℕ) (hP : 1 ≤ P) (hPN : P ≤ N)
    (c : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hprefix : ∀ M : ℕ, P ≤ M → M ≤ N → ‖∑ n ∈ Finset.Ioc P M, c n‖ ≤ R) :
    ‖∑ n ∈ Finset.Ioc P N, (Real.log (n : ℝ) : ℂ) * c n‖ ≤
      (2 * Real.log (N : ℝ) - Real.log (P : ℝ)) * R := by
  have ha1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have ha : (0 : ℝ) < P := by linarith
  have hab : (P : ℝ) ≤ N := by exact_mod_cast hPN
  have hb1 : (1 : ℝ) ≤ N := ha1.trans hab
  let g : ℝ → ℂ := fun t => (Real.log t : ℂ)
  let g' : ℝ → ℂ := fun t => ((1 / t : ℝ) : ℂ)
  have hg : ∀ t ∈ Icc (P : ℝ) (N : ℝ), HasDerivAt g (g' t) t := by
    intro t ht
    simpa only [g, g', one_div] using
      (Real.hasDerivAt_log (ha.trans_le ht.1).ne').ofReal_comp
  have hrc : ContinuousOn (fun t : ℝ => 1 / t) (Icc (P : ℝ) (N : ℝ)) := by
    intro t ht
    exact (continuousAt_const.div continuousAt_id (ha.trans_le ht.1).ne').continuousWithinAt
  have hgc : ContinuousOn g' (Icc (P : ℝ) (N : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn hrc
  have hgi : IntegrableOn (deriv g) (Icc (P : ℝ) (N : ℝ)) := by
    apply hgc.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro t ht
    exact (hg t ht).deriv.symm
  have h := sum_mul_eq_sub_sub_integral_mul (after P c) ha.le hab
    (fun t ht => (hg t ht).differentiableAt) hgi
  simp_rw [after_sum] at h
  simp only [Nat.floor_natCast, Finset.Ioc_self, Finset.sum_empty, mul_zero, sub_zero] at h
  rw [← intervalIntegral.integral_of_le hab] at h
  have hlhs : (∑ n ∈ Finset.Ioc P N, g n * after P c n) =
      ∑ n ∈ Finset.Ioc P N, (Real.log (n : ℝ) : ℂ) * c n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [after, if_pos (Finset.mem_Ioc.mp hn).1, g]
  rw [hlhs] at h
  have hint : (∫ t in (P : ℝ)..(N : ℝ), 1 / t) = Real.log N - Real.log P := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hrc.intervalIntegrable_of_Icc hab)
    intro t ht
    rw [uIcc_of_le hab] at ht
    simpa only [one_div] using Real.hasDerivAt_log (ha.trans_le ht.1).ne'
  have hi : ‖∫ t in (P : ℝ)..(N : ℝ),
      deriv g t * (∑ n ∈ Finset.Ioc P ⌊t⌋₊, c n)‖ ≤
      (Real.log N - Real.log P) * R := by
    rw [← hint, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · apply Filter.Eventually.of_forall
      intro t ht
      have htI : t ∈ Icc (P : ℝ) (N : ℝ) := ⟨ht.1.le, ht.2⟩
      have hPM : P ≤ ⌊t⌋₊ := by simpa using Nat.floor_le_floor htI.1
      have hMN : ⌊t⌋₊ ≤ N := by simpa using Nat.floor_le_floor htI.2
      rw [(hg t htI).deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr (ha.trans_le htI.1))]
      exact mul_le_mul_of_nonneg_left (hprefix _ hPM hMN)
        (one_div_pos.mpr (ha.trans_le htI.1)).le
    · exact (hrc.intervalIntegrable_of_Icc hab).mul_const R
  have he : ‖g (N : ℝ) * (∑ n ∈ Finset.Ioc P N, c n)‖ ≤ Real.log N * R := by
    rw [norm_mul]
    have hn : ‖g (N : ℝ)‖ = Real.log N := by
      change ‖(Real.log (N : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hb1)]
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hprefix N hPN le_rfl) (Real.log_nonneg hb1)
  rw [h]
  calc
    _ ≤ ‖g (N : ℝ) * (∑ n ∈ Finset.Ioc P N, c n)‖ +
        ‖∫ t in (P : ℝ)..(N : ℝ), deriv g t * (∑ n ∈ Finset.Ioc P ⌊t⌋₊, c n)‖ :=
      norm_sub_le _ _
    _ ≤ Real.log N * R + (Real.log N - Real.log P) * R := add_le_add he hi
    _ = _ := by ring

theorem log_weight_insertion_coarse (P N : ℕ) (hP : 1 ≤ P) (hPN : P ≤ N)
    (c : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hprefix : ∀ M : ℕ, P ≤ M → M ≤ N → ‖∑ n ∈ Finset.Ioc P M, c n‖ ≤ R) :
    ‖∑ n ∈ Finset.Ioc P N, (Real.log (n : ℝ) : ℂ) * c n‖ ≤ 2 * Real.log (N : ℝ) * R := by
  apply (log_weight_insertion P N hP hPN c R hR hprefix).trans
  apply mul_le_mul_of_nonneg_right _ hR
  have hlog : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast hP)
  linarith

#print axioms log_weight_insertion
run_cmd do
  for target in [``log_weight_insertion, ``log_weight_insertion_coarse] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.LogWeightInsertion152
end

end Update152_Component_21
/- END COMPONENT: LogWeightInsertion152.lean -/

/- BEGIN COMPONENT: MangoldtClosure152.lean -/
section Update152_Component_22




/-! The remaining prime input reduced to actual large-phase Mangoldt prefix sums.
The cancellation estimate is still an explicit unproved input. Prime powers,
log weights, the reference integral, and the Fourier reduction are all proved. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace Erdos374.MangoldtClosure152
open ReciprocalCharacter151 FourierSampling151 SamplingClosure147 PrimePowerRemoval151

theorem primePower_error_budget (A : ℕ) :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → 2 ≤ P →
      2 * Real.sqrt (2 * (P : ℝ)) * Real.log (2 * (P : ℝ)) ≤
        (P : ℝ) / (Real.log (P : ℝ)) ^ A := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (RemainingAnalytic115.RemainingAnalytic141.primePower_logPower_eventually_small141
      A (1 / 2) (by norm_num))
  obtain ⟨N, hN⟩ := exists_nat_ge x₀
  refine ⟨N, ?_⟩
  intro P hP hP2
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hP1 : (1 : ℝ) < P := by exact_mod_cast (show 1 < P by omega)
  have hPP : (P : ℝ) ≤ 2 * (P : ℝ) := by linarith
  have hx : x₀ ≤ 2 * (P : ℝ) := hN.trans ((Nat.cast_le.mpr hP).trans hPP)
  have he := hx₀ (2 * (P : ℝ)) hx
  have hlog := Real.log_le_log hP0 hPP
  have hL0 := Real.log_pos hP1
  have hE : 0 ≤ 2 * Real.sqrt (2 * (P : ℝ)) * Real.log (2 * (P : ℝ)) := by
    have hlog2 : 0 ≤ Real.log (2 * (P : ℝ)) := hL0.le.trans hlog
    positivity
  apply (le_div_iff₀ (pow_pos hL0 A)).mpr
  calc
    _ ≤ (2 * Real.sqrt (2 * (P : ℝ)) * Real.log (2 * (P : ℝ))) *
        (Real.log (2 * (P : ℝ))) ^ A :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0.le hlog A) hE
    _ ≤ (P : ℝ) := by nlinarith only [he]

theorem prime_sum_from_log5_prefixes :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → 2 ≤ P → ∀ (w : ℕ → ℂ) (C : ℝ), 0 ≤ C →
      (∀ n ∈ Finset.Ioc P (2 * P), ‖w n‖ ≤ 1) →
      (∀ M : ℕ, P ≤ M → M ≤ 2 * P →
        ‖mangoldtSum (Finset.Ioc P M) w‖ ≤ C * (P : ℝ) / (Real.log (P : ℝ)) ^ 5) →
      ‖∑ p ∈ openPrimeBand P, w p‖ ≤
        (C + 1) * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 := by
  obtain ⟨N, hN⟩ := primePower_error_budget 5
  refine ⟨N, ?_⟩
  intro P hP hP2 w C hC hw hprefix
  have hL0 : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have h := MangoldtToPrimes151.prime_sum_of_mangoldt_prefix_bound P (2 * P)
    hP2 (by omega) w (C * (P : ℝ) / (Real.log (P : ℝ)) ^ 5) (by positivity) hw hprefix
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  change ‖∑ p ∈ openPrimeBand P, w p‖ ≤ _ at h
  calc
    _ ≤ (C * (P : ℝ) / (Real.log (P : ℝ)) ^ 5 +
        2 * Real.sqrt (2 * (P : ℝ)) * Real.log (2 * (P : ℝ))) / Real.log P := h
    _ ≤ (C * (P : ℝ) / (Real.log (P : ℝ)) ^ 5 +
        (P : ℝ) / (Real.log (P : ℝ)) ^ 5) / Real.log P := by
      exact div_le_div_of_nonneg_right (add_le_add le_rfl (hN P hP hP2)) hL0.le
    _ = _ := by field_simp <;> ring

/-- The still-unproved cancellation obligation after all sampling adapters.
Every truncated interval P<n<=M is required, with one uniform constant. -/
def LargePhaseMangoldtCancellation : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℕ, ∀ P b : ℕ,
    P₀ ≤ P → 2 ≤ P → 1 ≤ b → (b : ℝ) ^ γ ≤ (P : ℝ) →
    ∀ n m : ℤ, 0 < n.natAbs + m.natAbs →
      n.natAbs + m.natAbs ≤ ⌈(Real.log (P : ℝ)) ^ 6⌉₊ →
      (Real.log (P : ℝ)) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P →
      ∀ M : ℕ, P ≤ M → M ≤ 2 * P →
        ‖mangoldtSum (Finset.Ioc P M) (fun k => curveCharacter b n m k)‖ ≤
          C * (P : ℝ) / (Real.log (P : ℝ)) ^ 5

theorem large_phase_sampling_of_mangoldt (HM : LargePhaseMangoldtCancellation) :
    FourierLargePhase151.LargePhaseCharacterSampling := by
  intro γ hγ
  obtain ⟨B, C, hC, N, hN⟩ := HM γ hγ
  obtain ⟨NP, hNP⟩ := prime_sum_from_log5_prefixes
  obtain ⟨NI, hNI⟩ := FourierReferenceIntegral152.large_phase_reference_integral
  obtain ⟨NL, hNL⟩ := RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨max B 5, C + 785, by linarith, max N (max NP (max NI NL)), ?_⟩
  intro P b hP hP2 hb hPb n m hnm hfreq hF
  have hPN : N ≤ P := by omega
  have hPP : NP ≤ P := by omega
  have hPI : NI ≤ P := by omega
  have hPL : NL ≤ P := by omega
  have hL := hNL P hPL
  have hsmall : (Real.log (P : ℝ)) ^ B < amplitude ((n : ℝ) * b) ((m : ℝ) * b) P :=
    (pow_le_pow_right₀ hL (le_max_left B 5)).trans_lt hF
  have hs := hNP P hPP hP2 (fun k => curveCharacter b n m k) C hC.le
    (by
      intro k _
      rw [FourierLargePhase151.curveCharacter_eq_character, norm_character])
    (hN P b hPN hP2 hb hPb n m hnm hfreq hsmall)
  have hi := hNI P b hPI hb n m hnm hfreq (max B 5) (le_max_right B 5) hF
  calc
    ‖characterDiscrepancy P b n m‖ ≤
        ‖∑ p ∈ openPrimeBand P, curveCharacter b n m p‖ +
        ‖∫ t in (P : ℝ)..(2 * (P : ℝ)), curveCharacter b n m t / (Real.log t : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ (C + 1) * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 +
        784 * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 := add_le_add hs hi
    _ = (C + 785) * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 := by ring

theorem candidate_main152
    (HF : HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151)
    (HM : LargePhaseMangoldtCancellation) : MainStatement :=
  SourceBoundary151.candidate_main151 HF (large_phase_sampling_of_mangoldt HM)

theorem positive_lower_density152
    (HF : HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151)
    (HM : LargePhaseMangoldtCancellation) : PositiveLowerDensity D6 :=
  SourceBoundary151.positive_lower_density151 HF (large_phase_sampling_of_mangoldt HM)

#check candidate_main152
#print axioms candidate_main152
run_cmd do
  for target in [``primePower_error_budget, ``prime_sum_from_log5_prefixes,
      ``large_phase_sampling_of_mangoldt, ``candidate_main152, ``positive_lower_density152] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.MangoldtClosure152
end

end Update152_Component_22
/- END COMPONENT: MangoldtClosure152.lean -/

/- BEGIN COMPONENT: ReciprocalAllOrderShape152.lean -/
section Update152_Component_23



set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set

namespace Erdos374.ReciprocalPhaseShape152
open ReciprocalPhase147 HigherDifference152

def realDifference : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | r + 1, f => realIncrement (realDifference r f)

theorem realDifference_hasDerivAt (r : ℕ) {f g : ℝ → ℝ} {a x : ℝ}
    (hd : ∀ t ∈ Ici a, HasDerivAt f (g t) t) (hx : a ≤ x) :
    HasDerivAt (realDifference r f) (realDifference r g x) x := by
  induction r generalizing x with
  | zero => exact hd x hx
  | succ r ih => exact realIncrement_hasDerivAt (fun _ ht => ih ht) hx

/-- Repeated mean value theorem, including order zero and both endpoints. -/
theorem exists_realDifference_eq (r : ℕ) (F : ℕ → ℝ → ℝ) {a x : ℝ}
    (hd : ∀ j t, t ∈ Ici a → HasDerivAt (F j) (F (j + 1) t) t) (hx : a ≤ x) :
    ∃ z ∈ Icc x (x + r), realDifference r (F 0) x = F r z := by
  induction r generalizing F x with
  | zero => exact ⟨x, by simp, rfl⟩
  | succ r ih =>
    obtain ⟨y, hy, hey⟩ := exists_hasDerivAt_eq_slope
      (realDifference r (F 0)) (realDifference r (F 1))
      (show x < x + 1 by linarith)
      (fun t ht => (realDifference_hasDerivAt r (hd 0) (hx.trans ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => realDifference_hasDerivAt r (hd 0) (hx.trans ht.1.le))
    obtain ⟨z, hz, hez⟩ := ih (fun j => F (j + 1))
      (fun j t ht => hd (j + 1) t ht) (hx.trans hy.1.le)
    refine ⟨z, ⟨hy.1.le.trans hz.1, ?_⟩, ?_⟩
    · push_cast
      linarith [hy.2, hz.2]
    · simp only [show x + 1 - x = 1 by ring, div_one] at hey
      exact hey.symm.trans hez

theorem realDifference_antitone (r : ℕ) (F : ℕ → ℝ → ℝ) {a : ℝ}
    (hd : ∀ j t, t ∈ Ici a → HasDerivAt (F j) (F (j + 1) t) t)
    (hm : AntitoneOn (F r) (Ici a)) : AntitoneOn (realDifference r (F 0)) (Ici a) := by
  induction r generalizing F with
  | zero => exact hm
  | succ r ih =>
    exact realIncrement_antitone_of_deriv_antitone
      (fun _ ht => realDifference_hasDerivAt r (hd 0) ht)
      (ih (fun j => F (j + 1)) (fun j t ht => hd (j + 1) t ht) hm)

theorem difference_sequence_eq_real (r : ℕ) (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    difference r (fun k => f (a + k)) n = realDifference r f (a + n) := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    simp only [difference, SecondDerivative151.increment, realDifference, realIncrement,
      ih, Nat.cast_add, Nat.cast_one, ← add_assoc]

theorem derivativeFormula_zero_eq (u v : ℝ) : derivativeFormula 0 u v = phase u v := by
  funext t
  simp [derivativeFormula, phase]

theorem difference_sequencePhase_eq_real (r : ℕ) (a u v : ℝ) (n : ℕ) :
    difference r (sequencePhase a u v) n = realDifference r (phase u v) (a + n) :=
  difference_sequence_eq_real r (phase u v) a n

theorem exists_difference_derivativeFormula (r : ℕ) (a u v : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ z ∈ Icc (a + n) (a + n + r),
      difference r (sequencePhase a u v) n = derivativeFormula r u v z := by
  obtain ⟨z, hz, hez⟩ := exists_realDifference_eq r (fun j => derivativeFormula j u v)
    (fun j t ht => derivativeFormula_hasDerivAt j u v t (ha.trans_le ht).ne')
    (show a ≤ a + n by linarith [Nat.cast_nonneg (α := ℝ) n])
  refine ⟨z, hz, ?_⟩
  rw [difference_sequencePhase_eq_real]
  simpa only [derivativeFormula_zero_eq] using hez

theorem derivativeFormula_oriented (r : ℕ) (u v t : ℝ) (ht : t ≠ 0) :
    derivativeFormula r ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v) t =
      (r.factorial : ℝ) / t ^ (r + 1) * normalized r u v t := by
  rw [derivativeFormula_factor r _ _ t ht]
  have hs : (-1 : ℝ) ^ r * (-1 : ℝ) ^ r = 1 := by rw [← mul_pow]; norm_num
  unfold normalized
  calc
    _ = ((-1 : ℝ) ^ r * (-1 : ℝ) ^ r) *
        ((r.factorial : ℝ) / t ^ (r + 1) * (u + ((r : ℝ) + 1) * v / t)) := by push_cast; ring
    _ = _ := by rw [hs, one_mul]; push_cast; ring

theorem next_derivativeFormula_oriented (r : ℕ) (u v t : ℝ) (ht : t ≠ 0) :
    derivativeFormula (r + 1) ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v) t =
      -((r + 1).factorial : ℝ) / t ^ (r + 2) * normalized (r + 1) u v t := by
  rw [derivativeFormula_factor (r + 1) _ _ t ht]
  have hs : (-1 : ℝ) ^ r * (-1 : ℝ) ^ r = 1 := by rw [← mul_pow]; norm_num
  unfold normalized
  rw [pow_succ]
  calc
    _ = -((-1 : ℝ) ^ r * (-1 : ℝ) ^ r) *
        (((r + 1).factorial : ℝ) / t ^ (r + 2) * (u + ((r : ℝ) + 2) * v / t)) := by
      push_cast
      ring
    _ = _ := by rw [hs]; push_cast; ring

theorem oriented_derivative_bounds (r : ℕ) (a u v t : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (ht : a ≤ t) (hdom : 2 * ((r + 1 : ℕ) : ℝ) * |v| ≤ u * a) :
    (r.factorial : ℝ) * u / (2 * t ^ (r + 1)) ≤
        derivativeFormula r ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v) t ∧
      derivativeFormula r ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v) t ≤
        3 * (r.factorial : ℝ) * u / (2 * t ^ (r + 1)) := by
  have ht0 := ha.trans_le ht
  have hn := normalized_signed_bounds r u v t ht0
    (hdom.trans (mul_le_mul_of_nonneg_left ht hu))
  rw [derivativeFormula_oriented r u v t ht0.ne']
  constructor
  · convert mul_le_mul_of_nonneg_left hn.1
      (by positivity : 0 ≤ (r.factorial : ℝ) / t ^ (r + 1)) using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hn.2
      (by positivity : 0 ≤ (r.factorial : ℝ) / t ^ (r + 1)) using 1 <;> ring

theorem oriented_derivative_antitone (r : ℕ) (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 2 * ((r + 1 : ℕ) : ℝ) * |v| ≤ u * a) :
    AntitoneOn (derivativeFormula r ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v)) (Ici a) := by
  have hn : ∀ t ∈ Ici a, 0 ≤ normalized (r + 1) u v t := by
    intro t ht
    apply normalized_nonneg (r + 1) u v t (ha.trans_le ht)
    have ht' : u * a ≤ u * t := mul_le_mul_of_nonneg_left ht hu
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hv := abs_nonneg v
    push_cast at hdom ⊢
    nlinarith
  apply antitoneOn_of_deriv_nonpos (convex_Ici a)
  · intro t ht
    exact (derivativeFormula_hasDerivAt r _ _ t (ha.trans_le ht).ne').continuousAt.continuousWithinAt
  · intro t ht
    exact (derivativeFormula_hasDerivAt r _ _ t
      (ha.trans_le (interior_subset ht)).ne').differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0 < t := ha.trans_le (interior_subset ht)
    rw [(derivativeFormula_hasDerivAt r _ _ t (ha.trans_le (interior_subset ht)).ne').deriv,
      next_derivativeFormula_oriented r u v t (ha.trans_le (interior_subset ht)).ne']
    have hc : 0 ≤ ((r + 1).factorial : ℝ) / t ^ (r + 2) := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg
      (by simpa only [neg_div] using neg_nonpos.mpr hc) (hn t (interior_subset ht))

theorem oriented_difference_antitone (r : ℕ) (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 2 * ((r + 1 : ℕ) : ℝ) * |v| ≤ u * a) :
    Antitone (difference r (sequencePhase a ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v))) := by
  have hm := realDifference_antitone r
    (fun j => derivativeFormula j ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v))
    (fun j t ht => derivativeFormula_hasDerivAt j _ _ t (ha.trans_le ht).ne')
    (oriented_derivative_antitone r a u v ha hu hdom)
  rw [derivativeFormula_zero_eq] at hm
  intro m n hmn
  rw [difference_sequencePhase_eq_real, difference_sequencePhase_eq_real]
  exact hm (by change a ≤ a + m; linarith [Nat.cast_nonneg (α := ℝ) m])
    (by change a ≤ a + n; linarith [Nat.cast_nonneg (α := ℝ) n])
    (add_le_add (le_refl a) (Nat.cast_le.mpr hmn))

/-- Every fixed finite-difference order is controlled by the actual phase,
with a quantitative bound and no assumed finite-difference shape premise. -/
theorem oriented_difference_bounds (r : ℕ) (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 2 * ((r + 1 : ℕ) : ℝ) * |v| ≤ u * a) (N n : ℕ) (hn : n < N) :
    (r.factorial : ℝ) * u / (2 * (a + (N : ℝ) + r) ^ (r + 1)) ≤
        difference r (sequencePhase a ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v)) n ∧
      difference r (sequencePhase a ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v)) n ≤
        3 * (r.factorial : ℝ) * u / (2 * a ^ (r + 1)) := by
  obtain ⟨z, hz, hez⟩ := exists_difference_derivativeFormula r a
    ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v) ha n
  rw [hez]
  have haz : a ≤ z := by linarith [hz.1, Nat.cast_nonneg (α := ℝ) n]
  have hz0 : 0 < z := ha.trans_le haz
  have hzN : z ≤ a + (N : ℝ) + r := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    linarith [hz.2]
  have hb := oriented_derivative_bounds r a u v z ha hu haz hdom
  constructor
  · exact (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0.le hzN (r + 1)) (by norm_num))).trans hb.1
  · exact hb.2.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le haz (r + 1)) (by norm_num)))

#print axioms oriented_difference_bounds
#print axioms oriented_difference_antitone

run_cmd do
  for target in [``exists_realDifference_eq, ``realDifference_antitone,
      ``oriented_difference_bounds, ``oriented_difference_antitone] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end

end Update152_Component_23
/- END COMPONENT: ReciprocalAllOrderShape152.lean -/

/- BEGIN COMPONENT: ReciprocalAllOrderSquare152.lean -/
section Update152_Component_24



set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Set
open scoped BigOperators

namespace Erdos374.ReciprocalPhaseShape152
open ReciprocalPhase147 HigherDifference152

theorem norm_sum_sequencePhase_oriented (r : ℕ) (a u v : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e
      (sequencePhase a ((-1 : ℝ) ^ r * u) ((-1 : ℝ) ^ r * v) n)‖ =
      ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a u v n)‖ := by
  induction r with
  | zero => simp only [pow_zero, one_mul]
  | succ r ih =>
    rw [pow_succ,
      show (-1 : ℝ) ^ r * -1 * u = -((-1 : ℝ) ^ r * u) by ring,
      show (-1 : ℝ) ^ r * -1 * v = -((-1 : ℝ) ^ r * v) by ring,
      norm_sum_sequencePhase_neg, ih]

theorem square_oriented_derivativeFormula (r : ℕ) (v t : ℝ) (ht : t ≠ 0) :
    derivativeFormula r 0 ((-1 : ℝ) ^ r * v) t =
      ((r + 1).factorial : ℝ) * v / t ^ (r + 2) := by
  have h := derivativeFormula_oriented r 0 v t ht
  simp only [mul_zero] at h
  rw [h]
  unfold normalized
  rw [Nat.factorial_succ, Nat.cast_mul]
  simp only [zero_add, Nat.cast_add, Nat.cast_one,
    show r + 2 = (r + 1) + 1 by omega, pow_succ]
  field_simp
  <;> ring

theorem square_oriented_derivative_antitone (r : ℕ) (a v : ℝ)
    (ha : 0 < a) (hv : 0 ≤ v) :
    AntitoneOn (derivativeFormula r 0 ((-1 : ℝ) ^ r * v)) (Ici a) := by
  intro x hx y hy hxy
  rw [square_oriented_derivativeFormula r v x (ha.trans_le hx).ne',
    square_oriented_derivativeFormula r v y (ha.trans_le hy).ne']
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos (ha.trans_le hx) (r + 2))
    (pow_le_pow_left₀ (ha.trans_le hx).le hxy (r + 2))

theorem square_oriented_difference_antitone (r : ℕ) (a v : ℝ)
    (ha : 0 < a) (hv : 0 ≤ v) :
    Antitone (difference r (sequencePhase a 0 ((-1 : ℝ) ^ r * v))) := by
  have hm := realDifference_antitone r
    (fun j => derivativeFormula j 0 ((-1 : ℝ) ^ r * v))
    (fun j t ht => derivativeFormula_hasDerivAt j _ _ t (ha.trans_le ht).ne')
    (square_oriented_derivative_antitone r a v ha hv)
  rw [derivativeFormula_zero_eq] at hm
  intro m n hmn
  rw [difference_sequencePhase_eq_real, difference_sequencePhase_eq_real]
  exact hm (by change a ≤ a + m; linarith [Nat.cast_nonneg (α := ℝ) m])
    (by change a ≤ a + n; linarith [Nat.cast_nonneg (α := ℝ) n])
    (add_le_add (le_refl a) (Nat.cast_le.mpr hmn))

/-- The pure square axis has a positive, decreasing finite difference at every
order after parity orientation; no dominance hypothesis is needed. -/
theorem square_oriented_difference_bounds (r : ℕ) (a v : ℝ)
    (ha : 0 < a) (hv : 0 ≤ v) (N n : ℕ) (hn : n < N) :
    ((r + 1).factorial : ℝ) * v / (a + (N : ℝ) + r) ^ (r + 2) ≤
        difference r (sequencePhase a 0 ((-1 : ℝ) ^ r * v)) n ∧
      difference r (sequencePhase a 0 ((-1 : ℝ) ^ r * v)) n ≤
        ((r + 1).factorial : ℝ) * v / a ^ (r + 2) := by
  obtain ⟨z, hz, hez⟩ := exists_difference_derivativeFormula r a 0
    ((-1 : ℝ) ^ r * v) ha n
  have haz : a ≤ z := by linarith [hz.1, Nat.cast_nonneg (α := ℝ) n]
  have hz0 : 0 < z := ha.trans_le haz
  have hzN : z ≤ a + (N : ℝ) + r := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    linarith [hz.2]
  rw [hez, square_oriented_derivativeFormula r v z hz0.ne']
  constructor
  · exact div_le_div_of_nonneg_left (by positivity) (pow_pos hz0 (r + 2))
      (pow_le_pow_left₀ hz0.le hzN (r + 2))
  · exact div_le_div_of_nonneg_left (by positivity) (pow_pos ha (r + 2))
      (pow_le_pow_left₀ ha.le haz (r + 2))

#print axioms square_oriented_difference_bounds
#print axioms square_oriented_difference_antitone

run_cmd do
  for target in [``square_oriented_difference_bounds, ``square_oriented_difference_antitone,
      ``norm_sum_sequencePhase_oriented] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end

end Update152_Component_24
/- END COMPONENT: ReciprocalAllOrderSquare152.lean -/

/- BEGIN COMPONENT: ReciprocalHigherShape152.lean -/
section Update152_Component_25



set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Set

namespace Erdos374.ReciprocalPhaseShape152
open ReciprocalPhase147 HigherDifference152

theorem realThirdDifference_antitone {f g h k : ℝ → ℝ} {a : ℝ}
    (h1 : ∀ t ∈ Ici a, HasDerivAt f (g t) t)
    (h2 : ∀ t ∈ Ici a, HasDerivAt g (h t) t)
    (h3 : ∀ t ∈ Ici a, HasDerivAt h (k t) t) (hk : AntitoneOn k (Ici a)) :
    AntitoneOn (realIncrement (realIncrement (realIncrement f))) (Ici a) :=
  realSecondDifference_antitone
    (fun _ ht => realIncrement_hasDerivAt h1 ht)
    (fun _ ht => realIncrement_hasDerivAt h2 ht)
    (realIncrement_antitone_of_deriv_antitone h3 hk)

theorem exists_realThirdDifference_eq {f g h k : ℝ → ℝ} {a x : ℝ}
    (h1 : ∀ t ∈ Ici a, HasDerivAt f (g t) t)
    (h2 : ∀ t ∈ Ici a, HasDerivAt g (h t) t)
    (h3 : ∀ t ∈ Ici a, HasDerivAt h (k t) t) (hx : a ≤ x) :
    ∃ z ∈ Ioo x (x + 3), realIncrement (realIncrement (realIncrement f)) x = k z := by
  obtain ⟨y, hy, hey⟩ := exists_realSecondDifference_eq
    (fun _ ht => realIncrement_hasDerivAt h1 ht)
    (fun _ ht => realIncrement_hasDerivAt h2 ht) hx
  have hya : a ≤ y := hx.trans hy.1.le
  obtain ⟨z, hz, hez⟩ := exists_hasDerivAt_eq_slope h k
    (show y < y + 1 by linarith)
    (fun t ht => (h3 t (hya.trans ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => h3 t (hya.trans ht.1.le))
  refine ⟨z, ⟨by linarith [hy.1, hz.1], by linarith [hy.2, hz.2]⟩, ?_⟩
  simp only [show y + 1 - y = 1 by ring, div_one] at hez
  exact hey.trans hez.symm

theorem derivativeFormula_neg (j : ℕ) (u v t : ℝ) :
    derivativeFormula j (-u) (-v) t = -derivativeFormula j u v t := by
  unfold derivativeFormula
  ring

theorem negative_thirdDerivative_bounds (a u v t : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (ht : a ≤ t) (hdom : 8 * |v| ≤ u * a) :
    3 * u / t ^ 4 ≤ derivativeFormula 3 (-u) (-v) t ∧
      derivativeFormula 3 (-u) (-v) t ≤ 9 * u / t ^ 4 := by
  have ht0 : 0 < t := ha.trans_le ht
  have hdomt : 8 * |v| ≤ u * t := hdom.trans (mul_le_mul_of_nonneg_left ht hu)
  have hnorm := normalized_signed_bounds 3 u v t ht0 (by norm_num; exact hdomt)
  rw [derivativeFormula_neg, derivativeFormula_factor 3 u v t ht0.ne']
  norm_num
  constructor
  · convert mul_le_mul_of_nonneg_left hnorm.1 (by positivity : 0 ≤ (6 : ℝ) / t ^ 4) using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hnorm.2 (by positivity : 0 ≤ (6 : ℝ) / t ^ 4) using 1 <;> ring

theorem negative_fourthDerivative_nonpos (a u v t : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (ht : a ≤ t) (hdom : 8 * |v| ≤ u * a) : derivativeFormula 4 (-u) (-v) t ≤ 0 := by
  have ht0 : 0 < t := ha.trans_le ht
  have hdomt : 8 * |v| ≤ u * t := hdom.trans (mul_le_mul_of_nonneg_left ht hu)
  have hn : 0 ≤ normalized 4 u v t :=
    normalized_nonneg 4 u v t ht0 (by norm_num; linarith [abs_nonneg v])
  rw [derivativeFormula_neg, derivativeFormula_factor 4 u v t ht0.ne']
  apply neg_nonpos.mpr
  apply mul_nonneg _ hn
  positivity

theorem negative_thirdDerivative_antitone (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 8 * |v| ≤ u * a) : AntitoneOn (derivativeFormula 3 (-u) (-v)) (Ici a) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici a)
  · intro t ht
    exact (derivativeFormula_hasDerivAt 3 (-u) (-v) t (ha.trans_le ht).ne').continuousAt.continuousWithinAt
  · intro t ht
    exact (derivativeFormula_hasDerivAt 3 (-u) (-v) t (ha.trans_le (interior_subset ht)).ne').differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(derivativeFormula_hasDerivAt 3 (-u) (-v) t (ha.trans_le (interior_subset ht)).ne').deriv]
    exact negative_fourthDerivative_nonpos a u v t ha hu (interior_subset ht) hdom

theorem thirdDifference_eq_real (a u v : ℝ) (n : ℕ) :
    difference 3 (sequencePhase a u v) n =
      realIncrement (realIncrement (realIncrement (phase u v))) (a + n) := by
  simp only [difference, SecondDerivative151.increment, sequencePhase, realIncrement,
    Nat.cast_add, Nat.cast_one, ← add_assoc]

theorem negative_thirdDifference_antitone (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 8 * |v| ≤ u * a) : Antitone (difference 3 (sequencePhase a (-u) (-v))) := by
  have hm := realThirdDifference_antitone
    (fun t ht => phase_hasDerivAt (-u) (-v) t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 1 (-u) (-v) t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 2 (-u) (-v) t (ha.trans_le ht).ne')
    (negative_thirdDerivative_antitone a u v ha hu hdom)
  intro m n hmn
  rw [thirdDifference_eq_real, thirdDifference_eq_real]
  exact hm (by change a ≤ a + m; linarith [Nat.cast_nonneg (α := ℝ) m])
    (by change a ≤ a + n; linarith [Nat.cast_nonneg (α := ℝ) n])
    (add_le_add (le_refl a) (Nat.cast_le.mpr hmn))

theorem negative_thirdDifference_bounds (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hdom : 8 * |v| ≤ u * a) (N n : ℕ) (hn : n < N) :
    3 * u / (a + (N : ℝ) + 3) ^ 4 ≤ difference 3 (sequencePhase a (-u) (-v)) n ∧
      difference 3 (sequencePhase a (-u) (-v)) n ≤ 9 * u / a ^ 4 := by
  obtain ⟨z, hz, heq⟩ := exists_realThirdDifference_eq
    (fun t ht => phase_hasDerivAt (-u) (-v) t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 1 (-u) (-v) t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 2 (-u) (-v) t (ha.trans_le ht).ne')
    (show a ≤ a + n by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [thirdDifference_eq_real, heq]
  have haz : a ≤ z := by linarith [hz.1, Nat.cast_nonneg (α := ℝ) n]
  have hz0 : 0 < z := ha.trans_le haz
  have hzN : z ≤ a + (N : ℝ) + 3 := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    linarith [hz.2]
  have hb := negative_thirdDerivative_bounds a u v z ha hu haz hdom
  constructor
  · exact (div_le_div_of_nonneg_left (by positivity) (pow_pos hz0 4)
      (pow_le_pow_left₀ hz0.le hzN 4)).trans hb.1
  · exact hb.2.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos ha 4)
      (pow_le_pow_left₀ ha.le haz 4))

theorem square_negative_thirdDerivative (v t : ℝ) :
    derivativeFormula 3 0 (-v) t = 24 * v / t ^ 5 := by
  norm_num [derivativeFormula, Nat.factorial]
  ring

theorem square_negative_thirdDerivative_antitone (a v : ℝ) (ha : 0 < a) (hv : 0 ≤ v) :
    AntitoneOn (derivativeFormula 3 0 (-v)) (Ici a) := by
  intro x hx y hy hxy
  rw [square_negative_thirdDerivative, square_negative_thirdDerivative]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos (ha.trans_le hx) 5)
    (pow_le_pow_left₀ (ha.trans_le hx).le hxy 5)

theorem square_negative_thirdDifference_antitone (a v : ℝ) (ha : 0 < a) (hv : 0 ≤ v) :
    Antitone (difference 3 (sequencePhase a 0 (-v))) := by
  have hm := realThirdDifference_antitone
    (fun t ht => phase_hasDerivAt 0 (-v) t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 1 0 (-v) t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 2 0 (-v) t (ha.trans_le ht).ne')
    (square_negative_thirdDerivative_antitone a v ha hv)
  intro m n hmn
  rw [thirdDifference_eq_real, thirdDifference_eq_real]
  exact hm (by change a ≤ a + m; linarith [Nat.cast_nonneg (α := ℝ) m])
    (by change a ≤ a + n; linarith [Nat.cast_nonneg (α := ℝ) n])
    (add_le_add (le_refl a) (Nat.cast_le.mpr hmn))

theorem square_negative_thirdDifference_bounds (a v : ℝ) (ha : 0 < a) (hv : 0 ≤ v)
    (N n : ℕ) (hn : n < N) :
    24 * v / (a + (N : ℝ) + 3) ^ 5 ≤ difference 3 (sequencePhase a 0 (-v)) n ∧
      difference 3 (sequencePhase a 0 (-v)) n ≤ 24 * v / a ^ 5 := by
  obtain ⟨z, hz, heq⟩ := exists_realThirdDifference_eq
    (fun t ht => phase_hasDerivAt 0 (-v) t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 1 0 (-v) t (ha.trans_le ht).ne')
    (fun t ht => derivativeFormula_hasDerivAt 2 0 (-v) t (ha.trans_le ht).ne')
    (show a ≤ a + n by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [thirdDifference_eq_real, heq, square_negative_thirdDerivative]
  have haz : a ≤ z := by linarith [hz.1, Nat.cast_nonneg (α := ℝ) n]
  have hz0 : 0 < z := ha.trans_le haz
  have hzN : z ≤ a + (N : ℝ) + 3 := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    linarith [hz.2]
  constructor
  · exact div_le_div_of_nonneg_left (by positivity) (pow_pos hz0 5)
      (pow_le_pow_left₀ hz0.le hzN 5)
  · exact div_le_div_of_nonneg_left (by positivity) (pow_pos ha 5)
      (pow_le_pow_left₀ ha.le haz 5)

#print axioms negative_thirdDifference_bounds
#print axioms negative_thirdDifference_antitone
#print axioms square_negative_thirdDifference_bounds
#print axioms square_negative_thirdDifference_antitone

run_cmd do
  for target in [``negative_thirdDifference_bounds, ``negative_thirdDifference_antitone,
      ``square_negative_thirdDifference_bounds, ``square_negative_thirdDifference_antitone] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end


end Update152_Component_25
/- END COMPONENT: ReciprocalHigherShape152.lean -/

/- BEGIN COMPONENT: ReciprocalWindow152.lean -/
section Update152_Component_26



set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Erdos374.ReciprocalPhaseShape152
open HigherDifference152 HigherDifferenceWindow152

def reciprocalLower (k N : ℕ) (a u : ℝ) : ℝ :=
  (k.factorial : ℝ) * |u| / (2 * (a + (N : ℝ) + k) ^ (k + 1))

def reciprocalRatio (k N : ℕ) (a : ℝ) : ℝ :=
  3 * (a + (N : ℝ) + k) ^ (k + 1) / a ^ (k + 1)

def squareLower (k N : ℕ) (a v : ℝ) : ℝ :=
  ((k + 1).factorial : ℝ) * |v| / (a + (N : ℝ) + k) ^ (k + 2)

def squareRatio (k N : ℕ) (a : ℝ) : ℝ :=
  (a + (N : ℝ) + k) ^ (k + 2) / a ^ (k + 2)

theorem order_ratio_ge_one (a K : ℝ) (ha : 0 < a) (hK : 1 ≤ K) (N k p : ℕ) :
    1 ≤ K * (a + (N : ℝ) + k) ^ p / a ^ p := by
  have he : a ≤ a + (N : ℝ) + k := by
    linarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) k]
  have hp := pow_le_pow_left₀ ha.le he p
  apply (le_div_iff₀ (pow_pos ha p)).mpr
  have ht : 0 ≤ (a + (N : ℝ) + k) ^ p := by positivity
  nlinarith

theorem reciprocal_window_positive (r N H Q : ℕ) (a u v Llo Lhi ε : ℝ)
    (ha : 0 < a) (hu : 0 < u)
    (hdom : 2 * ((r + 3 : ℕ) : ℝ) * |v| ≤ u * a)
    (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * reciprocalLower (r + 2) N a u ≤ Lhi)
    (hlower : Llo ≤ (Q : ℝ) ^ r * reciprocalLower (r + 2) N a u)
    (hbase : 32 * reciprocalRatio (r + 2) N a * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤ ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a u v n)‖ ≤ 10 * ε * (N : ℝ) := by
  have hL : 0 < reciprocalLower (r + 2) N a u := by
    unfold reciprocalLower
    positivity
  have hC : 1 ≤ reciprocalRatio (r + 2) N a :=
    order_ratio_ge_one a 3 ha (by norm_num) N (r + 2) ((r + 2) + 1)
  have hd : ∀ n < N, reciprocalLower (r + 2) N a u ≤
        difference (r + 2) (sequencePhase a ((-1 : ℝ) ^ (r + 2) * u) ((-1 : ℝ) ^ (r + 2) * v)) n ∧
      difference (r + 2) (sequencePhase a ((-1 : ℝ) ^ (r + 2) * u) ((-1 : ℝ) ^ (r + 2) * v)) n ≤
        reciprocalRatio (r + 2) N a * reciprocalLower (r + 2) N a u := by
    intro n hn
    have hb := oriented_difference_bounds (r + 2) a u v ha hu.le hdom N n hn
    refine ⟨by simpa only [reciprocalLower, abs_of_pos hu] using hb.1, hb.2.trans_eq ?_⟩
    unfold reciprocalLower reciprocalRatio
    rw [abs_of_pos hu]
    have he : a + (N : ℝ) + (r + 2 : ℕ) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hm : Antitone (difference (r + 2)
      (sequencePhase a ((-1 : ℝ) ^ (r + 2) * u) ((-1 : ℝ) ^ (r + 2) * v))) :=
    oriented_difference_antitone (r + 2) a u v ha hu.le hdom
  have hs := cancellation_of_window r N N H Q
    (sequencePhase a ((-1 : ℝ) ^ (r + 2) * u) ((-1 : ℝ) ^ (r + 2) * v))
    (reciprocalLower (r + 2) N a u) (reciprocalRatio (r + 2) N a) Llo Lhi ε
    le_rfl hH hQ hHN hL hC hlo hε hε1 hupper hlower hbase hdiag hdiscard hd
    (Or.inr (fun _ _ _ _ h => hm h))
  rwa [norm_sum_sequencePhase_oriented] at hs

/-- All-order cancellation for the actual signed reciprocal phase. The remaining
premises are explicit numerical shift budgets; no character-sum or phase-shape
estimate is assumed. -/
theorem reciprocal_window (r N H Q : ℕ) (a u v Llo Lhi ε : ℝ)
    (ha : 0 < a) (hu : u ≠ 0)
    (hdom : 2 * ((r + 3 : ℕ) : ℝ) * |v| ≤ |u| * a)
    (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * reciprocalLower (r + 2) N a u ≤ Lhi)
    (hlower : Llo ≤ (Q : ℝ) ^ r * reciprocalLower (r + 2) N a u)
    (hbase : 32 * reciprocalRatio (r + 2) N a * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤ ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a u v n)‖ ≤ 10 * ε * (N : ℝ) := by
  by_cases hpos : 0 ≤ u
  · exact reciprocal_window_positive r N H Q a u v Llo Lhi ε ha
      (lt_of_le_of_ne hpos hu.symm) (by simpa only [abs_of_nonneg hpos] using hdom)
      hH hQ hHN hlo hε hε1 hupper hlower hbase hdiag hdiscard
  · have hneg : u < 0 := lt_of_not_ge hpos
    have hs := reciprocal_window_positive r N H Q a (-u) (-v) Llo Lhi ε ha
      (by linarith) (by simpa only [abs_neg, abs_of_neg hneg] using hdom)
      hH hQ hHN hlo hε hε1
      (by simpa only [reciprocalLower, abs_neg] using hupper)
      (by simpa only [reciprocalLower, abs_neg] using hlower) hbase hdiag hdiscard
    rwa [norm_sum_sequencePhase_neg] at hs

theorem square_window_positive (r N H Q : ℕ) (a v Llo Lhi ε : ℝ)
    (ha : 0 < a) (hv : 0 < v)
    (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * squareLower (r + 2) N a v ≤ Lhi)
    (hlower : Llo ≤ (Q : ℝ) ^ r * squareLower (r + 2) N a v)
    (hbase : 32 * squareRatio (r + 2) N a * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤ ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a 0 v n)‖ ≤ 10 * ε * (N : ℝ) := by
  have hL : 0 < squareLower (r + 2) N a v := by unfold squareLower; positivity
  have hC : 1 ≤ squareRatio (r + 2) N a := by
    simpa only [squareRatio, one_mul] using
      order_ratio_ge_one a 1 ha (by norm_num) N (r + 2) ((r + 2) + 2)
  have hd : ∀ n < N, squareLower (r + 2) N a v ≤
        difference (r + 2) (sequencePhase a 0 ((-1 : ℝ) ^ (r + 2) * v)) n ∧
      difference (r + 2) (sequencePhase a 0 ((-1 : ℝ) ^ (r + 2) * v)) n ≤
        squareRatio (r + 2) N a * squareLower (r + 2) N a v := by
    intro n hn
    have hb := square_oriented_difference_bounds (r + 2) a v ha hv.le N n hn
    refine ⟨by simpa only [squareLower, abs_of_pos hv] using hb.1, hb.2.trans_eq ?_⟩
    unfold squareLower squareRatio
    rw [abs_of_pos hv]
    have he : a + (N : ℝ) + (r + 2 : ℕ) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hm := square_oriented_difference_antitone (r + 2) a v ha hv.le
  have hs := cancellation_of_window r N N H Q
    (sequencePhase a 0 ((-1 : ℝ) ^ (r + 2) * v))
    (squareLower (r + 2) N a v) (squareRatio (r + 2) N a) Llo Lhi ε
    le_rfl hH hQ hHN hL hC hlo hε hε1 hupper hlower hbase hdiag hdiscard hd
    (Or.inr (fun _ _ _ _ h => hm h))
  have he := norm_sum_sequencePhase_oriented (r + 2) a 0 v N
  simp only [mul_zero] at he
  rwa [he] at hs

/-- The all-order numerical-window theorem on the pure reciprocal-square axis,
including both signs and with no reciprocal-dominance premise. -/
theorem square_window (r N H Q : ℕ) (a v Llo Lhi ε : ℝ)
    (ha : 0 < a) (hv : v ≠ 0)
    (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * squareLower (r + 2) N a v ≤ Lhi)
    (hlower : Llo ≤ (Q : ℝ) ^ r * squareLower (r + 2) N a v)
    (hbase : 32 * squareRatio (r + 2) N a * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤ ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r)) :
    ‖∑ n ∈ Finset.range N, KusminLandau151.e (sequencePhase a 0 v n)‖ ≤ 10 * ε * (N : ℝ) := by
  by_cases hpos : 0 ≤ v
  · exact square_window_positive r N H Q a v Llo Lhi ε ha
      (lt_of_le_of_ne hpos hv.symm) hH hQ hHN hlo hε hε1 hupper hlower hbase hdiag hdiscard
  · have hneg : v < 0 := lt_of_not_ge hpos
    have hs := square_window_positive r N H Q a (-v) Llo Lhi ε ha
      (by linarith) hH hQ hHN hlo hε hε1
      (by simpa only [squareLower, abs_neg] using hupper)
      (by simpa only [squareLower, abs_neg] using hlower) hbase hdiag hdiscard
    have he := norm_sum_sequencePhase_neg a 0 v N
    simp only [neg_zero] at he
    rwa [he] at hs

#print axioms reciprocal_window
#print axioms square_window

run_cmd do
  for target in [``reciprocal_window, ``square_window] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end

end Update152_Component_26
/- END COMPONENT: ReciprocalWindow152.lean -/

/- BEGIN COMPONENT: ReciprocalWindowPrefix152.lean -/
section Update152_Component_27



set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Erdos374.ReciprocalPhaseShape152
open HigherDifference152 HigherDifferenceWindow152

theorem reciprocal_positive_on_prefix (r M N H Q : ℕ) (a u v Llo Lhi ε : ℝ)
    (ha : 0 < a) (hu : 0 < u)
    (hdom : 2 * ((r + 3 : ℕ) : ℝ) * |v| ≤ u * a)
    (hM : M ≤ N) (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * reciprocalLower (r + 2) N a u ≤ Lhi)
    (hlower : Llo ≤ (Q : ℝ) ^ r * reciprocalLower (r + 2) N a u)
    (hbase : 32 * reciprocalRatio (r + 2) N a * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤ ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r)) :
    ‖∑ n ∈ Finset.range M, KusminLandau151.e (sequencePhase a u v n)‖ ≤ 10 * ε * (N : ℝ) := by
  have hL : 0 < reciprocalLower (r + 2) N a u := by
    unfold reciprocalLower
    positivity
  have hC : 1 ≤ reciprocalRatio (r + 2) N a :=
    order_ratio_ge_one a 3 ha (by norm_num) N (r + 2) ((r + 2) + 1)
  have hd : ∀ n < M, reciprocalLower (r + 2) N a u ≤
        difference (r + 2) (sequencePhase a ((-1 : ℝ) ^ (r + 2) * u) ((-1 : ℝ) ^ (r + 2) * v)) n ∧
      difference (r + 2) (sequencePhase a ((-1 : ℝ) ^ (r + 2) * u) ((-1 : ℝ) ^ (r + 2) * v)) n ≤
        reciprocalRatio (r + 2) N a * reciprocalLower (r + 2) N a u := by
    intro n hn
    have hb := oriented_difference_bounds (r + 2) a u v ha hu.le hdom N n (hn.trans_le hM)
    refine ⟨by simpa only [reciprocalLower, abs_of_pos hu] using hb.1, hb.2.trans_eq ?_⟩
    unfold reciprocalLower reciprocalRatio
    rw [abs_of_pos hu]
    have he : a + (N : ℝ) + (r + 2 : ℕ) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hm : Antitone (difference (r + 2)
      (sequencePhase a ((-1 : ℝ) ^ (r + 2) * u) ((-1 : ℝ) ^ (r + 2) * v))) :=
    oriented_difference_antitone (r + 2) a u v ha hu.le hdom
  have hs := cancellation_of_window r M N H Q
    (sequencePhase a ((-1 : ℝ) ^ (r + 2) * u) ((-1 : ℝ) ^ (r + 2) * v))
    (reciprocalLower (r + 2) N a u) (reciprocalRatio (r + 2) N a) Llo Lhi ε
    hM hH hQ hHN hL hC hlo hε hε1 hupper hlower hbase hdiag hdiscard hd
    (Or.inr (fun _ _ _ _ h => hm h))
  rwa [norm_sum_sequencePhase_oriented] at hs

/-- All-order cancellation for the actual signed reciprocal phase. The remaining
premises are explicit numerical shift budgets; no character-sum or phase-shape
estimate is assumed. -/
theorem reciprocal_on_prefix (r M N H Q : ℕ) (a u v Llo Lhi ε : ℝ)
    (ha : 0 < a) (hu : u ≠ 0)
    (hdom : 2 * ((r + 3 : ℕ) : ℝ) * |v| ≤ |u| * a)
    (hM : M ≤ N) (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * reciprocalLower (r + 2) N a u ≤ Lhi)
    (hlower : Llo ≤ (Q : ℝ) ^ r * reciprocalLower (r + 2) N a u)
    (hbase : 32 * reciprocalRatio (r + 2) N a * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤ ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r)) :
    ‖∑ n ∈ Finset.range M, KusminLandau151.e (sequencePhase a u v n)‖ ≤ 10 * ε * (N : ℝ) := by
  by_cases hpos : 0 ≤ u
  · exact reciprocal_positive_on_prefix r M N H Q a u v Llo Lhi ε ha
      (lt_of_le_of_ne hpos hu.symm) (by simpa only [abs_of_nonneg hpos] using hdom)
      hM hH hQ hHN hlo hε hε1 hupper hlower hbase hdiag hdiscard
  · have hneg : u < 0 := lt_of_not_ge hpos
    have hs := reciprocal_positive_on_prefix r M N H Q a (-u) (-v) Llo Lhi ε ha
      (by linarith) (by simpa only [abs_neg, abs_of_neg hneg] using hdom)
      hM hH hQ hHN hlo hε hε1
      (by simpa only [reciprocalLower, abs_neg] using hupper)
      (by simpa only [reciprocalLower, abs_neg] using hlower) hbase hdiag hdiscard
    rwa [norm_sum_sequencePhase_neg] at hs

theorem square_positive_on_prefix (r M N H Q : ℕ) (a v Llo Lhi ε : ℝ)
    (ha : 0 < a) (hv : 0 < v)
    (hM : M ≤ N) (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * squareLower (r + 2) N a v ≤ Lhi)
    (hlower : Llo ≤ (Q : ℝ) ^ r * squareLower (r + 2) N a v)
    (hbase : 32 * squareRatio (r + 2) N a * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤ ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r)) :
    ‖∑ n ∈ Finset.range M, KusminLandau151.e (sequencePhase a 0 v n)‖ ≤ 10 * ε * (N : ℝ) := by
  have hL : 0 < squareLower (r + 2) N a v := by unfold squareLower; positivity
  have hC : 1 ≤ squareRatio (r + 2) N a := by
    simpa only [squareRatio, one_mul] using
      order_ratio_ge_one a 1 ha (by norm_num) N (r + 2) ((r + 2) + 2)
  have hd : ∀ n < M, squareLower (r + 2) N a v ≤
        difference (r + 2) (sequencePhase a 0 ((-1 : ℝ) ^ (r + 2) * v)) n ∧
      difference (r + 2) (sequencePhase a 0 ((-1 : ℝ) ^ (r + 2) * v)) n ≤
        squareRatio (r + 2) N a * squareLower (r + 2) N a v := by
    intro n hn
    have hb := square_oriented_difference_bounds (r + 2) a v ha hv.le N n (hn.trans_le hM)
    refine ⟨by simpa only [squareLower, abs_of_pos hv] using hb.1, hb.2.trans_eq ?_⟩
    unfold squareLower squareRatio
    rw [abs_of_pos hv]
    have he : a + (N : ℝ) + (r + 2 : ℕ) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hm := square_oriented_difference_antitone (r + 2) a v ha hv.le
  have hs := cancellation_of_window r M N H Q
    (sequencePhase a 0 ((-1 : ℝ) ^ (r + 2) * v))
    (squareLower (r + 2) N a v) (squareRatio (r + 2) N a) Llo Lhi ε
    hM hH hQ hHN hL hC hlo hε hε1 hupper hlower hbase hdiag hdiscard hd
    (Or.inr (fun _ _ _ _ h => hm h))
  have he := norm_sum_sequencePhase_oriented (r + 2) a 0 v M
  simp only [mul_zero] at he
  rwa [he] at hs

/-- The all-order numerical-window theorem on the pure reciprocal-square axis,
including both signs and with no reciprocal-dominance premise. -/
theorem square_on_prefix (r M N H Q : ℕ) (a v Llo Lhi ε : ℝ)
    (ha : 0 < a) (hv : v ≠ 0)
    (hM : M ≤ N) (hH : 0 < H) (hQ : 0 < Q) (hHN : H ≤ N)
    (hlo : 0 < Llo) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hupper : (H : ℝ) ^ r * squareLower (r + 2) N a v ≤ Lhi)
    (hlower : Llo ≤ (Q : ℝ) ^ r * squareLower (r + 2) N a v)
    (hbase : 32 * squareRatio (r + 2) N a * (1 + Real.log ((N : ℝ) + 1)) *
        ((N : ℝ) ^ 2 * Lhi + 1 / Llo) ≤ ε ^ (2 ^ (r + 1)) * (N : ℝ) ^ 2)
    (hdiag : 1 / (H : ℝ) ≤ ε ^ (2 ^ r))
    (hdiscard : (Q : ℝ) / H ≤ ε ^ (2 ^ r)) :
    ‖∑ n ∈ Finset.range M, KusminLandau151.e (sequencePhase a 0 v n)‖ ≤ 10 * ε * (N : ℝ) := by
  by_cases hpos : 0 ≤ v
  · exact square_positive_on_prefix r M N H Q a v Llo Lhi ε ha
      (lt_of_le_of_ne hpos hv.symm) hM hH hQ hHN hlo hε hε1 hupper hlower hbase hdiag hdiscard
  · have hneg : v < 0 := lt_of_not_ge hpos
    have hs := square_positive_on_prefix r M N H Q a (-v) Llo Lhi ε ha
      (by linarith) hM hH hQ hHN hlo hε hε1
      (by simpa only [squareLower, abs_neg] using hupper)
      (by simpa only [squareLower, abs_neg] using hlower) hbase hdiag hdiscard
    have he := norm_sum_sequencePhase_neg a 0 v M
    simp only [neg_zero] at he
    rwa [he] at hs

#print axioms reciprocal_on_prefix
#print axioms square_on_prefix

run_cmd do
  for target in [``reciprocal_on_prefix, ``square_on_prefix] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.ReciprocalPhaseShape152
end


end Update152_Component_27
/- END COMPONENT: ReciprocalWindowPrefix152.lean -/

/- BEGIN COMPONENT: VaughanCoefficients152.lean -/
section Update152_Component_28


/-! Bounds for the actual Vaughan coefficients used in Type I/II sums. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators

namespace Erdos374.VaughanCoefficients152
open Vaughan145

theorem low_mangoldt_bounds (V n : ℕ) :
    0 ≤ low V lam n ∧ low V lam n ≤ lam n := by
  rw [low_apply]
  split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]

/-- The actual small-small coefficient has logarithmic size, with no divisor
function loss and no assumed coefficient majorant. -/
theorem alpha_abs_le_log (U V n : ℕ) :
    |Vaughan145.alpha U V n| ≤ Real.log (n : ℝ) := by
  have hlog : zetaR * lam = ArithmeticFunction.log :=
    ArithmeticFunction.zeta_mul_vonMangoldt
  rw [Vaughan145.alpha, ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal, |low U muR x.1 * low V lam x.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal, zetaR x.1 * lam x.2 := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨hprod, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have hx0 : x.1 ≠ 0 := left_ne_zero_of_mul (hprod.symm ▸ hn)
      have hz : zetaR x.1 = 1 := by
        rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hx0]
        norm_num
      rw [abs_mul, abs_of_nonneg (low_mangoldt_bounds V x.2).1, hz, one_mul]
      calc
        _ ≤ 1 * low V lam x.2 :=
          mul_le_mul_of_nonneg_right (low_moebius_abs_le_one U x.1) (low_mangoldt_bounds V x.2).1
        _ ≤ lam x.2 := by simpa only [one_mul] using (low_mangoldt_bounds V x.2).2
    _ = (zetaR * lam) n := ArithmeticFunction.mul_apply.symm
    _ = Real.log (n : ℝ) := by rw [hlog]; rfl

theorem high_moebius_energy (s : Finset ℕ) (U : ℕ) :
    (∑ d ∈ s, ‖(high U muR d : ℂ)‖ ^ 2) ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h := high_moebius_abs_le_one U d
      nlinarith [abs_nonneg (high U muR d)]
    _ = _ := by simp

theorem beta_energy (s : Finset ℕ) (V N : ℕ) (hN : 1 ≤ N)
    (hs : ∀ k ∈ s, 1 ≤ k ∧ k ≤ N) :
    (∑ k ∈ s, ‖(beta V k : ℂ)‖ ^ 2) ≤ (s.card : ℝ) * (Real.log (N : ℝ)) ^ 2 := by
  calc
    _ ≤ ∑ _k ∈ s, (Real.log (N : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hb := beta_bounds V k
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := (hs k hk).1; omega)
      have hl : Real.log (k : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log hk0 (Nat.cast_le.mpr (hs k hk).2)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact pow_le_pow_left₀ hb.1 (hb.2.trans hl) 2
    _ = _ := by simp [nsmul_eq_mul]

#print axioms alpha_abs_le_log
run_cmd do
  for target in [``low_mangoldt_bounds, ``alpha_abs_le_log, ``high_moebius_energy, ``beta_energy] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.VaughanCoefficients152
end

end Update152_Component_28
/- END COMPONENT: VaughanCoefficients152.lean -/

#check Erdos374.MangoldtClosure152.candidate_main152
#print axioms Erdos374.MangoldtClosure152.candidate_main152
#print axioms Erdos374.MangoldtClosure152.positive_lower_density152
run_cmd do
  for target in [``Erdos374.MangoldtClosure152.candidate_main152,
      ``Erdos374.MangoldtClosure152.positive_lower_density152,
      ``Erdos374.MangoldtClosure152.large_phase_sampling_of_mangoldt,
      ``Erdos374.FourierReferenceIntegral152.large_phase_reference_integral,
      ``Erdos374.ReciprocalIntegral152.signed_character_weighted] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "UPDATE 152 FINAL AXIOM AUDIT PASSED: reference integral closed; TWO main analytic premises remain"

end
