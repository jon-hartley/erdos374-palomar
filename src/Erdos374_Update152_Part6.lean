/- Part 6 of 7 of `Erdos374_Update152` (split for the 10,000-line limit); continues `Erdos374_Update152_Part5`. -/
module

public import Erdos374_Update152_Part5

@[expose] public section


section Update152_Component_1
section Update151_Component_1
section Update150_Component_4
set_option autoImplicit false
set_option maxHeartbeats 2400000
section Flat_PrimeNumberTheoremAnd_MediumPNT
set_option lang.lemmaCmd true
open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

                  /- 
The approach here is completely standard. We follow the use of
$\mathcal{M}(\widetilde{1_{\epsilon}})$ as in [Kontorovich 2015].
-/

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

namespace Chebyshev

theorem psi_eq_sum_range (x : ℝ) :
    ψ x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n := by
  rw [psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]

end Chebyshev

                          
                           
                   
                                                   
    
                                       
    
                                                  
     
                             
noncomputable abbrev ChebyshevPsi (x : ℝ) : ℝ :=
  Chebyshev.psi x

                  /- 
It has already been established that zeta doesn't vanish on the 1 line, and has a pole at $s=1$
of order 1.
We also have the following.
-/

                                    
                                     
                   
                               
                                                                                 
                                        
theorem LogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = ∑' n, Λ n / (n : ℂ) ^ s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp
  · have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    dsimp [LSeriesSummable] at this
    convert! this; rename ℕ => n
    by_cases h : n = 0 <;> simp [LSeries.term, h]

                  /- 

The main object of study is the following inverse Mellin-type transform, which will turn out to
be a smoothed Chebyshev function.
-/

noncomputable abbrev SmoothedChebyshevIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

           
                                
                   
                                                                                          
                                                                                
                                                                                   
                                          
            
                                             
      
noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate

set_option backward.isDefEq.respectTransparency false in
lemma smoothedChebyshevIntegrand_conj
    {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    SmoothedChebyshevIntegrand SmoothingF ε X (conj s) =
      conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
  unfold SmoothedChebyshevIntegrand
  simp only [map_mul, map_div₀, map_neg]
  congr
  · exact deriv_riemannZeta_conj s
  · exact riemannZeta_conj s
  · unfold mellin
    rw[← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x xpos
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    congr
    nth_rw 1 [← map_one conj]
    rw[← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg xpos.le]
    exact Real.pi_ne_zero.symm
  · rw[Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm

open MeasureTheory

           
                                                        
                   
                                                                                             
                                                                                              
                                      
    
                                                             
    
                                
     
               
                                                                                                
                             
     
                        
lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
  obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  apply Integrable.mono' (g := (fun t ↦ c / ε * 1 / (1 + t ^ 2)))
  · apply Integrable.const_mul integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
      SmoothingFpos mass_one (s := σ + x * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith) |>.continuousAt
    fun_prop
  · filter_upwards [] with t
    calc
      _≤ c / ε * 1 / (σ^2 + t^2) := by
        convert hc (σ / 2) (by linarith) (σ + t * I) (by simp only [add_re, ofReal_re, mul_re,
          I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, half_le_self_iff]; linarith)
          (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero]; linarith) ε εpos  ε_lt_one using 1
        simp only [mul_one, Complex.sq_norm, normSq_apply, add_re, ofReal_re, mul_re, I_re,
          mul_zero, ofReal_im, I_im, sub_self, add_zero, add_im, mul_im, zero_add, mul_inv_rev]
        ring_nf
      _ ≤ _ := by
        gcongr; nlinarith

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

set_option backward.isDefEq.respectTransparency false in
           
                                                           
                   
                                                                                             
                                                                                                 
                                
                                                               
                                                                             
                                                                       
                                                                  
     
                                                             
                        
lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by

  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith

  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast

  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnnorm_real, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top

    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
        (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp[h]
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
           
                                         
                   
              
                                                                                     
     
               
              
                                                                                           
                                          
            
                                                                                                
                                                                   
                        
                                                        
                                          
            
    
    
                                         
      
theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
  dsimp [SmoothedChebyshev, SmoothedChebyshevIntegrand, VerticalIntegral', VerticalIntegral]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := logt_gt_one X_gt.le
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by
      simp only [inv_pos]
      linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LogDerivativeDirichlet]
    · rw [← tsum_mul_right, ← tsum_mul_right]
    · simp [σ_gt]
  · congr
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
      · push_cast at this ⊢
        rw [← this, div_mul_cancel₀]
        · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
      · apply div_nonneg (by linarith : 0 ≤ X); simp
      · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · push_cast
    congr
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
        εpos (by positivity)

                  /- 
The smoothed Chebyshev function is close to the actual Chebyshev function.
-/

--open scoped ArithmeticFunction in
theorem SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) →
      Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
  ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
      ψ X‖ ≤
    C * ε * X * Real.log X := by
  norm_cast

  let F := Smooth1 SmoothingF ε

  let n₀ := ⌈X * (1 - c₁ * ε)⌉₊

  have n₀_pos : 0 < n₀ := by
    simp only [Nat.ceil_pos, n₀]
    subst C_eq
    simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos]
    exact mul_lt_one_of_nonneg_of_lt_one_left c₁_pos.le c₁_lt ε_lt_one.le

  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    apply sub_le_self
    positivity

  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    exact le_of_lt (Nat.ceil_lt_add_one (by bound))

  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))

  have sumΛ : Summable (fun (n : ℕ) ↦ Λ n * F (n / X)) := by
    exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    (hc₂ _ _ (⟨ε_pos, ε_lt_one⟩) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
    (s ∘ Finset.mem_range.2))))))

  have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ Λ (n + n₀) * F ((n + n₀) / X)) := by
    exact_mod_cast sumΛ.comp_injective fun Q => by omega

  rw[← Summable.sum_add_tsum_nat_add' (k := n₀) (mod_cast sumΛn₀ n₀)]

  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊

  have n₁_pos : 0 < n₁ := by
    dsimp only [n₁]
    apply Nat.le_floor
    rw[Nat.succ_eq_add_one, zero_add]
    norm_cast
    apply one_le_mul_of_one_le_of_one_le (by linarith)
    apply le_add_of_nonneg_right
    positivity

  have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))

  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)

  have n₁_ge_n₀ : n₀ ≤ n₁ := by
    exact_mod_cast le_imp_le_of_le_of_le n₀_le n₁_ge (by linarith)

  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
    calc
      (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                        exact sub_le_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
       _            = X * ε * (c₂ + c₁) := by ring

  rw[show (∑' (n : ℕ), Λ (n + n₀ : ) * F ((n + n₀ : ) / X)) =
      (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((n + n₀) / X)) +
      (∑' (n : ℕ), Λ (n + n₁ : ) * F ((n + n₁ : ) / X)) by
    rw[← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)]
    · congr! 5
      · simp only [Nat.cast_add]
      · omega
      · congr! 1
        norm_cast
        omega
    · convert sumΛn₀ ((n₁ - n₀) + n₀) using 4
      · omega
      · congr! 1
        norm_cast
        omega]

  rw [show(∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) by
    have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) =
        Λ (n₁) * F (↑n₁ / X) + (∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X)) := by
      let fTemp := fun n ↦ Λ (n + n₁) * F ((↑n + ↑n₁) / X)
      have hTemp (n : ℕ): fTemp n = Λ (n + n₁) * F (↑(n + n₁) / X) := by rw[Nat.cast_add]
      rw[← tsum_congr hTemp, ← tsum_congr fun n ↦ (hTemp (n + 1))]
      have : Λ n₁ * F (↑n₁ / X) = fTemp 0 := by
        dsimp only [fTemp]
        rw[← Nat.cast_add, zero_add]
      rw[this]
      exact Summable.tsum_eq_zero_add (sumΛn₀ n₁)
    rw[this]
    apply add_eq_left.mpr
    convert tsum_zero with n
    convert mul_zero _
    apply smoothIs0
    rw[← mul_le_mul_iff_left₀ X_pos]
    rw [(by field_simp : ↑(n + 1 + n₁) / X * X = ↑(n + 1 + n₁)),
      (by ring : (1 + c₂ * ε) * X = 1 + (X * (1 + c₂ * ε) - 1)), Nat.cast_add, Nat.cast_add]
    bound]

  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
    apply le_trans <| Nat.le_ceil X
    exact_mod_cast Nat.ceil_le_floor_add_one X

  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := Nat.floor_le (by positivity)

  rw [show ψ X =
      (∑ x ∈ Finset.range n₀, Λ x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + ↑n₀) by
    field_simp
    simp only [add_comm _ n₀]
    rw [← Finset.sum_range_add, Nat.add_sub_of_le, Chebyshev.psi_eq_sum_range,
      Nat.floor_add_one X_pos.le]
    dsimp only [n₀]
    exact Nat.ceil_le.mpr (by linarith)]

  rw [show ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, Λ n by
    apply Finset.sum_congr rfl
    intro n hn
    obtain rfl|n_zero := eq_or_ne n 0
    · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert mul_one _
      apply smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      exact Nat.lt_ceil.mp hn |>.le]
  have vonBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    intro n hn
    have n_add_n0_le_n1: (n : ℝ) + n₀ ≤ n₁ := by
      apply le_of_lt
      rw[Finset.mem_range] at hn
      rw[← add_lt_add_iff_right (-↑n₀), add_neg_cancel_right, add_comm, ← sub_eq_neg_add]
      exact_mod_cast hn
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
    have inter2: Real.log (↑n + ↑n₀) ≤ Real.log (↑n₁) := by
      exact_mod_cast Real.log_le_log (by positivity) n_add_n0_le_n1
    have inter3: Real.log (↑n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by
      exact Real.log_le_log (by bound) (by linarith)
    exact le_imp_le_of_le_of_le inter1 inter3 inter2

  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖
    ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by
    have : (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) =
        (∑ n ∈ Finset.range (n₁ - n₀), Real.log (X * (1 + c₂ * ε))) := by
      rw[← Nat.cast_sub]
      · nth_rewrite 1 [← Finset.card_range (n₁ - n₀)]
        rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
        exact Eq.symm (Finset.sum_const (Real.log (X * (1 + c₂ * ε))))
      exact n₁_ge_n₀
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul (vonBnd1 _ hn) _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    · dsimp only [F]
      apply smooth1BddAbove
      bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound

  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤ (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by
    have : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) =
        (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), Real.log (X + 1)) := by
      rw[← Nat.cast_sub]
      · nth_rewrite 1 [← Finset.card_range (⌊X + 1⌋₊ - n₀)]
        rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
        exact Eq.symm (Finset.sum_const (Real.log (X + 1)))
      simp only [Nat.ceil_le, n₀]
      exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X
        X_le_floor_add_one
    rw[this]
    apply Finset.sum_le_sum
    intro n hn
    have n_add_n0_le_X_add_one: (n : ℝ) + n₀ ≤ X + 1 := by
      rw[Finset.mem_range] at hn
      rw [← add_le_add_iff_right (-↑n₀), add_assoc, ← sub_eq_add_neg, sub_self, add_zero,
        ← sub_eq_add_neg]
      have temp: (n : ℝ) < ⌊X + 1⌋₊ - n₀ := by
        rw [← Nat.cast_sub, Nat.cast_lt]
        · exact hn
        simp only [Nat.ceil_le, n₀]
        exact le_trans n₀_inside_le_X X_le_floor_add_one
      have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
        apply sub_le_sub_right floor_X_add_one_le_self
      exact le_of_lt (lt_of_le_of_lt' this temp)
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
    apply le_trans inter1
    exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)

  clear vonBnd1

  have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
    apply Real.log_le_log (by positivity)
    have const_le_2: 1 + c₂ * ε ≤ 3 := by
      have : (3 : ℝ) = 1 + 2 := by ring
      rw[this]
      apply add_le_add_right
      rw[← mul_one 2]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw[mul_comm]
    exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)

  calc
    _ = ‖∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X) -
          ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀) + Λ n₁ * F (↑n₁ / X)‖ := by
      congr 1
      ring
    _ ≤ (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
        ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ := by
      apply norm_add_le_of_le
      · apply norm_sub_le_of_le
        · apply norm_sum_le_of_le
          intro b hb
          exact norm_mul_le_of_le (by rfl) (by rfl)
        apply norm_sum_le_of_le
        intro b hb
        rfl
      exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)
    _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by
      apply add_le_add
      · apply le_trans <| add_le_add bnd1 bnd2
        rw [(by ring : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁)), add_mul]
        apply add_le_add
        · calc
            _ ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
              apply mul_le_mul n₁_sub_n₀ _ (log_nonneg (by linarith)) (by positivity)
              rw[← Real.log_mul (by positivity) (by positivity)]
              nth_rewrite 3 [mul_comm]
              exact inter1
            _ ≤ 2 * ((X * ε * (c₂ + c₁)) * Real.log X) := by
              rw[two_mul, mul_add]
              bound
            _ = _ := by ring
        calc
          _ ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
            apply mul_le_mul _ _ (log_nonneg (by linarith)) (by positivity)
            · rw [(by ring : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)))]
              apply sub_le_sub
              · apply le_trans floor_X_add_one_le_self
                ring_nf
                rw[add_comm, add_le_add_iff_left]
                exact X_bound_1
              nth_rewrite 2 [mul_comm]
              exact n₀_gt
            rw[← Real.log_mul (by positivity) (by norm_num), mul_comm]
            exact Real.log_le_log (by positivity) (by linarith)
          _ = 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log 3) := by ring
          _ ≤ 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log X) := by gcongr
          _ = _ := by ring
      · apply le_trans _ inter1
        rw[← mul_one (Real.log (X * (1 + c₂ * ε)))]
        apply mul_le_mul _ _ (norm_nonneg _) (log_nonneg (by bound))
        · rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact le_trans ArithmeticFunction.vonMangoldt_le_log <|
            Real.log_le_log (mod_cast n₁_pos) n₁_le
        rw[Real.norm_of_nonneg <| smooth1BddBelow _ n₁_pos]
        apply smooth1BddAbove _ n₁_pos
    _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (Real.log X + (Real.log X + Real.log 3)) := by
      rw [← Real.log_mul (by positivity) (by positivity), mul_comm X 3]
      nth_rewrite 2 [mul_add]
      apply add_le_add_right
      nth_rewrite 1 [← one_mul (Real.log (3 * X))]
      apply mul_le_mul_of_nonneg_right _ (log_nonneg (by linarith))
      linarith
    _ = 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
          2 * (X * ε * (3 * c₁ + c₂)) * Real.log 3 := by ring
    _ ≤ 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
          2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by gcongr
    _ = _ := by
      rw [C_eq]
      ring

           
                                     
                   
              
                                                          
     
               
                                                                                                
                                                                                              
                                                                                   

                                                                                                  
                                                                          
                                                                                                   
                                                                                                  
                                             
                                                 
                                                                             
      
theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one

  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF

  have c₁_lt : c₁ < 1 := by
    rw[c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)

  have c₂_lt : c₂ < 2 := by
    rw[c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity

  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl

  clear_value C

  have Cpos : 0 < C := by
    rw [C_eq]
    positivity

  refine ⟨C, Cpos, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩

  have X_gt_zero : (0 : ℝ) < X := by linarith

  have n_on_X_pos {n : ℕ} (npos : 0 < n) :
      0 < n / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity

  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)

  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos

  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : n ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le

  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ n / X) :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le

  have ε_pos: ε > 0 := by linarith
  have X_pos: X > 0 := by linarith
  have X_gt_three : 3 < X := by linarith

  intro X_bound

  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw[c₁_eq, ← div_le_iff₀]
    · have : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw[one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
        · exact Real.log_pos (by norm_num)
        norm_num
      exact le_of_lt (gt_trans X_bound this)
    exact Real.log_pos (by norm_num)

  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw[c₂_eq, ← div_le_iff₀]
    · have : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        · rw[one_div_lt_one_div, ← one_mul (1 / 2)]
          · apply mul_lt_mul
            · norm_num
            · apply le_of_lt
              exact lt_trans (by norm_num) (Real.log_two_gt_d9)
            repeat norm_num
          · norm_num
            exact Real.log_pos (by norm_num)
          · norm_num
      exact le_of_lt (gt_trans X_bound this)
    norm_num
    exact Real.log_pos (by norm_num)

  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF
    mass_one (by linarith) εpos ε_lt_one]

  convert SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε
    ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow
    smoothIs1 smoothIs0

                                  
                                   
                   
                                                                                  
                                                                                                  
      
def LogDerivZetaHasBound (n₁ n₂ : ℝ) (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ n₁)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ n₂

                  /- 
Suppose we have an estimate of the form in Definition \ref{LogDerivZetaHasBound}. Returning to the
definition of $\psi_{\epsilon}$, fix a large $T$ to be chosen later, and set
$\sigma_0 = 1 + 1 / log X$,
$\sigma_1 = 1- A/ \log T^{n_1}$ (where $n_1$ comes from our estimate from Definition
\ref{LogDerivZetaHasBound}), and
$\sigma_2<\sigma_1$ a constant.
Pull
contours (via rectangles!) to go
from $\sigma_0-i\infty$ up to $\sigma_0-iT$, then over to $\sigma_1-iT$, up to $\sigma_1-3i$,
over to $\sigma_2-3i$, up to $\sigma_2+3i$, back over to $\sigma_1+3i$, up to $\sigma_1+iT$,
over to $\sigma_0+iT$, and finally up to $\sigma_0+i\infty$.

In the process, we will pick up the residue at $s=1$.
We will do this in several stages. Here the interval integrals are defined as follows:
-/

           
      
                 
                   
    
                                                                  
        
                                     
         
                                                    
                    
          
    
      
noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

           
      
                 
                   
    
                                                                                   
        
                                   
         
                                                   
                            
    
      
noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

           
       
                  
                   
    
                                                                         
        
                                     
         
                                                     
                             
    
      
noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

           
      
                 
                   
    
                                                                                   
        
                                   
         
                                                   
                            
    
      
noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

           
      
                 
                   
    
                                                                
        
                                     
         
                                                     
                             
    
      
noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

           
      
                 
                   
    
                                                                       
        
                                     
         
                                                     
                             
    
      
noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

           
      
                 
                   
    
                                                                     
        
                                     
         
                                                     
                             
    
      
noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

           
      
                 
                   
    
                                                                                          
        
                                   
         
                                                   
                            
    
      
noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

           
      
                 
                   
    
                                                                                          
        
                                   
         
                                                   
                            
    
      
noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

           
      
                 
                   
    
                                                                   
        
                                     
         
                                                     
                             
    
      
noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

theorem realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  apply ContinuousAt.comp _ (by fun_prop)
  convert hf.continuousAt
  simp

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})

theorem dlog_riemannZeta_bdd_on_vertical_lines_explicit {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∀(t : ℝ), ‖(-ζ' (σ₀ + t * I) / ζ (σ₀ + t * I))‖ ≤ ‖(ζ' σ₀ / ζ σ₀)‖ :=
  fun _ ↦ dlog_riemannZeta_bdd_on_vertical_lines_generalized _ _ _ σ₀_gt <| le_refl _

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED
           
                                                     
                   
                                                               
    
                         
                                                                               
    
     
               
                                                                                              
     
                        
theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
    ∃ c > 0, ∀(t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ c := by
  refine ⟨1 + ‖(ζ' σ₀ / ζ σ₀)‖, (by positivity), fun t ↦ ?_⟩
  have := dlog_riemannZeta_bdd_on_vertical_lines_explicit σ₀_gt t
  rw [neg_div, norm_neg] at this
  exact le_trans this (lt_one_add _).le

           
                                                    
                   
                                                                                   
                                                                                  
     
               
                                                                                   
                                            
                                                          
                                
                                            
                                                                             
                                           
     
                        
theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
    intro t
    simp only [Complex.norm_mul, c]
    gcongr
    · convert! hC t using 1
      simp
    · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
      · simp
      · linarith
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, ne_eq]
        linarith
  convert (SmoothedChebyshevDirichlet_aux_integrable ContDiffSmoothingF SmoothingFnonneg
    suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul
      (c := c) ?_ (ae_of_all _ this) using 2
  · unfold SmoothedChebyshevIntegrand
    ring
  · apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    intro t _
    let s := σ₀ + (t : ℂ) * I
    have s_ne_one : s ≠ 1 := by
      intro h
      -- If σ₀ + t * I = 1, then taking real parts gives σ₀ = 1
      have : σ₀ = 1 := by
        have := congr_arg Complex.re h
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, one_re, s] at this
        exact this
      -- But this contradicts 1 < σ₀
      linarith [σ₀_gt]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have diffζ := differentiableAt_riemannZeta s_ne_one
      apply ContinuousAt.div
      · apply ContinuousAt.neg
        have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
          differentiableAt_deriv_riemannZeta s_ne_one
        convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) this <;> simp
      · convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp [σ₀_gt]
    · apply ContinuousAt.comp _ (by fun_prop)
      apply continuousAt_const_cpow
      norm_cast
      linarith

           
                             
                                                                                                                                 
                                                                                                                
                        
lemma BddAboveOnRect {g : ℂ → ℂ} {z w : ℂ} (holoOn : HolomorphicOn g (z.Rectangle w)) :
    BddAbove (norm ∘ g '' (z.Rectangle w)) := by
  have compact_rect : IsCompact (z.Rectangle w) := by
    apply IsCompact.reProdIm <;> apply isCompact_uIcc
  refine IsCompact.bddAbove_image compact_rect ?_
  apply holoOn.continuousOn.norm

           
                                     
                   
              
                        
                                          
         
                               
   
    
     
                                                                            
theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
  unfold SmoothedChebyshev
  unfold VerticalIntegral'
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    bound
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw[← one_add_one_eq_two]
    gcongr
    exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  · exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
      X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
  · have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
    unfold I₁
    simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc, add_left_cancel_iff]
    unfold I₉
    nth_rewrite 6 [add_comm]
    simp only [← add_assoc]
    rw [add_right_cancel_iff,
        ← add_right_inj (1 / (2 * ↑π * I) *
          -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
        ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
    unfold VIntegral I₂ I₃₇ I₈
    simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
    let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
      SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
    let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
    have : ∫ (y : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
        ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
        unfold fTempRR
        simp only [temp]
    rw[this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ - ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
        unfold fTempRR
        simp only [ofReal_neg, neg_mul, sub_eq_add_neg]
    rw[this]
    have : ∫ (t : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
        ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := rfl
    rw[this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ + ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := rfl
    rw[this]
    have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
        -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
        I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
        -(2 * ↑π * I) * RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
        unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
        simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
          ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
          neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
          ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
          zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
        ring_nf
        simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
          mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
        ring_nf
    rw[this]
    field_simp
    rw[mul_comm, eq_comm, neg_add_eq_zero]

    have pInRectangleInterior :
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
      refine rectangle_mem_nhds_iff.mpr ?_
      refine mem_reProdIm.mpr ?_
      simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
        sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
      constructor
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨σ₁_lt_one, (by linarith)⟩
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨(by linarith), (by linarith)⟩

    apply ResidueTheoremOnRectangleWithSimplePole'
    · simp; linarith
    · simp; linarith
    · simp only [one_div]
      exact pInRectangleInterior
    · apply DifferentiableOn.mul
      · apply DifferentiableOn.mul
        · simp only [re_add_im]
          have : (fun z ↦ -ζ' z / ζ z) = -(ζ' / ζ) := by ext; simp; ring
          rw [this]
          apply DifferentiableOn.neg
          apply holoOn.mono
          apply Set.sdiff_subset_sdiff_left
          apply reProdIm_subset_iff'.mpr
          left
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
            neg_zero, zero_div, zero_add]
          constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
        · intro s hs
          apply DifferentiableAt.differentiableWithinAt
          simp only [re_add_im]
          apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one
          have := mem_reProdIm.mp hs.1 |>.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        simp only [re_add_im]
        apply DifferentiableAt.const_cpow (by fun_prop)
        left
        norm_cast
        linarith
    · let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
      let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
      let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
      unfold fTempC fTempRR SmoothedChebyshevIntegrand
      simp only [re_add_im]
      have g_holc : HolomorphicOn g U := by
        intro u uInU
        apply DifferentiableAt.differentiableWithinAt
        simp only [g]
        apply DifferentiableAt.mul
        · apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one
          simp only [ofReal_inv, U] at uInU
          unfold Rectangle at uInU
          rw[Complex.mem_reProdIm] at uInU
          have := uInU.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
        · unfold HPow.hPow instHPow
          apply DifferentiableAt.const_cpow differentiableAt_fun_id
          left
          norm_cast
          linarith
      have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
        simp only [one_mul, f]
        exact riemannZetaLogDerivResidueBigO
      convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
      ext
      simp [f, g]
      ring

lemma interval_membership (r : ℝ) (a b : ℝ) (h1 : r ∈ Set.Icc (min a b) (max a b)) (h2 : a < b) :
    a ≤ r ∧ r ≤ b := by
  -- Since a < b, we have min(a,b) = a and max(a,b) = b
  have min_eq : min a b = a := min_eq_left (le_of_lt h2)
  have max_eq : max a b = b := max_eq_right (le_of_lt h2)
  rw [min_eq, max_eq] at h1
  rw [← @mem_Icc]
  exact h1

lemma verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    VIntegral f σ s e =
    VIntegral f σ s a +
    VIntegral f σ a b +
    VIntegral f σ b e := by
  dsimp [VIntegral]
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a),
    ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
  · ring
  all_goals
    apply IntervalIntegrable.mono_set hf
    apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith

lemma verticalIntegral_split_three_finite' {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s e) =
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) := by
  have : (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
      (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
      (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) =
        (1 : ℂ) / (2 * π * I) * ((VIntegral f σ s a) +
    (VIntegral f σ a b) +
    (VIntegral f σ b e)) := by ring
  rw [this]
  clear this
  rw [← verticalIntegral_split_three_finite hf hab]

theorem SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
  (holoOn : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
  ContinuousOn (fun (t : ℝ) ↦ -ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)) (Icc (-T) T) := by
  rw [show (fun (t : ℝ) ↦ -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) =
      -(ζ' / ζ) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
  apply ContinuousOn.neg
  apply holoOn.continuousOn.comp (by fun_prop)
  intro t ht
  simp only [Set.mem_sdiff, mem_singleton_iff]
  constructor
  · apply mem_reProdIm.mpr
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
    linarith
  · intro h
    replace h := congr_arg re h
    simp at h
    linarith

                  /- 
Next pull contours to another box.
-/

           
                                     
                   
              
    
          
                             
   
    
     
                                                                          
                        
theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith
  -- Step (1)
  -- Show that the Rectangle is in a given subset of holomorphicity
  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
    -- for every point x in the Rectangle
    intro x hx
    constructor
    · -- x is in the locus of holomorphicity
      simp only [Rectangle, uIcc] at hx
      rw [Complex.mem_reProdIm] at hx ⊢
      obtain ⟨hx_re, hx_im⟩ := hx
      -- the real part of x is in the correct interval
      have hzw_re : z.re < w.re := by
        simpa [z, w] using σ₂_lt_σ₁
      have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
        exact interval_membership x.re z.re w.re hx_re hzw_re
      have x_re_in_Icc : x.re ∈ Icc σ₂ 2 := by
        have ⟨h_left, h_right⟩ := x_re_bounds
        have h_left' : σ₂ ≤ x.re := by
          simpa [z] using h_left
        have h_right' : x.re ≤ 2 := by
          apply le_trans h_right
          have : w.re ≤ 2 := by
            simp [w]
            linarith
          exact this
        exact ⟨h_left', h_right'⟩
      -- the imaginary part of x is in the correct interval
      have hzw_im : z.im < w.im := by
        norm_num [z, w]
      have x_im_bounds : z.im ≤ x.im ∧ x.im ≤ w.im := by
        exact interval_membership x.im z.im w.im hx_im hzw_im
      have x_im_in_Icc : x.im ∈ Icc (-3) 3 := by
        have ⟨h_left, h_right⟩ := x_im_bounds
        have h_left' : -3 ≤ x.im := by
          simpa [z] using h_left
        have h_right' : x.im ≤ 3 := by
          simpa [w] using h_right
        exact ⟨h_left', h_right'⟩
      exact ⟨x_re_in_Icc, x_im_in_Icc⟩
    -- x is not in {1} by contradiction
    · simp only [mem_singleton_iff]
      -- x has real part less than 1
      have x_re_upper: x.re ≤ σ₁ := by
        simp only [Rectangle, uIcc] at hx
        rw [Complex.mem_reProdIm] at hx
        obtain ⟨hx_re, _⟩ := hx
        -- the real part of x is in the interval
        have hzw_re : z.re < w.re := by
          simpa [z, w] using σ₂_lt_σ₁
        have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
          exact interval_membership x.re z.re w.re hx_re hzw_re
        have x_re_upper' : x.re ≤ w.re := x_re_bounds.2
        have hw_re : w.re = σ₁ := by simp [w]
        linarith
      -- by contracdiction
      have h_x_ne_one : x ≠ 1 := by
        intro h_eq
        have h_re : x.re = 1 := by rw [h_eq, Complex.one_re]
        have h1 : 1 ≤ σ₁ := by
          rw [← h_re]
          exact x_re_upper
        linarith
      exact h_x_ne_one
  have zero_over_box := HolomorphicOn.vanishesOnRectangle holoOn2 sub
  have splitting : I₃₇ SmoothingF ε T X σ₁ =
    I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    unfold I₃₇ I₃ I₅ I₇
    apply verticalIntegral_split_three_finite'
    · apply ContinuousOn.integrableOn_Icc
      unfold SmoothedChebyshevIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t t_mem
          have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
          simpa using realDiff_of_complexDiff _ this
      · apply continuousOn_of_forall_continuousAt
        intro t t_mem
        apply ContinuousAt.comp
        · refine continuousAt_const_cpow' ?_
          intro h
          have : σ₁ = 0 := by
            have h_real : (↑σ₁ + ↑t * I).re = (0 : ℂ).re := by
              rw [h]
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, zero_re] at h_real
            exact h_real
          linarith
        · -- continuity -- failed
          apply ContinuousAt.add
          · exact continuousAt_const
          · apply ContinuousAt.mul
            · apply continuous_ofReal.continuousAt
            · exact continuousAt_const
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc I₃₇ SmoothingF ε T X σ₁ =
        I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
        (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
        (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
        - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
        + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
        - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp [RectangleIntegral]
    _ = I₃₇ SmoothingF ε T X σ₁ -
        ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
        - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
        + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
        - (1 / (2 * π * I)) *
            VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
        w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
    --- starting from now, we split the integral `I₃₇` into `I₃ σ₂ + I₅ σ₁ + I₇ σ₁` using `verticalIntegral_split_three_finite`
    _ = I₃ SmoothingF ε T X σ₁
    + I₅ SmoothingF ε X σ₁
    + I₇ SmoothingF ε T X σ₁
    - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      rw [splitting]
    _ = I₃ SmoothingF ε T X σ₁
    - I₄ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₂
    + I₆ SmoothingF ε X σ₁ σ₂
    + I₇ SmoothingF ε T X σ₁ := by
      ring

                  /- 
We insert this information in $\psi_{\epsilon}$. We add and subtract the integral over the box
$[1-\delta,2] \times_{ℂ} [-T,T]$, which we evaluate as follows
-/
           
                          
                   
                                                                                                                                    
                      
    
                                                         
                    
     
                                                    
     
                                                                                   
theorem ZetaBoxEval {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C, ∀ᶠ ε in (nhdsWithin 0 (Ioi 0)), ∀ X : ℝ, 0 ≤ X →
    ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X - X‖ ≤ C * ε * X := by
  have := MellinOfSmooth1c ContDiffSmoothingF suppSmoothingF mass_one
  clear suppSmoothingF mass_one ContDiffSmoothingF
  rw[Asymptotics.isBigO_iff] at this
  obtain ⟨C, hC⟩ := this
  use C
  have εpos : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), ε > 0 :=
    eventually_mem_of_tendsto_nhdsWithin fun ⦃U⦄ hU ↦ hU
  filter_upwards [hC, εpos] with ε hC εpos
  rw[id_eq, norm_of_nonneg (le_of_lt εpos)] at hC
  intro X Xnne
  nth_rw 2 [← one_mul (X : ℂ)]
  rw[← sub_mul, norm_mul, norm_real, norm_of_nonneg Xnne]
  exact mul_le_mul_of_nonneg_right hC Xnne

theorem poisson_kernel_integrable (x : ℝ) (hx : x ≠ 0) :
  MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
  -- First, simplify the complex norm
  have h1 : ∀ t : ℝ, ‖x + t * I‖^2 = x^2 + t^2 := by
    intro t
    rw [← normSq_eq_norm_sq, normSq_add_mul_I]
  -- Rewrite the integrand using this simplification
  simp_rw [h1]
  apply integrable_comp_mul_left_iff _ hx |>.mp
  have : (fun t ↦ (x ^ 2 + (x * t) ^ 2) ⁻¹) = (fun t ↦ (1 / x ^ 2) * (1 + t ^ 2) ⁻¹) := by
    ext
    field_simp
  rw [this]
  apply integrable_inv_one_add_sq.const_mul

theorem ae_volume_of_contains_compl_singleton_zero
  (s : Set ℝ)
  (h : (univ : Set ℝ) \ {0} ⊆ s) :
  s ∈ (MeasureTheory.ae volume) := by
  -- The key insight is that {0} has measure zero in ℝ
  have h_zero_null : volume ({0} : Set ℝ) = 0 := by
    exact volume_singleton

  -- Since s contains univ \ {0} = ℝ \ {0}, its complement is contained in {0}
  have h_compl_subset : sᶜ ⊆ {0} := by
    intro x hx
    -- If x is not in s, then x is not in ℝ \ {0} (since ℝ \ {0} is a subset of s)
    -- This means x = 0
    by_contra h_not_zero
    have : x ∈ univ \ {0} := ⟨trivial, h_not_zero⟩
    exact hx (h this)

  -- Therefore, volume(sᶜ) ≤ volume({0}) = 0
  have h_compl_measure : volume sᶜ ≤ volume ({0} : Set ℝ) :=
    measure_mono h_compl_subset

  -- So volume(sᶜ) = 0
  have h_compl_zero : volume sᶜ = 0 := by
    rw [h_zero_null] at h_compl_measure
    exact le_antisymm h_compl_measure (by positivity)

  -- A set is in ae.sets iff its complement has measure zero
  rwa [mem_ae_iff]

theorem integral_evaluation (x : ℝ) (T : ℝ) (T_large : 3 < T) :
    ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
  have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
    intro x t
    rw [Complex.norm_add_mul_I x t]
    ring_nf
    rw [Real.sq_sqrt _]
    · simp only [le_add_iff_nonneg_right]; positivity
    · positivity

  have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro x t hyp
    have U0 : 0 < t^2 := by positivity
    have U1 : 0 < ‖x + t * I‖^2 := by
      rw [Complex.norm_add_mul_I x t,
        Real.sq_sqrt _]

      · positivity
      · positivity
    rw [inv_le_inv₀ U1 U0]
    exact (T00 x t)

  have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    refine mem_inf_of_left ?_
    · refine Filter.mem_sets.mp ?_
      · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
          rw [Set.setOf_subset_setOf]
          intro t hyp_t
          exact T0 x t hyp_t
        have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
          apply Set.ext
          intro x
          simp_all only [ne_eq, setOf_subset_setOf, not_false_eq_true, implies_true,
            mem_setOf_eq, Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]

        rw [U1] at U
        exact ae_volume_of_contains_compl_singleton_zero _ U

  have T3 : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Iic (-T))) := by
    have D3 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by linarith : 0 < T) |>.comp_neg
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, measure_singleton,
            EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow]

  calc
    _ ≤ ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹  := by
      apply MeasureTheory.integral_mono_of_nonneg _ T3 T1
      filter_upwards [] with x
      simp
    _ = _ := by
      rw [← integral_comp_neg_Ioi]
      conv => lhs; arg 2; ext x; rw [show ((-x) ^ 2)⁻¹ = x ^ (-2 : ℝ) by simp [zpow_ofNat]]
      rw[integral_Ioi_rpow_of_lt (by norm_num) (by linarith)]
      ring_nf
      rw [rpow_neg_one]

                  /- 
It remains to estimate all of the integrals.
-/

                  /- 
This auxiliary lemma is useful for what follows.
-/
           
                          
                   
                                                                                                               
    
                         
    
     
               
                                                                    
                                                                                               
     
                        
lemma IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) {k : ℝ} (k_pos : 0 < k) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
  -- When X is large, the ratio goes to 0.
  have ⟨M, hM⟩ := Filter.eventually_atTop.mp (isLittleO_log_rpow_rpow_atTop k zero_lt_one).eventuallyLE
  -- When X is small, use the extreme value theorem.
  let f := fun X ↦ Real.log X ^ k / X
  set I := Icc X₀ M with defI
  have : 0 ∉ I := notMem_Icc_of_lt X₀pos
  have f_cont : ContinuousOn f (Icc X₀ M) := by
    unfold f
    refine ContinuousOn.div₀ (ContinuousOn.rpow (continuousOn_log.mono ?_) continuousOn_const (fun _ _ ↦ Or.inr k_pos)) (continuousOn_id' _) (fun x hx h ↦ ?_)
    · simp only [subset_compl_singleton_iff, ← defI, this, not_false_eq_true]
    · rw [← defI, h] at hx
      exact this hx
  have ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn f_cont
  use max C₁ 1, le_max_right C₁ 1
  intro X hX
  have Xpos : X > 0 := lt_of_lt_of_le X₀pos hX
  by_cases hXM : X ≤ M
  · rw[← div_le_iff₀ Xpos]
    calc
      f X ≤ ‖f X‖ := le_norm_self _
      _ ≤ C₁ := hC₁ X ⟨hX, hXM⟩
      _ ≤ max C₁ 1 := le_max_left C₁ 1
  · calc
      Real.log X ^ k ≤ ‖Real.log X ^ k‖ := le_norm_self _
      _ ≤ ‖X ^ 1‖ := by exact_mod_cast hM X (by linarith[hXM])
      _ = 1 * X := by
        rw[pow_one, one_mul]
        apply norm_of_nonneg
        exact Xpos.le
      _ ≤ max C₁ 1 * X := by
        rw[mul_le_mul_iff_left₀ Xpos]
        exact le_max_right C₁ 1

def I1BoundGenProp (SmoothingF : ℝ → ℝ) : Prop := ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)

           
                      
                   
              
    
                                   
                                        
   
    
     
               
                                                             
    
                                           
        
                                      
        
                                     
         
                                                    
                    
          
         
    
                                                          
                                                                             
                                                                                                 
    
      
                
        
                      
               
                                        
              
      
         
   
    
                                               
                                     
    
      
              
                                   
                     
               
      
          
                                 
   
    
                                                                                               
     
                        
theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I1BoundGenProp SmoothingF := by

  obtain ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  have G0 : ∃K > 0, ∀(t σ : ℝ), 1 < σ → σ < 2 → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    let ⟨K', ⟨K'_pos, K'_bounds_zeta⟩⟩ := triv_bound_zeta
    use (2 * (K' + 1))
    use (by positivity)
    intro t σ cond cond2

    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
        norm_neg, tsub_le_iff_right, inv_one]

    have T : (K' + 1) * 1 ≤ (K' + 1) * (σ - 1)⁻¹ :=
      by
        exact (mul_le_mul_iff_right₀ T0).mpr T1
    have U := calc
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by
        rw [← norm_neg _, mul_comm, neg_div' _ _]
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds_zeta σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by linarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by
        ring_nf

    exact U

  obtain ⟨K, ⟨K_is_pos, K_bounds_zeta_at_any_t'⟩⟩ := G0

  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity

  use (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M))
  use C_final_pos

  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)

  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := by
    intro t
    unfold pts
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]

  have pts_re_ge_one : 1 < pts_re := by
    unfold pts_re
    simp only [lt_add_iff_pos_right, inv_pos]
    have U : 1 < X := by linarith
    exact Real.log_pos U

  have pts_re_le_one : pts_re < 2 := by
    unfold pts_re
    have Z : Real.log 3 < Real.log X :=
      by
        refine log_lt_log ?_ X_large
        simp only [Nat.ofNat_pos]

    have Z01 : 1 < Real.log 3 := logt_gt_one le_rfl
    have Zpos0 : 0 < Real.log 3 := by positivity
    have Zpos1 : 0 < Real.log X := by calc
      0 < Real.log 3 := Zpos0
      _ < Real.log X := Z

    have Z1 : (Real.log X)⁻¹ < (Real.log 3)⁻¹ := (inv_lt_inv₀ Zpos1 Zpos0).mpr Z

    have Z02 : (Real.log 3)⁻¹ < 1 := by
      have T01 := (inv_lt_inv₀ ?_ ?_).mpr Z01
      · simp only [inv_one] at T01
        exact T01
      · exact Zpos0
      simp only [zero_lt_one]

    have Z2 : 1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := by
      exact (add_lt_add_iff_left 1).mpr Z1

    have Z3 : 1 + (Real.log 3)⁻¹ < 2 := by
      calc
        1 + (Real.log 3)⁻¹ < 1 + 1 := by linarith
        _ = 2 := by ring_nf

    calc
      1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := Z2
      _ < 2 := Z3

  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    unfold pts_re
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, add_sub_cancel_left, inv_inv]

  have K_bounds_zeta_at_any_t :
      ∀(t : ℝ), ‖ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
    intro t
    rw [←inve]
    exact K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by
    unfold pts_re
    positivity

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := by
    intro t
    unfold pts_re
    exact Eq.ge (pts_re_triv t)

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 := by
    intro t
    unfold pts
    refine EReal.coe_le_coe_iff.mp ?_
    · simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, le_refl, implies_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, EReal.coe_le_coe_iff]
      exact le_of_lt pts_re_le_one

  have pts_re_ge_1 : pts_re > 1 := by
    unfold pts_re
    exact pts_re_ge_one

  have X_pos_triv : 0 < X := by positivity

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  /- Main pointwise bound -/

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by

    intro t

    let M_bounds_mellin_easy := fun (t : ℝ) ↦
      M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t) (triv_pts_up_bound t)
        eps eps_pos eps_less_one

    let zeta_part := (fun (t : ℝ) ↦ -ζ' (pts t) / ζ (pts t))
    let mellin_part := (fun (t : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF eps x : ℂ)) (pts t))
    let X_part := (fun (t : ℝ) ↦ (↑X : ℂ) ^ (pts t))

    let g := fun (t : ℝ) ↦ (zeta_part t) * (mellin_part t) * (X_part t)

    have X_part_eq : ∀(t : ℝ), ‖X_part t‖ = X^pts_re := by
      intro t
      have U := Complex.norm_cpow_eq_rpow_re_of_pos (X_pos_triv) (pts t)
      rw [pts_re_triv t] at U
      exact U

    have X_part_bound : ∀(t : ℝ), ‖X_part t‖ ≤ X^pts_re := by
      intro t
      rw [←X_part_eq]

    have mellin_bound : ∀(t : ℝ), ‖mellin_part t‖ ≤ M * (eps * ‖pts t‖ ^ 2)⁻¹ := by
      intro t
      exact M_bounds_mellin_easy t

    have X_part_and_mellin_bound :
        ∀(t : ℝ), ‖mellin_part t * X_part t‖ ≤ M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
      intro t
      exact norm_mul_le_of_le (mellin_bound t) (X_part_bound t)

    have T2 : ∀(t : ℝ), ‖zeta_part t‖ = ‖ζ' (pts t) / ζ (pts t)‖ := by
      intro t
      unfold zeta_part
      simp only [Complex.norm_div, norm_neg]

    have zeta_bound : ∀(t : ℝ), ‖zeta_part t‖ ≤ K * Real.log X := by
      intro t
      unfold zeta_part
      rw [T2]
      exact K_bounds_zeta_at_any_t t

    have g_bound : ∀(t : ℝ), ‖zeta_part t * (mellin_part t * X_part t)‖ ≤
        (K * Real.log X) * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      intro t
      exact norm_mul_le_of_le (zeta_bound t) (X_part_and_mellin_bound t)

    have T1 : f = g := rfl

    have final_bound_pointwise :
        ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      rw [T1]
      unfold g
      rw [mul_assoc]
      exact g_bound t

    have trivialize :
        K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) =
          (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by ring_nf

    rw [trivialize] at final_bound_pointwise
    exact final_bound_pointwise

  have σ₀_gt : 1 < pts_re := pts_re_ge_1
  have σ₀_le_2 : pts_re ≤ 2 := by
    unfold pts_re
    -- LOL!
    exact
      Preorder.le_trans (1 + (Real.log X)⁻¹) (pts (SmoothingF (SmoothingF M))).re 2
        (triv_pts_lo_bound (SmoothingF (SmoothingF M)))
        (triv_pts_up_bound (SmoothingF (SmoothingF M)))

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large σ₀_gt
    σ₀_le_2 suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    unfold pts_re

    calc
      X ^ (1 + (Real.log X)⁻¹) = X * X ^ ((Real.log X)⁻¹) := by
        refine rpow_one_add' ?_ ?_
        · positivity
        · exact Ne.symm (ne_of_lt pts_re_pos)
      _ = X * rexp 1 := by
        refine (mul_right_inj' ?_).mpr ?_
        · exact Ne.symm (ne_of_lt X_pos_triv)
        · refine rpow_inv_log X_pos_triv ?_
          · by_contra h
            simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
              Complex.norm_div, Nat.not_ofNat_lt_one]
      _ = rexp 1 * X := by ring_nf

  have pts_re_neq_zero : pts_re ≠ 0 := by
    by_contra h
    rw [h] at pts_re_ge_1
    simp only [gt_iff_lt] at pts_re_ge_1
    norm_cast at pts_re_ge_1

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Iic (-T), f t‖ ≤ ∫ (t : ℝ) in Iic (-T), ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Iic (-T), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono ?_ ?_ (fun t ↦ G t)
            · refine Integrable.norm ?_
              · unfold f
                exact MeasureTheory.Integrable.restrict f_integrable
            · have equ : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹ := by
                   intro t; ring_nf
              have fun_equ : (fun (t : ℝ) ↦ ((K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re)) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹)) := by
                   funext t
                   exact equ t

              rw [fun_equ]
              have simple_int : MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
                := by
                   unfold pts
                   exact poisson_kernel_integrable pts_re (pts_re_neq_zero)

              have U := MeasureTheory.Integrable.const_mul simple_int
                ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              refine MeasureTheory.Integrable.restrict ?_
              exact U
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ *
              ∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹ := by
              have simpli_fun :
                  (fun (t : ℝ) ↦ (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re) =
                    (fun (t : ℝ) ↦ ((K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹)) :=
                by funext t; ring_nf
              rw [simpli_fun]
              exact MeasureTheory.integral_const_mul ((K * M) * Real.log X * X ^ pts_re * eps⁻¹)
                (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ := by
              have U := integral_evaluation (pts_re) T (T_large)
              unfold pts
              simp only [ge_iff_le]
              have U2 : 0 ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ := by
                simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
                  Complex.norm_div, le_refl, implies_true, inv_pos, mul_nonneg_iff_of_pos_right]
                refine Left.mul_nonneg ?_ ?_
                · refine Left.mul_nonneg ?_ ?_
                  · exact Left.mul_nonneg (by positivity) (by positivity)
                  · refine log_nonneg ?_
                    · linarith
                · refine Left.mul_nonneg ?_ ?_
                  · exact exp_nonneg 1
                  · exact le_of_lt X_pos_triv
              exact mul_le_mul_of_nonneg_left U U2
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf

  unfold I₁
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 := mul_le_mul_of_nonneg_left Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4

set_option backward.isDefEq.respectTransparency false in
lemma I9I1 {SmoothingF : ℝ → ℝ} {ε X T : ℝ} (Xpos : 0 < X) :
    I₉ SmoothingF ε X T = conj (I₁ SmoothingF ε X T) := by
  unfold I₉ I₁
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun <| measurableSet_Ioi
    intro t ht
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp

def I9BoundGenProp (SmoothingF : ℝ → ℝ) : Prop := ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)

                     
                      
                   
              
    
                                   
                                  
   
    
     
               
                                                                                                    
     
                        
theorem I9Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I9BoundGenProp SmoothingF := by
  obtain ⟨C, Cpos, bound⟩ := I1Bound suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]

lemma one_add_inv_log {X : ℝ} (X_ge : 3 ≤ X) : (1 + (Real.log X)⁻¹) < 2 := by
  rw[← one_add_one_eq_two]
  refine (add_lt_add_iff_left 1).mpr ?_
  refine inv_lt_one_of_one_lt₀ (logt_gt_one X_ge)

def I2BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)

                        
                         
                   
                                                                                    
    
                                                            
    
     
               
                                                           
    
                                                  
                                                  
                                                       
                                                       
                  
            
         
    
        
                
                            
                       
                                     
              
            
       
                                              
   
    
                                                                                                 
                                                              
                                                  
     
                        
lemma I2GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound n₁ n₂ A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    I2BoundGenProp n₁ SmoothingF A := by
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) n₂_pos)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    dsimp[σ₁]
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_right
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      · exact A_in.1.le
      apply Real.rpow_nonneg
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have σ₁pos : 0 < σ₁ := by
    rw[sub_pos]
    calc
      A / Real.log T ^ n₁ ≤ 1 / 2 / Real.log T ^ n₁ := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply Real.rpow_nonneg
        rw[log_nonneg_iff Tpos]
        exact le_trans (by norm_num) (le_of_lt T_gt)
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) (Real.one_le_rpow ?_ n₁_pos.le)
        rw[Real.le_log_iff_exp_le Tpos]
        linarith [Real.exp_one_lt_d9]
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹),
      ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        rw [uIoc_of_le interval_length_nonneg]
        exact this
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        · rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
          calc
            1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
            _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ n₂ := has_bound σ (-T)
          (by simp only [abs_neg]; rw [abs_of_pos Tpos]; exact T_gt)
          (by unfold σ₁ at hσ; simp only [mem_Ioc, abs_neg, log_abs, mem_Ici,
            tsub_le_iff_right] at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ n₂ := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith[one_add_inv_log X_gt.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          · simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
              sub_zero]
            rw [← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
            · exact hσ.2
            · refine (Real.log_pos ?_).ne.symm
              linarith
            · apply Real.log_pos
              linarith
            · linarith
            · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          · exact this
          · exact ε_pos
          · positivity
          · apply mul_pos ε_pos
            exact lt_of_lt_of_le (pow_pos Tpos 2) this
          · positivity
        _ = C' * X / (ε * T) := by
          field_simp

           
                   
                   
                                   
    
                                                                 
   
    
     
                                                                                       
                        
lemma I8I2 {SmoothingF : ℝ → ℝ}
    {X ε T σ₁ : ℝ} (T_gt : 3 < T) :
    I₈ SmoothingF ε X T σ₁ = -conj (I₂ SmoothingF ε X T σ₁) := by
  unfold I₂ I₈
  rw[map_mul, ← neg_mul]
  congr
  · simp[conj_ofNat]
  · rw[← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw[← smoothedChebyshevIntegrand_conj]
    · simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    · exact lt_trans (by norm_num) T_gt

def I8BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)

                        
                         
                   
                                                                                     
    
                                                            
    
     
               
                                                                                                    
     
                        
lemma I8GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound n₁ n₂ A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    I8BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C, hC, i2Bound⟩ := I2GenBound suppSmoothingF ContDiffSmoothingF n₁_pos n₂_pos has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
  exact i2Bound

                                        
                                         
                   
                                      
                          
     
               
                                                                                                               
                                     
                                    
                                        
             
     
                        
lemma Real.log_le_const_mul_rpow {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Real.log x ≤ c * x ^ (1 / c) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (1 / c)); rw [Real.log_rpow hx] at h
  have h' := mul_le_mul_of_nonneg_left h hc.le; field_simp at h'
  nlinarith [Real.rpow_pos_of_pos hx (1 / c)]

           
                                                
                   
                                                                            
    
                                      
    
     
               
                                                                
                                             
                              
                                                
                                                                                    
     
                        
lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℝ, (n_pos : 0 < n) →
    ∃ C : ℝ, 0 < C ∧ ∀ T > 3, ∫ x in Ioo 3 T, (Real.log x) ^ n / x ^ 2 < C := by
  intro n n_pos
  set c : ℝ := 2 * n with cDef
  have cpos : 0 < c := by linarith
  set g : ℝ → ℝ := fun x => c ^ n * x ^ (-(3 / 2) : ℝ) with gDef
  have g_nonneg : ∀ x ∈ Ioi (3 : ℝ), 0 ≤ g x := by
    intro x hx; simp only [mem_Ioi] at hx
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  have gInt_nonneg : 0 ≤ ∫ x in Ioi (3 : ℝ), g x := setIntegral_nonneg measurableSet_Ioi g_nonneg
  have g_integrable : IntegrableOn g (Ioi 3) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)) _
  have g_mono : ∀ x ∈ Ioi (3 : ℝ), Real.log x ^ n / x ^ 2 ≤ g x := by
    intro x hx; simp only [mem_Ioi] at hx
    have xpos : 0 < x := by linarith
    have logxPos : 0 < Real.log x := by
      rw [Real.log_pos_iff xpos.le]
      linarith
    have logBnd := Real.rpow_le_rpow logxPos.le (Real.log_le_const_mul_rpow cpos xpos) n_pos.le
    rw [Real.mul_rpow cpos.le (Real.rpow_nonneg xpos.le _), ← Real.rpow_mul xpos.le, cDef] at logBnd
    field_simp at logBnd
    have : - ((3 : ℝ) / 2) = (1 / 2) - 2 := by norm_num
    simp only [cDef, gDef, this, Real.rpow_sub xpos, ← mul_div_assoc, rpow_ofNat]
    exact (div_le_div_iff_of_pos_right (sq_pos_iff.mpr (ne_of_gt xpos))).mpr logBnd
  refine ⟨1 + (∫ x in Ioi (3 : ℝ), g x), by linarith, fun T _ => ?_⟩
  calc
    _ ≤ ∫ (x : ℝ) in Ioo 3 T, g x := by
      refine setIntegral_mono_on (IntegrableOn.mono_set (ContinuousOn.integrableOn_Icc
        (ContinuousOn.div (ContinuousOn.rpow_const (ContinuousOn.log (continuousOn_id' _)
        (fun x hx ↦ ?_)) ?_) (ContinuousOn.fun_pow (continuousOn_id' _) _)
        (fun x hx ↦ pow_ne_zero _ ?_))) Ioo_subset_Icc_self)
        (IntegrableOn.mono_set g_integrable Ioo_subset_Ioi_self) measurableSet_Ioo
        (fun x hx ↦ g_mono x hx.1)
      · linarith [hx.1]
      · simp only [mem_Icc, ne_eq, log_eq_zero, not_or, n_pos.le, or_true, implies_true]
      · linarith [hx.1]
    _ ≤ ∫ (x : ℝ) in Ioi 3, g x := by
      refine setIntegral_mono_set g_integrable ?_ (LE.le.eventuallyLE Ioo_subset_Ioi_self)
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx ↦ g_nonneg x hx)
  linarith

def I3BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
      {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
      ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

set_option maxHeartbeats 400000 in
-- Slow

                        
                         
                   
                                                                                     
    
                                                                                          
    
     
               
                                                           
    
                                                     
                                    
                                                   
                                                   
                    
          
         
    
        
                
             
                     
                                       
              
       
   
    
                                                                                   
                                                                                                        
     
                        
theorem I3GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound n₁ n₂ A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    I3BoundGenProp n₁ SmoothingF A := by
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded n₂ n₂_pos
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have Xpos := zero_lt_three.trans Xgt3
  have Tgt3' : -T < -3 := neg_lt_neg_iff.mpr Tgt3

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      exact ht.2.trans (by norm_num)
    rw [← Set.neg_mem_Ioo_iff, mem_Ioo] at ht
    rwa [this]

  have logt2gt1_bounds :
      ∀ t, t ∈ Set.Icc (-T) (-3) → Real.log |t| ^ n₂ > 1 := by
    intro t ht
    refine Real.one_lt_rpow ?_ n₂_pos
    have : |t| = -t := by
        refine abs_of_neg ?_
        exact ht.2.trans_lt (by norm_num)
    rw [this, Real.lt_log_iff_exp_lt (by linarith [ht.2])]
    linarith [ht.2, Real.exp_one_lt_d9]

  have Aoverlogt2gtAoverlogT2_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ n₁ > A / Real.log T ^ n₁ := by
    intro t ht
    refine div_lt_div_of_pos_left hA.1 ?_ ?_
    · exact zero_lt_one.trans <| Real.one_lt_rpow (logt_gt_one ht.1.le) n₁_pos
    · have h1 := log_lt_log (zero_lt_three.trans ht.1) ht.2
      have h2 := logt_gt_one ht.1.le
      have h3 : 0 ≤ Real.log |t| := zero_le_one.trans h2.le
      apply Real.rpow_lt_rpow h3 h1 n₁_pos

  have AoverlogT1in0half: A / Real.log T ^ n₁ ∈ Ioo 0 (1/2) := by
    have logT1gt1 : 1 < Real.log T ^ n₁ := by
      have logt_gt_one : 1 < Real.log T := logt_gt_one Tgt3.le
      exact Real.one_lt_rpow logt_gt_one n₁_pos
    have logT9pos := zero_lt_one.trans logT1gt1
    constructor
    · exact div_pos hA.1 logT9pos
    · rw [div_lt_comm₀ logT9pos one_half_pos, div_lt_iff₀' one_half_pos]
      apply hA.2.trans_lt
      rwa [lt_mul_iff_one_lt_right one_half_pos]

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    linarith[AoverlogT1in0half.1]

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    linarith[AoverlogT1in0half.2]

  have quotient_bound :
      ∀ t ∈ Ioo (-T) (-3), Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ n₂ / t ^ 2 := by
    intro t ht
    have loght := logt2gt1_bounds t (Ioo_subset_Icc_self ht)
    have logpos : Real.log |t| ^ n₂ > 0 := zero_lt_one.trans loght
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := (le_add_iff_nonneg_left _).mpr <| sq_nonneg σ₁
    have denom_pos : 0 < t ^ 2 := by
      apply sq_pos_of_ne_zero
      rintro rfl
      norm_num [mem_Ioo] at ht
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) denom_pos
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have MellinBound : ∀ (t : ℝ),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ₁ + t * I)‖ ≤
        CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    refine CMhyp σ₁ σ₁pos _ ?_ ?_ _ εgt0 εlt1 <;> simp [σ₁lt1.le.trans one_le_two]

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ n₂ := by
    intro t tbounds
    apply hCζ
    · exact tbounds.1
    · unfold σ₁
      rw [mem_Ici, sub_le_sub_iff_left]
      exact (Aoverlogt2gtAoverlogT2_bounds t tbounds).le

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have bound_integral : ∀ t ∈ Ioo (-T) (-3), ‖f t‖ ≤ g t := by
    intro t ht
    unfold f

    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ n₂) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
        simp [norm_cpow_eq_rpow_re_of_pos Xpos]
      obtain ⟨ht_gt3, ht_ltT⟩ := t_bounds _ ht
      have logtgt1 : 1 < Real.log |t| := logt_gt_one ht_gt3.le
      have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
      have h𝓜 := MellinBound t
      rw[Xσ_bound]
      gcongr

    have : (Cζ * Real.log |t| ^ n₂) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f :
      ∫ (t : ℝ) in (-T)..(-3),
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑X ^ (↑σ₁ + ↑t * I) =
      ∫ (t : ℝ) in (-T)..(-3), f t := by
    simp only [f]
  rw[int_with_f]

  apply (norm_mul_le _ _).trans
  rw [Complex.norm_mul, Complex.norm_I, one_mul]

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ ≤ ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · simp only [one_div, norm_inv]
      apply inv_le_one_of_one_le₀
      simp only [Complex.norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs, pi_nonneg,
        abs_of_nonneg, norm_I, mul_one]
      apply one_le_mul_of_one_le_of_one_le one_le_two
      exact le_trans (by norm_num) pi_gt_three.le
  apply le_trans this

  apply le_trans (intervalIntegral.norm_integral_le_integral_norm Tgt3'.le)

  have ne_zero_of_mem_uIcc (x) (hx : x ∈ uIcc (-T) (-3)) : x ≠ 0 := by
    rintro rfl
    norm_num [mem_uIcc] at hx
    linarith

  have cont1 : ContinuousOn (fun t ↦ Real.log |t| ^ n₂) (uIcc (-T) (-3)) := by
    exact ContinuousOn.rpow (ContinuousOn.log continuous_abs.continuousOn (fun x hx ↦ abs_ne_zero.mpr (ne_zero_of_mem_uIcc x hx))) continuousOn_const (fun _ _ ↦ Or.inr n₂_pos)

  have g_cont : ContinuousOn g (uIcc (-T) (-3)) := by
    unfold g
    refine .mul ?_ continuousOn_const
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const.mul cont1
    · fun_prop
    · intro x hx
      apply mul_ne_zero εgt0.ne'
      have : 0 < σ₁ ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos σ₁pos) (sq_nonneg x)
      simp only [Complex.sq_norm, normSq_add_mul_I, ne_eq, this.ne', not_false_eq_true]

  have int_normf_le_int_g: ∫ (t : ℝ) in (-T)..(-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in (-T)..(-3), g ↑t := by
    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · exact intervalIntegral.integral_mono_on_of_le_Ioo
        Tgt3'.le h_int g_cont.intervalIntegrable bound_integral
    · rw [intervalIntegral.integral_undef h_int]
      apply intervalIntegral.integral_nonneg Tgt3'.le
      intro t ht
      unfold g
      have := logt2gt1_bounds t ht
      positivity

  apply le_trans int_normf_le_int_g
  unfold g

  simp only [σ₁]

  have : X ^ (1 - A / Real.log T ^ n₁) = X * X ^ (- A / Real.log T ^ n₁) := by
    rw [sub_eq_add_neg, Real.rpow_add Xpos, Real.rpow_one, neg_div]

  rw[this]

  have Bound_of_log_int: ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]

    have bound : ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      simp_rw [Complex.sq_norm, normSq_add_mul_I]

      have : ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in (-T)..(-3), Real.log |t| ^ n₂ /  t ^ 2 := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo Tgt3'.le ?_ ?_ ?_
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ n₂ / (σ₁ ^ 2 + t ^ 2)) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' _
            · intro t ht
              have h1 : 0 < t ^ 2 := pow_two_pos_of_ne_zero (ne_zero_of_mem_uIcc t ht)
              have h2 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              exact (add_pos_of_pos_of_nonneg h2 h1.le).ne'
          apply cont.intervalIntegrable
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ n₂ / t ^ 2) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' _
            · intro t ht
              exact pow_ne_zero 2 (ne_zero_of_mem_uIcc t ht)
          apply cont.intervalIntegrable
        · intro x hx
          exact quotient_bound x hx
      apply le_trans this
      rw [← intervalIntegral.integral_comp_neg]
      simp only [abs_neg, log_abs, even_two, Even.neg_pow]
      rw [intervalIntegral.integral_of_le Tgt3.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact (Cinthyp T Tgt3).le
    rw [mul_comm,
      ← mul_div_assoc, mul_one]

    exact (div_le_div_iff_of_pos_right εgt0).mpr bound

  have factor_out_constants :
  ∫ (t : ℝ) in (-T)..(-3), Cζ * CM * Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ^ n₁))
  = Cζ * CM * (X * X ^ (-A / Real.log T ^ n₁)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     simp only [log_abs]
     rw [← intervalIntegral.integral_const_mul]
     apply intervalIntegral.integral_congr
     intro t ht
     ring_nf

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T ^ n₁)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ n₂ / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T ^ n₁)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · positivity

  apply le_trans this
  ring_nf
  field_simp
  rfl

lemma I7I3 {SmoothingF : ℝ → ℝ} {ε X T σ₁ : ℝ} (Xpos : 0 < X) :
    I₇ SmoothingF ε T X σ₁ = conj (I₃ SmoothingF ε T X σ₁) := by
  unfold I₃ I₇
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj, ← intervalIntegral.integral_comp_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [← smoothedChebyshevIntegrand_conj Xpos]
    simp

def I7BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
      {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
      ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

                        
                         
                   
                                                                                     
    
                                                                                          
    
     
               
                                                                                                    
     
                        
theorem I7GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound n₁ n₂ A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    I7BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C, Cpos, bound⟩ := I3GenBound suppSmoothingF ContDiffSmoothingF n₁_pos n₂_pos hCζ Cζpos hA
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]

def I4BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

           
                         
                   
                                                                                     
    
                                                    
                                                         
    
     
               
                                                                                                
                                                                                  
                                                                                                  
                                                                                                  
                                                                                            
     
                        
lemma I4GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {n : ℝ} (n_pos : n > 0) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    I4BoundGenProp n SmoothingF A σ₂ := by
  have reOne : re 1 = 1 := rfl
  have imOne : im 1 = 0 := rfl
  have reThree : re 3 = 3 := rfl
  have imThree : im 3 = 0 := rfl

  unfold I4BoundGenProp I₄ SmoothedChebyshevIntegrand

  let S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1
  let C' : ℝ := sSup S
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -(ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        ((ζ' / ζ) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_singleton_iff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  obtain ⟨D, Dpos, MellinSmooth1bBound⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  let C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)
  use C
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnnorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[(by ring : σ₂ - σ₂ * x + x - I * 3 = σ₂ - σ₂ * x + (x - I * 3))] at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := temp
        positivity
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert sInfPos.le using 5
      norm_cast
  use CNonneg

  let Tlb : ℝ := max 4 (max (rexp (A ^ (n : ℝ)⁻¹)) (rexp ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹)))
  use Tlb

  have : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  use this

  intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb ^ n := by
      have : rexp ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹) ≤ Tlb := by
        unfold Tlb
        nth_rewrite 2 [max_comm]
        rw[max_left_comm]
        apply le_max_of_le_left (by rfl)
      rw[← Real.le_log_iff_exp_le] at this
      · have h1 : 0 ≤ (A / (1 - σ₂)) ^ (n : ℝ)⁻¹ := by apply Real.rpow_nonneg (by exact expr_nonneg)
        rw[← Real.rpow_le_rpow_iff h1 logTlb_nonneg n_pos] at this
        have h: ((A / (1 - σ₂)) ^ (n : ℝ)⁻¹) ^ (n : ℝ) = A / (1 - σ₂) := by
          apply rpow_inv_rpow (by exact expr_nonneg)
          exact Ne.symm (Std.ne_of_lt n_pos)
        rw[h, div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · linarith
        · exact rpow_pos_of_pos (by exact logTlb_pos) _
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ^ n ≤ 1 - A / Real.log T ^ n := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · apply Real.rpow_pos_of_pos
        apply Real.log_pos
        linarith
      · exact Real.rpow_le_rpow logTlb_nonneg (log_le_log (by linarith) T_gt_Tlb.le) n_pos.le
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    apply Real.rpow_pos_of_pos
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T ^ n) / ε = 1 * (C * X * X ^ (-A / Real.log T ^ n) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg pi_nonneg, Complex.norm_I, mul_one]
    have : 1 / (2 * π) < 1 / 6 := by
      rw[_root_.one_div_lt_one_div]
      · refine (div_lt_iff₀' ?_).mp ?_
        · norm_num
        ring_nf
        refine gt_iff_lt.mpr ?_
        exact Real.pi_gt_three
      · positivity
      · norm_num
    exact le_of_lt (lt_trans this (by norm_num))
  · let f : ℝ → ℂ := fun σ ↦ (-ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T ^ n) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T ^ n) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul]
        have : C * X * X ^ (-A / Real.log T ^ n) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T ^ n)) := by ring
        rw[this]
        have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I) =
              𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s := rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T ^ n) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]
                · rw[zero_mul, neg_zero, Real.exp_zero]
                  simp only [inv_one, mul_one]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    ring_nf at xInIoc
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T ^ n) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T ^ n) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  · simp only [norm_nonneg]
  norm_num

lemma I6I4 {SmoothingF : ℝ → ℝ} {ε X σ₁ σ₂ : ℝ} (Xpos : 0 < X) :
    I₆ SmoothingF ε X σ₁ σ₂ = -conj (I₄ SmoothingF ε X σ₁ σ₂) := by
  unfold I₆ I₄
  simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_one, conj_ofNat]
  rw [← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp [conj_ofNat]

def I6BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε

                        
                         
                   
                                                                                     
    
                                                    
                                                         
    
     
               
                                                                                                    
     
                        
lemma I6GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {n : ℝ} (n_pos : 0 < n) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    I6BoundGenProp n SmoothingF A σ₂ := by
  obtain ⟨C, Cpos, Tlb, Tlb_gt, bound⟩ := I4GenBound suppSmoothingF ContDiffSmoothingF h_logDeriv_holo hσ₂ n_pos hA
  refine ⟨C, Cpos, Tlb, Tlb_gt, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]

def I5BoundGenProp (SmoothingF : ℝ → ℝ) (σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε

           
                      
                   
              
    
                                                                            
    
     
               
                                                                                              
                                                                                          
                                                                                                   
     
                        
lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1) :
    I5BoundGenProp SmoothingF σ₂ := by
  unfold LogDerivZetaIsHoloSmall HolomorphicOn at h_logDeriv_holo
  let zeta'_zeta_on_line := fun (t : ℝ) ↦ ζ' (σ₂ + t * I) / ζ (σ₂ + t * I)

  have subst : {σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
    simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, neg_le_self_iff,
      Nat.ofNat_nonneg, uIcc_of_le]
    intro z hyp_z
    simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · constructor
      · rw [hyp_z.1]
        apply left_mem_uIcc
      · exact hyp_z.2
    · push Not
      by_contra h
      rw [h] at hyp_z
      simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
      linarith [hσ₂.2]

  have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn

  have is_compact' : IsCompact ({σ₂} ×ℂ uIcc (-3) 3) := by
    refine IsCompact.reProdIm ?_ ?_
    · exact isCompact_singleton
    · exact isCompact_uIcc

  let ⟨zeta_bound, zeta_prop⟩ :=
    IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

  let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

  unfold I5BoundGenProp I₅ SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith[hσ₂.2]))

  simp only [mul_inv_rev] at mellin_prop

  let Const := 1 + (σ₂^2)⁻¹ * (abs zeta_bound) * M

  let C := |π|⁻¹ * 2⁻¹ * 6 * Const
  use C
  have C_pos : 0 < C := by positivity
  use C_pos

  clear C_pos

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < σ₂^2 := by
    exact sq_pos_of_pos (by linarith[hσ₂.1])

  have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        simp only [le_add_iff_nonneg_right]
        exact zpow_two_nonneg t
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        positivity
      positivity

  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
    intro t hyp_t
    have Z := by
      calc
        ‖(-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)) * (𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · trivial
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z

  -- Now want to apply the triangle inequality
  -- and bound everything trivially
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε := by
    unfold C
    ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)

def LogDerivZetaBoundedAndHoloGenProp (n₁ n₂ : ℝ) : Prop := ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound n₁ n₂ A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ n₁) 2)  ×ℂ (Icc (-T) T) ) \ {1})

lemma LogDerivZetaBoundedAndHoloGen {n₁ n₂ : ℝ}
  (LogDerivZetaBndUnif : LogDerivZetaBndUnifGenProp n₁ n₂)
  (LogDerivZetaHolcLargeT : LogDerivZetaHolcLargeTGenProp n₁) :
  LogDerivZetaBoundedAndHoloGenProp n₁ n₂ := by
  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd⟩ := LogDerivZetaBndUnif
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  · intro σ T hT hσ
    apply zeta_bnd _ _ hT
    apply mem_Ici.mpr (le_trans _ hσ)
    gcongr
    · bound
    · apply min_le_left
  · intro T hT
    apply (holo _ hT).mono
    intro s hs
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_reProdIm] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    refine ⟨?_, hs.1.1.2⟩
    apply le_trans _ hs.1.1.1
    gcongr
    · bound
    · apply min_le_right

lemma LogDerivZetaBoundedAndHolo99 : LogDerivZetaBoundedAndHoloGenProp 9 9 := by
  exact LogDerivZetaBoundedAndHoloGen LogDerivZetaBndUnif99 LogDerivZetaHolcLargeT9

lemma MellinOfSmooth1cExplicit {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
    ∀ ε ∈ Ioo 0 ε₀, ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1‖ ≤ c * ε := by
  have := MellinOfSmooth1c diffν suppν mass_one
  rw [Asymptotics.isBigO_iff'] at this
  rcases this with ⟨c, cpos, hc⟩
  unfold Filter.Eventually at hc
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hc
  rcases hc with ⟨ε₀, ε₀pos, h⟩
  refine ⟨ε₀, c, ε₀pos, cpos, fun ε hε ↦ ?_⟩
  specialize h hε
  rw [mem_setOf_eq, id_eq, norm_of_nonneg hε.1.le] at h
  exact h

open Filter Topology

-- `x * rexp (-c * (log x) ^ B)) = Real.exp (Real.log x - c * (Real.log x) ^ B))`
-- so if `B < 1`, the exponent goes to infinity
lemma x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
  have coeff_to_zero {B : ℝ} (B_le : B < 1) :
      Tendsto (fun x ↦ Real.log x ^ (B - 1)) atTop (𝓝 0) := by
    have B_minus_1_neg : B - 1 < 0 := by linarith
    rw [← Real.zero_rpow (ne_of_lt B_minus_1_neg),
      zero_rpow (ne_of_lt B_minus_1_neg)]

    have one_minus_B_pos : 0 < 1 - B := by linarith
    rw [show B - 1 = -(1 - B) by ring]
    have : ∀ᶠ (x : ℝ) in atTop, Real.log x ^ (-(1 - B)) = (Real.log x ^ ((1 - B)))⁻¹ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      apply Real.rpow_neg
      exact Real.log_nonneg hx
    rw [tendsto_congr' this]
    apply tendsto_inv_atTop_zero.comp
    apply (tendsto_rpow_atTop one_minus_B_pos).comp
    exact tendsto_log_atTop

  have log_sub_log_pow_inf (c : ℝ) {B : ℝ} (B_le : B < 1) :
      Tendsto (fun (x : ℝ) ↦ Real.log x - c * Real.log x ^ B) atTop atTop := by
    have factor_form : ∀ x > 1, Real.log x - c * Real.log x ^ B =
        Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      intro x hx
      ring_nf
      congr! 1
      rw [mul_assoc, mul_comm (Real.log x), mul_assoc]
      congr! 1
      have log_pos : 0 < Real.log x := Real.log_pos hx
      rw [(by simp : Real.log x ^ (-1 + B) * Real.log x =
        Real.log x ^ (-1 + B) * (Real.log x) ^ (1 : ℝ))]
      rw [← Real.rpow_add log_pos]
      ring_nf
    have coeff_to_one : Tendsto (fun x ↦ 1 - c * Real.log x ^ (B - 1)) atTop (𝓝 1) := by
      specialize coeff_to_zero B_le
      apply Tendsto.const_mul c at coeff_to_zero
      convert (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub coeff_to_zero
      ring

    have eventually_factored : ∀ᶠ x in atTop, Real.log x - c * Real.log x ^ B =
    Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact factor_form x hx

    rw [tendsto_congr' eventually_factored]
    apply Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) tendsto_log_atTop  coeff_to_one

  have x_εx_eq (c B : ℝ) : ∀ᶠ (x : ℝ) in atTop, x * rexp (-c * Real.log x ^ B) =
        rexp (Real.log x - c * Real.log x ^ B) := by
    filter_upwards [eventually_gt_atTop 0] with x hx_pos
    conv =>
      enter [1, 1]
      rw [(Real.exp_log hx_pos).symm]
    rw [← Real.exp_add]
    ring_nf

  rw [tendsto_congr' (x_εx_eq c B)]
  exact tendsto_exp_atTop.comp (log_sub_log_pow_inf c B_le)

                  /- 
\section{MediumPNT}
-/

                            
                             
                   
                                                                                       
                                                                     
     
               
                                                                           
                                                 
                                                                                    
                                        
                                                                                          
                                                                                       
                                      
                                                                                              
                                                  
                                                                 
                                                       
                                                                           
      
lemma GenStrengthPNT {n₁ n₂ : ℝ}
  (LogDerivZetaBoundedAndHolo : LogDerivZetaBoundedAndHoloGenProp n₁ n₂)
  (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) : ∃ c > 0,
  (ψ - id) =O[atTop]
    fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))) := by
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := LogDerivZetaBoundedAndHolo
  obtain ⟨σ₂, σ₂InIoo, holo2⟩ := LogDerivZetaHolcSmallT'
  obtain ⟨c_close, c_close_pos, h_close⟩ := SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩  := MellinOfSmooth1cExplicit ContDiff1ν ν_supp ν_massOne

  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  σ₂InIoo
  obtain ⟨c₇, c₇pos, hc₇⟩ := I7GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₈, c₈pos, hc₈⟩ := I8GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne

  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4GenBound ν_supp ContDiff1ν holo2 σ₂InIoo n₁_pos A_in_Ioc
  obtain ⟨c₆, c₆pos, Tlb₆, Tlb₆bnd, hc₆⟩ := I6GenBound ν_supp ContDiff1ν holo2 σ₂InIoo n₁_pos A_in_Ioc

  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇

  let c : ℝ := A ^ ((1 : ℝ) / (1 + n₁)) / 4
  have cpos : 0 < c := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, Nat.ofNat_pos, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, c]
    obtain ⟨left, right⟩ := A_in_Ioc
    positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩

  let c_εx : ℝ := A ^ ((1 : ℝ) / (1 + n₁)) / 2
  have c_εx_pos : 0 < c_εx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, Nat.ofNat_pos, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, c, c_εx]
  let c_Tx : ℝ := A ^ ((1 : ℝ) / (1 + n₁))
  have c_Tx_pos : 0 < c_Tx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, Nat.ofNat_pos, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, c, c_εx, c_Tx]

  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))))

  have one_div_succ_n₁_pos : 0 < (1 : ℝ) / (1 + n₁) := by
    simp only [one_div, inv_pos]
    linarith

  have one_div_succ_n₁_lt_one : (1 : ℝ) / (1 + n₁) < 1 := by
    rw [one_div, inv_lt_one₀ (one_div_pos.mp one_div_succ_n₁_pos)]
    norm_num [n₁_pos]

  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop one_div_succ_n₁_pos).comp Real.tendsto_log_atTop

  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x) : -c_εx * Real.log x ^ ((1 : ℝ) / (1 + n₁)) = -(c_εx * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    exact (tendsto_rpow_atTop one_div_succ_n₁_pos).comp tendsto_log_atTop

  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num

  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx one_div_succ_n₁_lt_one
    exact this.eventually_gt_atTop 2

  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3

  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _

  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) ^ n₁ := by
    apply (tendsto_order.mp ?_).1
    · exact σ₂InIoo.2
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop n₁_pos).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp only [comp_apply, div_eq_mul_inv]
    · simp

  have eventually_ε_lt_ε_main : ∀ᶠ (x : ℝ) in atTop, εx x < ε_main := by
    apply (tendsto_order.mp ex_to_zero).2
    assumption

  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop

  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 10] with x hx x_gt
        convert hx using 1
        · rw [Real.norm_of_nonneg]
          exact Real.log_nonneg (logt_gt_one (by linarith)).le
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp

  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this,
        mul_assoc]

      grw [hx]
      simp

  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c εx c_εx
    have const1bnd : (A ^ ((1 : ℝ) / (1 + n₁)) / 4) < (A ^ ((1 : ℝ) / (1 + n₁)) / 2) := by
        linarith
    have this (x) :
      C' * rexp (-(A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd one_div_succ_n₁_pos, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]

  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / (1 + n₁)
    have const2bnd : 0 < const2 := one_div_succ_n₁_pos
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have this (x) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]

  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / (1 + n₁))
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (n₁ : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul, Real.log_exp, Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (n₁ : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le,
          div_eq_mul_inv]

        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos, const2_eq]
        field_simp
        ring_nf
      rw [div_mul_eq_div_div, neg_div, this (A_in_Ioc.1), mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div, this (y := Real.log x) logxpos, ← Real.exp_add]
      apply Real.exp_monotone
      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]
      gcongr
      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      positivity
    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith

  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ^ n₁) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / (1 + n₁) with const2eq
    set const1 := (A ^ const2 / 2) with const1eq
    set const1' := (A ^ const2 / 4) with const1'eq
    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]
    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt
    have this (x) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ n₁)
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (n₁ : ℝ))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      ring
    rw [this]
    grw [x_bnd]

  have event_4_aux4 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      Tendsto (fun x ↦ c' * Real.log x ^ pow2) atTop (𝓝 0) := by
    rw [← mul_zero c']
    apply Tendsto.const_mul
    have := tendsto_rpow_neg_atTop (y := -pow2) (by linarith)
    rw [neg_neg] at this
    apply this.comp
    exact Real.tendsto_log_atTop

  have event_4_aux3 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      ∀ᶠ (x : ℝ) in atTop, c' * (Real.log x) ^ pow2 < c := by
    apply (event_4_aux4 pow2_neg cpos c').eventually_lt_const
    exact cpos

  have event_4_aux2 {c1 : ℝ} (c1pos : 0 < c1) (c2 : ℝ) {pow1 : ℝ} (pow1_lt : pow1 < 1) :
      ∀ᶠ (x : ℝ) in atTop, 0 ≤ Real.log x * (c1 - c2 * (Real.log x) ^ (pow1 - 1)) := by
    filter_upwards [eventually_gt_atTop 3 , event_4_aux3 (by linarith : pow1 - 1 < 0)
      (by linarith : 0 < c1 / 2) c2] with x x_gt hx
    have : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      linarith
    apply mul_nonneg this
    linarith

  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    filter_upwards [event_4_aux2 (by linarith : 0 < 1 - const1) (const2 + const3) pow1_lt,
      eventually_gt_atTop 3] with x hx x_gt
    have :
      Real.log x - const3 * Real.log x ^ pow1 - (const1 * Real.log x + const2 * Real.log x ^ pow1)
      = (1 - const1) * Real.log x - (const2 + const3) * Real.log x ^ pow1 := by ring
    rw [← sub_nonneg, this]
    convert hx using 1
    ring_nf
    congr! 1
    · have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
          = const2 * Real.log x ^ pow1 := by
        rw [mul_assoc, mul_comm, mul_assoc]
        congr! 1
        conv =>
          enter [1, 2]
          rw [← Real.rpow_one (Real.log x)]
        rw [← Real.rpow_add (Real.log_pos (by linarith))]
        ring_nf
      rw [this]
    have : Real.log x * const3 * Real.log x ^ (-1 + pow1)
        = const3 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]

  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / (1 + n₁)) / 4) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂InIoo.2 (A ^ ((1 : ℝ) / (1 + n₁)) / 2)
      (A ^ ((1 : ℝ) / (1 + n₁)) / 4) one_div_succ_n₁_lt_one] with x x_gt hx
    rw [mul_le_mul_iff_right₀ c₅pos]
    apply Real.exp_monotone
    convert hx

  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf
    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf

  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4

  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge

  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X

  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T) ^ n₁
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T) ^ n₁ >= 1 - (1/2) / 1 ^ n₁ := by
      gcongr
      · exact A_in_Ioc.2
      · exact (logt_gt_one T_gt_3.le).le
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound

  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith [mem_reProdIm.mp hs.1 |>.1.1, σ₂InIoo.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1 ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂InIoo.1 σ₁_lt_one σ₂_lt_σ₁ holo1 holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    rw [(by ring : I₁ ν ε X T - I₂ ν ε T X σ₁ + I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂ = (I₁ ν ε X T - I₂ ν ε T X σ₁) + (I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂))]
    apply le_trans (by apply norm_add_le)
    rw [(by ring : ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ =
      (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖) + (‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖))]
    gcongr <;> apply le_trans (by apply norm_sub_le) <;> rfl
  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]

  have C'''bnd : c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T ^ n₁) / ε := by
    apply le_of_eq
    ring

  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X)
                  + (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖
                  + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! h_close using 1
      rw [← norm_neg]
      congr
      ring
    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

/-- *** Prime Number Theorem (Medium Strength) *** The `ChebyshevPsi` function is asymptotic to `x`. -/
           
                        
                   
           
                                                                 
     
               
                                                                                                
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  have := GenStrengthPNT LogDerivZetaBoundedAndHolo99 (by linarith) (by linarith); ring_nf at this
  simpa only [gt_iff_lt, one_div, neg_mul] using this

#print axioms MediumPNT

end Flat_PrimeNumberTheoremAnd_MediumPNT
#eval "COMPLETED PrimeNumberTheoremAnd.MediumPNT"

namespace Erdos374.ExternalInputs149
theorem psiMediumPNT :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop]
        (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
  exact MediumPNT
end Erdos374.ExternalInputs149
#print axioms Erdos374.ExternalInputs149.psiMediumPNT

end Update150_Component_4
/- END COMPONENT: PNTMathlib149.lean -/

/- BEGIN COMPONENT: OtherInputsHECFlat.lean -/
section Update150_Component_5

















set_option maxHeartbeats 1000000

/- Port of math-inc/RiemannHypothesisCurves commit c99880dff2a087d59147ab832074379ac28f7e68.
The original source and separate module ports are retained under work/external.
Imports are narrowed and proof-term compatibility repairs target Lean4.35.0-rc2. -/

/- BEGIN PORTED MODULE HasseDerivatives -/

noncomputable def hasseDerivOp (F : Type*) [Field F] (k : ℕ) : Polynomial F → Polynomial F :=
  fun p => (Polynomial.hasseDeriv k) p

lemma sum_hasseDeriv_piAntidiag_eq_sum_fin
    (F : Type*) [Field F] (k r : ℕ) (f : Fin r → Polynomial F) :
    (∑ j ∈ ((Finset.univ : Finset (Fin r)).piAntidiag k),
        (Finset.univ : Finset (Fin r)).prod
          (fun i => hasseDerivOp F (j i) (f i)))
      =
      (∑ j ∈ (((Finset.univ : Finset (Fin r → Fin (k + 1)))).filter
                  (fun j =>
                    ((Finset.univ : Finset (Fin r)).sum (fun i => (j i).val)) = k)),
          (Finset.univ : Finset (Fin r)).prod
            (fun i => hasseDerivOp F ((j i).val) (f i))) :=
by
  let phi :
      (j : Fin r → ℕ) →
      j ∈ ((Finset.univ : Finset (Fin r)).piAntidiag k) →
      (Fin r → Fin (k + 1)) :=
    fun j hj i =>
      ⟨j i,
        Nat.lt_succ_of_le <|
          by
            have hj_sum :
                (Finset.univ : Finset (Fin r)).sum j = k :=
              (Finset.mem_piAntidiag.mp hj).1
            simpa [hj_sum] using
              (Finset.single_le_sum_of_canonicallyOrdered
                (f := j) (s := (Finset.univ : Finset (Fin r))) (i := i) (by simp))⟩
  refine
    Finset.sum_bij (fun j hj => phi j hj) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_piAntidiag.mp hj with ⟨hj_sum, -⟩
    simp [phi, hj_sum]
  · intro j₁ _ j₂ _ h_eq
    funext i
    simpa [phi] using congrArg (fun g => (g i).val) h_eq
  · intro j' hj'
    refine ⟨fun i => (j' i).val, ?_, ?_⟩
    · rcases Finset.mem_filter.mp hj' with ⟨_, hP⟩
      refine Finset.mem_piAntidiag.mpr ?_
      refine ⟨hP, ?_⟩
      intro i _
      simp
    · ext i
      simp [phi]
  · intro j _
    simp [phi]

lemma hasseLeibniz_general (F : Type*) [Field F] (k r : ℕ) (f : Fin r → Polynomial F) :
  hasseDerivOp F k ((Finset.univ : Finset (Fin r)).prod (fun i => f i)) =
    Finset.sum
      (((Finset.univ : Finset (Fin r → Fin (k + 1)))).filter
        (fun j => ((Finset.univ : Finset (Fin r)).sum (fun i => (j i).val)) = k))
      (fun j => (Finset.univ : Finset (Fin r)).prod
        (fun i => hasseDerivOp F ((j i).val) (f i))) :=
by
  have hasseLeibniz_piAntidiag_finset :
      ∀ (s : Finset (Fin r)) (k : ℕ),
        hasseDerivOp F k (s.prod f) =
          ∑ j ∈ s.piAntidiag k,
            s.prod fun i => hasseDerivOp F (j i) (f i) := by
    intro s
    refine Finset.cons_induction ?h_empty ?h_cons s
    · intro k
      cases k with
      | zero =>
          simp [hasseDerivOp]
      | succ k =>
          simpa [hasseDerivOp,
            Finset.piAntidiag_empty_of_ne_zero (Nat.succ_ne_zero _)] using
            (Polynomial.hasseDeriv_C (R := F) (k := Nat.succ k) (r := (1 : F))
              (Nat.succ_pos _))
    · intro a s ha ih k
      let u : Finset (Fin r) := Finset.cons a s ha
      have hmul :
          hasseDerivOp F k (u.prod f) =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                hasseDerivOp F p.2 (s.prod f) := by
        have hprod : u.prod f = f a * s.prod f := by
          simpa [u] using
            (Finset.prod_cons (s := s) (a := a) (f := f) ha)
        simpa [hasseDerivOp, hprod] using
          (Polynomial.hasseDeriv_mul (R := F) (k := k)
            (f := f a) (g := s.prod f))
      have hL :
          hasseDerivOp F k (u.prod f) =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        refine (hmul.trans ?_)
        refine Finset.sum_congr rfl ?_
        intro p hp
        simp [ih p.2]
      let w : (Fin r → ℕ) → Polynomial F :=
        fun j => u.prod fun i => hasseDerivOp F (j i) (f i)
      have hR1 :
          ∑ j ∈ u.piAntidiag k, w j =
            ∑ p ∈ Finset.antidiagonal k,
              ∑ j ∈ (s.piAntidiag p.2).map
                      (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j := by
        let t : (ℕ × ℕ) → Finset (Fin r → ℕ) :=
          fun p =>
            (s.piAntidiag p.2).map
              (addRightEmbedding (fun t => if t = a then p.1 else 0))
        have hpw :
            (↑(Finset.antidiagonal k) : Set (ℕ × ℕ)).PairwiseDisjoint t := by
          simpa [t] using
            (Finset.pairwiseDisjoint_piAntidiag_map_addRightEmbedding
              (i := a) (s := s) (hi := ha) (n := k))
        have hsd :
            ∑ j ∈ (Finset.antidiagonal k).biUnion t, w j =
              ∑ p ∈ Finset.antidiagonal k,
                ∑ j ∈ t p, w j := by
          simpa [t] using
            (Finset.sum_biUnion
              (s := Finset.antidiagonal k)
              (t := t)
              (hs := hpw)
              (f := w))
        have hpi :
            u.piAntidiag k = (Finset.antidiagonal k).biUnion t := by
          simpa [u, t, Finset.disjiUnion_eq_biUnion] using
            (Finset.piAntidiag_cons (i := a) (s := s) (hi := ha) (n := k))
        simpa [hpi, t] using hsd
      have h_inner :
          ∀ p ∈ Finset.antidiagonal k,
            (∑ j ∈ (s.piAntidiag p.2).map
                      (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j) =
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        intro p hp
        let e : (Fin r → ℕ) ↪ (Fin r → ℕ) :=
          addRightEmbedding (fun t => if t = a then p.1 else 0)
        have h_pointwise :
            ∀ g ∈ s.piAntidiag p.2,
              w (e g) =
                hasseDerivOp F p.1 (f a) *
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
          intro g hg
          obtain ⟨-, hmem⟩ : s.sum g = p.2 ∧ ∀ i, g i ≠ 0 → i ∈ s := by
            simpa [Finset.mem_piAntidiag] using hg
          have hga : g a = 0 := by
            by_contra hne
            exact ha (hmem a hne)
          have hsplit :
              u.prod (fun i => hasseDerivOp F (e g i) (f i)) =
                hasseDerivOp F (e g a) (f a) *
                  s.prod fun i => hasseDerivOp F (e g i) (f i) := by
            simpa [u] using
              (Finset.prod_cons
                (s := s) (a := a)
                (f := fun i => hasseDerivOp F (e g i) (f i))
                ha)
          have h_on_s :
              ∀ i ∈ s, e g i = g i := by
            intro i hi
            have hne : i ≠ a := by
              intro h
              subst h
              exact ha hi
            simp [e, hne]
          have hprod_s :
              s.prod (fun i => hasseDerivOp F (e g i) (f i)) =
                s.prod fun i => hasseDerivOp F (g i) (f i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            simp [h_on_s i hi]
          have h_at_a : e g a = p.1 := by
            simp [e, hga]
          simp [w, hsplit, h_at_a, hprod_s]
        calc
          ∑ j ∈ (s.piAntidiag p.2).map
                    (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j =
              ∑ g ∈ s.piAntidiag p.2, w (e g) := by simp [w, e]
          _ =
              ∑ g ∈ s.piAntidiag p.2,
                hasseDerivOp F p.1 (f a) *
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
                refine Finset.sum_congr rfl ?_
                intro g hg
                simpa using h_pointwise g hg
          _ = hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
                simp [Finset.mul_sum]
      have hR :
          ∑ j ∈ u.piAntidiag k, w j =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        refine (hR1.trans ?_)
        refine Finset.sum_congr rfl ?_
        intro p hp
        simpa using h_inner p hp
      simpa [u, w] using hL.trans hR.symm
  simpa using
    (hasseLeibniz_piAntidiag_finset (Finset.univ : Finset (Fin r)) k).trans
      (sum_hasseDeriv_piAntidiag_eq_sum_fin F k r f)

lemma hasseDerivOp_X_sub_C_pow (F : Type*) [Field F]
    (k r : ℕ) (hk : k ≤ r) :
    ∀ a : F,
      hasseDerivOp F k ((Polynomial.X - Polynomial.C a)^r) =
        Polynomial.C (Nat.choose r k : F) * (Polynomial.X - Polynomial.C a)^(r - k) :=
by
  intro a
  ext n
  have hL :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        ((n + k).choose k : F) *
          ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) := by
    simpa [hasseDerivOp] using
      (Polynomial.hasseDeriv_coeff (k := k)
        (f := (Polynomial.X - Polynomial.C a) ^ r) (n := n))
  have hcoeff_pow :
      ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) =
        (-a) ^ (r - (n + k)) * (Nat.choose r (n + k) : F) := by
    simpa [sub_eq_add_neg] using
      (Polynomial.coeff_X_add_C_pow (R := F) (-a) r (n + k))
  have hcoeff_pow2 :
      ((Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
        (-a) ^ ((r - k) - n) * (Nat.choose (r - k) n : F) := by
    simpa [sub_eq_add_neg] using
      (Polynomial.coeff_X_add_C_pow (R := F) (-a) (r - k) n)
  have hL' :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        (-a) ^ (r - (n + k)) *
          (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) := by
    calc
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
          ((n + k).choose k : F) *
            ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) := hL
      _ = ((n + k).choose k : F) *
            ((-a) ^ (r - (n + k)) * (Nat.choose r (n + k) : F)) := by
            simp [hcoeff_pow]
      _ = (-a) ^ (r - (n + k)) *
            (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) := by
            ring
  have hR' :
      (Polynomial.C (Nat.choose r k : F) *
          (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
        (-a) ^ (r - (n + k)) *
          ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
    calc
      (Polynomial.C (Nat.choose r k : F) *
            (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
          (Nat.choose r k : F) *
            ((Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n := by
            simp
      _ = (Nat.choose r k : F) *
            ((-a) ^ ((r - k) - n) * (Nat.choose (r - k) n : F)) := by
            simp [hcoeff_pow2]
      _ = (Nat.choose r k : F) *
            ((-a) ^ (r - (n + k)) * (Nat.choose (r - k) n : F)) := by
            have : (r - k) - n = r - (n + k) := by
              simp [Nat.add_comm, Nat.sub_sub]
            simp [this]
      _ = (-a) ^ (r - (n + k)) *
            ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
            ring
  have hscalar :
      (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) =
        (Nat.choose r k : F) * (Nat.choose (r - k) n : F) := by
    by_cases hnk : n + k ≤ r
    · have hsk : k ≤ n + k := Nat.le_add_left k n
      have h_nat :
          (Nat.choose r (n + k) * Nat.choose (n + k) k : ℕ) =
            Nat.choose r k * Nat.choose (r - k) n := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.choose_mul (n := r) (k := n + k) (s := k) hsk)
      have h_natF :
          ((Nat.choose r (n + k) * Nat.choose (n + k) k : ℕ) : F) =
            (Nat.choose r k * Nat.choose (r - k) n : ℕ) := by
        exact congrArg (fun x : ℕ => (x : F)) h_nat
      have h_main :
          (Nat.choose r (n + k) : F) * (Nat.choose (n + k) k : F) =
            (Nat.choose r k : F) * (Nat.choose (r - k) n : F) := by
        simpa [Nat.cast_mul] using h_natF
      simpa [mul_comm] using h_main
    · have hlt : r < n + k := Nat.lt_of_not_ge hnk
      have hlt' : r - k < n :=
        (add_lt_add_iff_right (a := k)).1
          (by simpa [Nat.sub_add_cancel hk] using hlt)
      simp [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt hlt']
  have hmid :
      (-a) ^ (r - (n + k)) *
        (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) =
      (-a) ^ (r - (n + k)) *
        ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
    exact congrArg (fun x => (-a) ^ (r - (n + k)) * x) hscalar
  have hcoeff_eq :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        (Polynomial.C (Nat.choose r k : F) *
          (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n :=
    (hL'.trans hmid).trans hR'.symm
  simpa using hcoeff_eq

lemma hasseDerivOp_prod_single_polynomial_dvd
    (F : Type*) [Field F] (k r : ℕ)
    (g : Polynomial F)
    (j : Fin r → Fin (k + 1))
    (h_sum : (Finset.univ : Finset (Fin r)).sum (fun i => (j i).val) = k) :
    g^(r - k) ∣
      (Finset.univ : Finset (Fin r)).prod
        (fun i => hasseDerivOp F (j i).val g) :=
by
  let s : Finset (Fin r) := Finset.univ
  let Z : Finset (Fin r) := s.filter fun i => (j i).val = 0
  let NZ : Finset (Fin r) := s.filter fun i => (j i).val ≠ 0
  have hprod_split :
      Z.prod (fun i => hasseDerivOp F (j i).val g) *
        NZ.prod (fun i => hasseDerivOp F (j i).val g) =
      s.prod (fun i => hasseDerivOp F (j i).val g) :=
    Finset.prod_filter_mul_prod_filter_not
      (s := s)
      (p := fun i : Fin r => (j i).val = 0)
      (f := fun i => hasseDerivOp F (j i).val g)
  have hsum_decomp :
      Z.sum (fun i => (j i).val) + NZ.sum (fun i => (j i).val) =
        s.sum (fun i => (j i).val) :=
    Finset.sum_filter_add_sum_filter_not
      (s := s)
      (p := fun i : Fin r => (j i).val = 0)
      (f := fun i => (j i).val)
  have hZsum_zero :
      Z.sum (fun i => (j i).val) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simpa using (Finset.mem_filter.1 hi).2
  have hsum_NZ :
      NZ.sum (fun i => (j i).val) = k := by
    simpa [hZsum_zero] using hsum_decomp.trans h_sum
  have h_le_Zcard : r - k ≤ Z.card := by
    have hNZ_card_le_sum :
        NZ.card ≤ NZ.sum (fun i => (j i).val) := by
      have hones :
          NZ.card = NZ.sum (fun _ : Fin r => (1 : ℕ)) :=
        Finset.card_eq_sum_ones (s := NZ)
      have hterm :
          NZ.sum (fun _ : Fin r => (1 : ℕ)) ≤
            NZ.sum (fun i => (j i).val) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        obtain ⟨_, hne⟩ := Finset.mem_filter.1 hi
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
      rwa [hones.symm] at hterm
    have hNZ_card_le_k : NZ.card ≤ k := by
      simpa [hsum_NZ] using hNZ_card_le_sum
    have h_r_eq : r = Z.card + NZ.card := by
      have hcard_Z_NZ :
          Z.card + NZ.card = s.card :=
        Finset.card_filter_add_card_filter_not
          (s := s)
          (p := fun i : Fin r => (j i).val = 0)
      simpa [s] using hcard_Z_NZ.symm
    simpa [h_r_eq, Nat.add_comm] using
      Nat.sub_le_sub_left hNZ_card_le_k r
  have hZprod :
      Z.prod (fun i => hasseDerivOp F (j i).val g) = g ^ Z.card := by
    calc
      Z.prod (fun i => hasseDerivOp F (j i).val g)
          = Z.prod (fun _ : Fin r => g) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              obtain ⟨_, hzero⟩ := Finset.mem_filter.1 hi
              simp [hasseDerivOp, hzero]
      _ = g ^ Z.card :=
        Finset.prod_const (s := Z) (b := g)
  have hdiv_Z :
      g ^ (r - k) ∣ Z.prod (fun i => hasseDerivOp F (j i).val g) := by
    simpa [hZprod] using pow_dvd_pow g h_le_Zcard
  have :=
    dvd_mul_of_dvd_left hdiv_Z
      (NZ.prod fun i => hasseDerivOp F (j i).val g)
  simpa [s, hprod_split] using this

lemma hasseDerivOp_pow_dvd
    (F : Type*) [Field F] (k r : ℕ) :
    ∀ g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (g^r) :=
by
  intro g
  have hLeib' := hasseLeibniz_general F k r (fun _ : Fin r => g)
  simp [Finset.card_univ, Fintype.card_fin] at hLeib'
  rw [hLeib']
  refine Finset.dvd_sum ?_
  intro j hj
  simpa using hasseDerivOp_prod_single_polynomial_dvd F k r g j (Finset.mem_filter.1 hj).2

lemma hasseDerivOp_mul_pow_dvd (F : Type*) [Field F]
    (k r : ℕ) :
    ∀ f g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (f * g^r) :=
by
  intro f g
  have :
      g ^ (r - k) ∣
        ∑ p ∈ Finset.antidiagonal k,
          hasseDerivOp F p.1 f * hasseDerivOp F p.2 (g ^ r) := by
    refine Finset.dvd_sum ?_
    intro p hp
    have : p.2 ≤ k := by
      have : p.2 ≤ p.1 + p.2 := Nat.le_add_left _ _
      simpa [Finset.mem_antidiagonal.1 hp] using this
    refine dvd_mul_of_dvd_right
      (dvd_trans (pow_dvd_pow _ (Nat.sub_le_sub_left this _))
        (hasseDerivOp_pow_dvd (F := F) (k := p.2) (r := r) g)) _
  simpa [hasseDerivOp,
    ← Polynomial.hasseDeriv_mul (R := F) (k := k) (f := f) (g := g ^ r)] using this

lemma hasse_formulas (F : Type*) [Field F] (k r : ℕ) (hk : k ≤ r) :
  (∀ a : F,
      hasseDerivOp F k ((Polynomial.X - Polynomial.C a)^r) =
        Polynomial.C (Nat.choose r k : F) * (Polynomial.X - Polynomial.C a)^(r - k))
  ∧
  (∀ f g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (f * g^r) ∧
      Polynomial.degree ((hasseDerivOp F k (f * g^r)) / (g^(r - k))) ≤
        (match (Polynomial.degree f + (k : WithBot ℕ) * Polynomial.degree g) with
         | ⊥ => ⊥
         | some n => some (n - k))) :=
by
  constructor
  · intro a
    simpa using
      (hasseDerivOp_X_sub_C_pow (F := F) (k := k) (r := r) (hk := hk) (a := a))
  · intro f g
    constructor
    · simpa using
        (hasseDerivOp_mul_pow_dvd (F := F) (k := k) (r := r) f g)
    · by_cases hf : f = 0
      · subst hf
        simp [hasseDerivOp]
      · by_cases hg : g = 0
        · subst hg
          by_cases hr0 : r = 0
          · subst hr0
            have hk0 : k = 0 := Nat.le_antisymm hk (Nat.zero_le _)
            subst hk0
            have :
                Polynomial.degree f ≤
                  (match Polynomial.degree f with
                   | ⊥ => (⊥ : WithBot ℕ)
                   | some n => some (n - 0)) := by
              cases hdeg : Polynomial.degree f with
              | bot =>
                  simp
              | coe a =>
                  simp [hdeg, WithBot.some_eq_coe]
            simpa [hasseDerivOp] using this
          · simp [hasseDerivOp, hr0]
        · -- Main case: `f ≠ 0` and `g ≠ 0`.
          set num : Polynomial F := hasseDerivOp F k (f * g ^ r) with hnum
          set den : Polynomial F := g ^ (r - k) with hden
          have hdiv : den ∣ num := by
            have hdiv' : g ^ (r - k) ∣ hasseDerivOp F k (f * g ^ r) :=
              hasseDerivOp_mul_pow_dvd (F := F) (k := k) (r := r) f g
            simpa [hnum, hden] using hdiv'
          have hden_ne : den ≠ 0 := by
            have hg0 : g ≠ 0 := hg
            simpa [hden] using pow_ne_zero (r - k) hg0
          set q : Polynomial F := num / den with hq_def
          have h_deg_q :
              Polynomial.degree q ≤
                (match
                    Polynomial.degree f
                      + (k : WithBot ℕ) * Polynomial.degree g with
                 | ⊥ => (⊥ : WithBot ℕ)
                 | some n => some (n - k)) := by
            by_cases hq0 : q = 0
            · simp [hq0]
            · have hq_ne : q ≠ 0 := hq0
              have hnum_nat_le1 :
                  num.natDegree ≤ (f * g ^ r).natDegree - k := by
                simpa [hnum, hasseDerivOp] using
                  (Polynomial.natDegree_hasseDeriv_le (p := f * g ^ r) (n := k))
              have hmul_nat_le :
                  (f * g ^ r).natDegree ≤
                    f.natDegree + (g ^ r).natDegree :=
                Polynomial.natDegree_mul_le (p := f) (q := g ^ r)
              have hpow_nat_le :
                  (g ^ r).natDegree ≤ r * g.natDegree :=
                Polynomial.natDegree_pow_le (p := g) (n := r)
              have hfg_nat_le :
                  (f * g ^ r).natDegree ≤
                    f.natDegree + r * g.natDegree :=
                le_trans hmul_nat_le (Nat.add_le_add_left hpow_nat_le _)
              have hnum_nat_le :
                  num.natDegree ≤ f.natDegree + r * g.natDegree - k :=
                le_trans hnum_nat_le1 (Nat.sub_le_sub_right hfg_nat_le _)
              have hmul_eq : den * q = num := by
                simpa [hq_def] using
                  (EuclideanDomain.mul_div_cancel'
                    (R := Polynomial F) (a := num) (b := den) hden_ne hdiv)
              have hnum_nat_eq :
                  num.natDegree = den.natDegree + q.natDegree := by
                have := congrArg Polynomial.natDegree hmul_eq.symm
                simpa [Polynomial.natDegree_mul (p := den) (q := q) hden_ne hq_ne] using this
              have hden_nat : den.natDegree = (r - k) * g.natDegree := by
                simp [hden]
              have hsub_le :
                  num.natDegree - (r - k) * g.natDegree ≤
                    f.natDegree + r * g.natDegree - k
                      - (r - k) * g.natDegree :=
                Nat.sub_le_sub_right hnum_nat_le _
              have hq_eq :
                  num.natDegree - (r - k) * g.natDegree =
                    q.natDegree := by
                have : num.natDegree =
                    (r - k) * g.natDegree + q.natDegree := by
                  simpa [hden_nat, Nat.add_comm] using hnum_nat_eq
                simp [this]
              have hr : k + (r - k) = r := Nat.add_sub_of_le hk
              have hr_mul :
                  r * g.natDegree =
                    k * g.natDegree + (r - k) * g.natDegree := by
                calc
                  r * g.natDegree
                      = (k + (r - k)) * g.natDegree := by simp [hr]
                  _ = k * g.natDegree + (r - k) * g.natDegree := by
                        simp [Nat.add_mul]
              have hRHS_eq :
                  f.natDegree + r * g.natDegree - k
                      - (r - k) * g.natDegree =
                    f.natDegree + k * g.natDegree - k := by
                have h1 :
                    f.natDegree + r * g.natDegree - k
                        - (r - k) * g.natDegree =
                      f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree) := by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                      (tsub_add_eq_tsub_tsub
                        (a := f.natDegree + r * g.natDegree)
                        (b := k)
                        (c := (r - k) * g.natDegree)).symm
                have h2 :
                    f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree) =
                      f.natDegree + k * g.natDegree - k := by
                  calc
                    f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree)
                        = f.natDegree
                            + (k * g.natDegree + (r - k) * g.natDegree)
                            - (k + (r - k) * g.natDegree) := by
                            simp [hr_mul]
                    _ = f.natDegree + k * g.natDegree
                          + (r - k) * g.natDegree
                          - (k + (r - k) * g.natDegree) := by
                          simp [Nat.add_assoc]
                    _ = f.natDegree + k * g.natDegree - k := by
                      simpa [Nat.add_comm, Nat.add_left_comm,
                        Nat.add_assoc] using
                        (add_tsub_add_eq_tsub_right
                          (a := f.natDegree + k * g.natDegree)
                          (c := (r - k) * g.natDegree)
                          (b := k))
                exact h1.trans h2
              have hq_nat_le :
                  q.natDegree ≤ f.natDegree + k * g.natDegree - k := by
                have := hsub_le
                simpa [hq_eq, hRHS_eq] using this
              have hdeg_q' :
                  Polynomial.degree q ≤
                    ((f.natDegree + k * g.natDegree - k : ℕ) :
                      WithBot ℕ) :=
                (Polynomial.natDegree_le_iff_degree_le).1 hq_nat_le
              have hf_deg :
                  Polynomial.degree f =
                    (Polynomial.natDegree f : WithBot ℕ) :=
                Polynomial.degree_eq_natDegree hf
              have hg_deg :
                  Polynomial.degree g =
                    (Polynomial.natDegree g : WithBot ℕ) :=
                Polynomial.degree_eq_natDegree hg
              rw [hf_deg, hg_deg]
              change Polynomial.degree q ≤
                (some (f.natDegree + k * g.natDegree - k) : WithBot ℕ)
              exact hdeg_q'
          simpa [hnum, hden, hq_def] using h_deg_q

lemma hasse_divisibility (F : Type*) [Field F] (f : Polynomial F) (a : F) (ℓ : ℕ)
    (hvan : ∀ k < ℓ, (hasseDerivOp F k f).eval a = 0) :
    (Polynomial.X - Polynomial.C a)^ℓ ∣ f :=
by
  set t : Polynomial F := Polynomial.taylor a f
  have hcoeff0 : ∀ k < ℓ, t.coeff k = 0 := by
    intro k hk
    simpa [t, Polynomial.taylor_coeff, hasseDerivOp] using hvan k hk
  have hfact :
      t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ i) =
        (Polynomial.X - Polynomial.C a) ^ ℓ *
          t.sum (fun i c =>
            Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ (i - ℓ)) := by
    simp [Polynomial.sum_def, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hle : ℓ ≤ i := by
      by_contra h
      have : t.coeff i = 0 := hcoeff0 i (Nat.lt_of_not_ge h)
      exact (Polynomial.mem_support_iff.mp hi) this
    calc
      Polynomial.C (t.coeff i) * (Polynomial.X - Polynomial.C a) ^ i
          = (Polynomial.X - Polynomial.C a) ^ i *
              Polynomial.C (t.coeff i) := by
                simp [mul_comm]
      _ = (Polynomial.X - Polynomial.C a) ^ (ℓ + (i - ℓ)) *
              Polynomial.C (t.coeff i) := by
                simp [Nat.add_sub_of_le hle]
      _ = (Polynomial.X - Polynomial.C a) ^ ℓ *
              (Polynomial.C (t.coeff i) *
                (Polynomial.X - Polynomial.C a) ^ (i - ℓ)) := by
                simp [pow_add, mul_comm, mul_assoc]
  refine ⟨t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ (i - ℓ)), ?_⟩
  have hf :
      f =
        t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ i) := by
    simpa [t] using (Polynomial.sum_taylor_eq (R := F) f a).symm
  exact hf.trans hfact
/- BEGIN PORTED MODULE StepanovAuxiliary -/

lemma auxiliary_derivatives (F : Type*) [Field F]
    (f : Polynomial F) (m d ℓ c : ℕ)
    (hfdeg : f.natDegree = m)
    (rj sj : Polynomial F) (hr : rj.natDegree ≤ d) (hs : sj.natDegree ≤ d)
    (k : ℕ) (hk : k ≤ ℓ) :
  ∃ rjk sjk : Polynomial F,
    hasseDerivOp F k (f^ℓ * rj) = rjk * f^(ℓ - k) ∧
    hasseDerivOp F k (f^(ℓ + c) * sj) = sjk * f^(ℓ + c - k) ∧
    rjk.natDegree ≤ d + k * (m - 1) ∧ sjk.natDegree ≤ d + k * (m - 1) :=
by
  by_cases hf0 : f = 0
  · subst hf0
    have hm0 : m = 0 := by
      simpa [Polynomial.natDegree_zero] using hfdeg.symm
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨rj, sj, ?_, ?_, ?_, ?_⟩
      · simp [hasseDerivOp, mul_comm]
      · simp [hasseDerivOp, mul_comm]
      · simpa [hm0]
      · simpa [hm0]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hℓpos : 0 < ℓ := lt_of_lt_of_le hkpos hk
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
      · have hpow : (0 : Polynomial F) ^ ℓ = 0 := by
          have hne : ℓ ≠ 0 := ne_of_gt hℓpos
          simp [hne]
        simp [hasseDerivOp, hpow]
      · have hℓcpos : 0 < ℓ + c := lt_of_lt_of_le hℓpos (Nat.le_add_right _ _)
        have hpow : (0 : Polynomial F) ^ (ℓ + c) = 0 := by
          have hne : ℓ + c ≠ 0 := ne_of_gt hℓcpos
          simpa [hne] using (zero_pow (M₀ := Polynomial F) (n := ℓ + c) hne)
        simp [hasseDerivOp, hpow]
      · simp [hm0]
      · simp [hm0]
  · have hdeg_f_eq : Polynomial.degree f = (m : WithBot ℕ) := by
      simpa [hfdeg] using Polynomial.degree_eq_natDegree hf0
    obtain ⟨_, hℓ⟩ := hasse_formulas F k ℓ hk
    rcases hℓ rj f with ⟨hdiv_rj_core, hdeg_rj_core⟩
    have hdiv_rj : f ^ (ℓ - k) ∣ hasseDerivOp F k (f ^ ℓ * rj) := by
      simpa [mul_comm] using hdiv_rj_core
    have hkℓc : k ≤ ℓ + c := le_trans hk (Nat.le_add_right _ _)
    obtain ⟨_, hℓc⟩ := hasse_formulas F k (ℓ + c) hkℓc
    rcases hℓc sj f with ⟨hdiv_sj_core, hdeg_sj_core⟩
    have hdiv_sj : f ^ (ℓ + c - k) ∣ hasseDerivOp F k (f ^ (ℓ + c) * sj) := by
      simpa [mul_comm] using hdiv_sj_core
    set rjk : Polynomial F :=
      hasseDerivOp F k (f ^ ℓ * rj) / f ^ (ℓ - k) with hrjk_def
    set sjk : Polynomial F :=
      hasseDerivOp F k (f ^ (ℓ + c) * sj) / f ^ (ℓ + c - k) with hsjk_def
    have hr_eq : hasseDerivOp F k (f ^ ℓ * rj) = rjk * f ^ (ℓ - k) := by
      simpa [hrjk_def, mul_comm] using
        (EuclideanDomain.mul_div_cancel'
          (R := Polynomial F)
          (a := hasseDerivOp F k (f ^ ℓ * rj))
          (b := f ^ (ℓ - k)) (pow_ne_zero _ hf0) hdiv_rj).symm
    have hs_eq : hasseDerivOp F k (f ^ (ℓ + c) * sj) = sjk * f ^ (ℓ + c - k) := by
      simpa [hsjk_def, mul_comm] using
        (EuclideanDomain.mul_div_cancel'
          (R := Polynomial F)
          (a := hasseDerivOp F k (f ^ (ℓ + c) * sj))
          (b := f ^ (ℓ + c - k)) (pow_ne_zero _ hf0) hdiv_sj).symm
    have hdeg_rjk_match :
        Polynomial.degree rjk ≤
          (match
              Polynomial.degree rj + (k : WithBot ℕ) * Polynomial.degree f with
            | ⊥ => ⊥
            | some n => some (n - k)) := by
      rw [hrjk_def, mul_comm (f ^ ℓ) rj]
      exact hdeg_rj_core
    have hdeg_sjk_match :
        Polynomial.degree sjk ≤
          (match
              Polynomial.degree sj + (k : WithBot ℕ) * Polynomial.degree f with
            | ⊥ => ⊥
            | some n => some (n - k)) := by
      rw [hsjk_def, mul_comm (f ^ (ℓ + c)) sj]
      exact hdeg_sj_core
    have hdeg_rj_le_d : Polynomial.degree rj ≤ (d : WithBot ℕ) :=
      (Polynomial.natDegree_le_iff_degree_le).1 hr
    have hdeg_sj_le_d : Polynomial.degree sj ≤ (d : WithBot ℕ) :=
      (Polynomial.natDegree_le_iff_degree_le).1 hs
    let Ftrunc : WithBot ℕ → WithBot ℕ :=
      fun x => match x with | ⊥ => ⊥ | some n => some (n - k)
    have hF_mono :
        ∀ {x y : WithBot ℕ}, x ≤ y → Ftrunc x ≤ Ftrunc y := by
      intro x y hxy
      cases x using WithBot.recBotCoe with
      | bot =>
          cases y using WithBot.recBotCoe with
          | bot => simp [Ftrunc]
          | coe _ => exact bot_le
      | coe a =>
          cases y using WithBot.recBotCoe with
          | bot =>
              have hxbot : ((a : ℕ) : WithBot ℕ) = (⊥ : WithBot ℕ) :=
                (le_bot_iff).1 hxy
              exact (WithBot.natCast_ne_bot (α := ℕ) a) hxbot |> False.elim
          | coe b =>
              have hab : a ≤ b := (WithBot.coe_le_coe).1 hxy
              have hsub : a - k ≤ b - k := Nat.sub_le_sub_right hab k
              exact (WithBot.coe_le_coe).2 hsub
    let x_rj : WithBot ℕ :=
      Polynomial.degree rj + (k : WithBot ℕ) * Polynomial.degree f
    let x_sj : WithBot ℕ :=
      Polynomial.degree sj + (k : WithBot ℕ) * Polynomial.degree f
    let y : WithBot ℕ :=
      (d : WithBot ℕ) + (k : WithBot ℕ) * Polynomial.degree f
    have hx_rj_le_y : x_rj ≤ y := by
      exact add_le_add_left hdeg_rj_le_d ((k : WithBot ℕ) * Polynomial.degree f)
    have hx_sj_le_y : x_sj ≤ y := by
      exact add_le_add_left hdeg_sj_le_d ((k : WithBot ℕ) * Polynomial.degree f)
    have hF_xrj_le_y : Ftrunc x_rj ≤ Ftrunc y := hF_mono hx_rj_le_y
    have hF_xsj_le_y : Ftrunc x_sj ≤ Ftrunc y := hF_mono hx_sj_le_y
    have hF_y_eq :
        Ftrunc y = ((d + k * m - k : ℕ) : WithBot ℕ) := by
      have hy : y = ((d + k * m : ℕ) : WithBot ℕ) := by
        simp [y, hdeg_f_eq, mul_comm]
      rw [hy]
      rfl
    have hdeg_rjk_le :
        Polynomial.degree rjk ≤ ((d + k * m - k : ℕ) : WithBot ℕ) := by
      simpa [hF_y_eq] using
        (le_trans (by simpa [x_rj, Ftrunc] using hdeg_rjk_match) hF_xrj_le_y)
    have hdeg_sjk_le :
        Polynomial.degree sjk ≤ ((d + k * m - k : ℕ) : WithBot ℕ) := by
      simpa [hF_y_eq] using
        (le_trans (by simpa [x_sj, Ftrunc] using hdeg_sjk_match) hF_xsj_le_y)
    have hnat_rjk_le : rjk.natDegree ≤ d + k * m - k :=
      (Polynomial.natDegree_le_iff_degree_le).2 hdeg_rjk_le
    have hnat_sjk_le : sjk.natDegree ≤ d + k * m - k :=
      (Polynomial.natDegree_le_iff_degree_le).2 hdeg_sjk_le
    have h_nat_ineq : d + k * m - k ≤ d + k * (m - 1) := by
      cases m with
      | zero => simp
      | succ m' =>
          have : d + k * Nat.succ m' - k = d + k * m' := by
            simpa [Nat.mul_succ, Nat.add_assoc] using
              (Nat.add_sub_cancel (d + k * m') k)
          simp [this]
    refine ⟨rjk, sjk, hr_eq, hs_eq, ?_, ?_⟩
    · exact le_trans hnat_rjk_le h_nat_ineq
    · exact le_trans hnat_sjk_le h_nat_ineq

lemma hasseDerivOp_mul_Xqpow
  (F : Type*) [Field F] [Fintype F]
  (q k : ℕ) (hq : q = Fintype.card F) (hkq : k < q)
  (P : Polynomial F) (j : ℕ) :
  hasseDerivOp F k (P * (Polynomial.X : Polynomial F)^(j * q)) =
    hasseDerivOp F k P * (Polynomial.X : Polynomial F)^(j * q) :=
by
  have choose_mul_card_pow_cast_eq_zero
      (q j i : ℕ) (hq : q = Fintype.card F)
      (hi_pos : 0 < i) (hi_lt : i < q) :
      (Nat.choose (j * q) i : F) = 0 := by
    have hfrob :
        (1 + (Polynomial.X : Polynomial F)) ^ q =
          (1 : Polynomial F) ^ q +
            (Polynomial.X : Polynomial F) ^ q := by
      simpa [hq, FiniteField.coe_frobeniusAlgHom] using
        (FiniteField.frobeniusAlgHom F (Polynomial F)).map_add
          (1 : Polynomial F) (Polynomial.X : Polynomial F)
    have hpow :
        (1 + (Polynomial.X : Polynomial F)) ^ (j * q) =
          (1 + (Polynomial.X : Polynomial F) ^ q) ^ j := by
      have h1 :
          (1 + (Polynomial.X : Polynomial F)) ^ (j * q) =
            ((1 + (Polynomial.X : Polynomial F)) ^ q) ^ j := by
        simp [pow_mul, mul_comm]
      have h2 :
          ((1 + (Polynomial.X : Polynomial F)) ^ q) ^ j =
            (1 + (Polynomial.X : Polynomial F) ^ q) ^ j := by
        simpa [one_pow] using
          congrArg (fun p : Polynomial F => p ^ j) hfrob
      exact h1.trans h2
    have hcoeff_right_zero :
        ((1 + (Polynomial.X : Polynomial F) ^ q) ^ j).coeff i = 0 := by
      have h' : ∀ n : ℕ,
          ((1 + (Polynomial.X : Polynomial F) ^ q) ^ n).coeff i = 0 := by
        refine Nat.rec ?base ?step
        · have hi_ne_zero : i ≠ 0 := ne_of_gt hi_pos
          simp [pow_zero, Polynomial.coeff_one, hi_ne_zero]
        · intro n hn
          have hmul :
              (((1 + (Polynomial.X : Polynomial F) ^ q) ^ n) *
                  (Polynomial.X : Polynomial F) ^ q).coeff i = 0 := by
            simpa [Nat.not_le.mpr hi_lt] using
              (Polynomial.coeff_mul_X_pow'
                (p := (1 + (Polynomial.X : Polynomial F) ^ q) ^ n)
                (n := q) (d := i))
          have :
              ((1 + (Polynomial.X : Polynomial F) ^ q) ^ (n.succ)).coeff i =
                ((1 + (Polynomial.X : Polynomial F) ^ q) ^ n).coeff i +
                  (((1 + (Polynomial.X : Polynomial F) ^ q) ^ n) *
                      (Polynomial.X : Polynomial F) ^ q).coeff i := by
            simp [pow_succ, mul_add, Polynomial.coeff_add]
          simp [this, hn, hmul]
      exact h' j
    have hcoeff_left_zero :
        ((1 + (Polynomial.X : Polynomial F)) ^ (j * q)).coeff i = 0 := by
      simpa [congrArg (fun p : Polynomial F => p.coeff i) hpow.symm]
        using hcoeff_right_zero
    simpa [Polynomial.coeff_one_add_X_pow (R := F) (n := j * q) (k := i)]
      using hcoeff_left_zero

  have hasseDerivOp_X_pow_mul_card_eq_zero
      (j k : ℕ) (hq : q = Fintype.card F)
      (hk_pos : 0 < k) (hk_lt : k < q) :
      hasseDerivOp F k ((Polynomial.X : Polynomial F) ^ (j * q)) = 0 := by
    have hchoose_zero :
        (Nat.choose (j * q) k : F) = 0 :=
      choose_mul_card_pow_cast_eq_zero q j k hq hk_pos hk_lt
    simp [hasseDerivOp, Polynomial.X_pow_eq_monomial, hchoose_zero]

  cases k with
  | zero =>
      simp [hasseDerivOp, mul_comm]
  | succ k' =>
      have hmul :
          hasseDerivOp F (Nat.succ k')
              (P * (Polynomial.X : Polynomial F) ^ (j * q)) =
            ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
              hasseDerivOp F p.1 P *
                hasseDerivOp F p.2
                  ((Polynomial.X : Polynomial F) ^ (j * q)) := by
        simpa [hasseDerivOp, mul_comm, mul_left_comm, mul_assoc] using
          (Polynomial.hasseDeriv_mul (R := F) (k := Nat.succ k')
            (f := P)
            (g := (Polynomial.X : Polynomial F) ^ (j * q)))
      have hsum :
          ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
              hasseDerivOp F p.1 P *
                hasseDerivOp F p.2
                  ((Polynomial.X : Polynomial F) ^ (j * q)) =
            hasseDerivOp F (Nat.succ k') P *
              (Polynomial.X : Polynomial F) ^ (j * q) := by
        have h' :
            ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
                hasseDerivOp F p.1 P *
                  hasseDerivOp F p.2
                    ((Polynomial.X : Polynomial F) ^ (j * q)) =
              hasseDerivOp F (Nat.succ k') P *
                hasseDerivOp F 0
                  ((Polynomial.X : Polynomial F) ^ (j * q)) := by
          refine
            Finset.sum_eq_single_of_mem
              (a := (Nat.succ k', 0))
              ?ha
              ?hothers
          · exact Finset.mem_antidiagonal.mpr (by simp)
          · intro p hp_mem hp_ne
            rcases p with ⟨a, b⟩
            change (a, b) ∈ _ at hp_mem
            change (a, b) ≠ (Nat.succ k', 0) at hp_ne
            have hsum_ab : a + b = Nat.succ k' :=
              Finset.mem_antidiagonal.mp hp_mem
            have hb_ne_zero : b ≠ 0 := by
              intro hb0
              have : a = Nat.succ k' := by
                simpa [hb0] using hsum_ab
              apply hp_ne
              ext <;> simp [this, hb0]
            have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne_zero
            have hb_le : b ≤ Nat.succ k' := by
              have : b ≤ a + b := Nat.le_add_left _ _
              simpa [hsum_ab] using this
            have hb_ltq : b < q := lt_of_le_of_lt hb_le hkq
            have hderiv_zero :
                hasseDerivOp F b
                    ((Polynomial.X : Polynomial F) ^ (j * q)) = 0 :=
              hasseDerivOp_X_pow_mul_card_eq_zero j b hq hb_pos hb_ltq
            simp [hderiv_zero]
        simpa [hasseDerivOp] using h'
      simpa using (hmul.trans hsum)

lemma stepanov_form (F : Type*) [Field F] [Fintype F]
    (f : Polynomial F) (ℓ q c J k : ℕ) (hk : k < ℓ)
    (hq : q = Fintype.card F) (hkq : k < q)
    (rj sj : ℕ → Polynomial F) :
  ∃ rjk sjk : ℕ → Polynomial F,
    (∀ j, hasseDerivOp F k (f^ℓ * (rj j)) = (rjk j) * f^(ℓ - k)) ∧
    (∀ j, hasseDerivOp F k (f^(ℓ + c) * (sj j)) = (sjk j) * f^(ℓ + c - k)) ∧
    hasseDerivOp F k
      (f^ℓ *
        (Finset.sum (Finset.range J)
          (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q)))) =
      f^(ℓ - k) *
        Finset.sum (Finset.range J)
          (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) :=
by
  have h_ex :
      ∀ j : ℕ, ∃ rjk_j sjk_j : Polynomial F,
        hasseDerivOp F k (f^ℓ * (rj j)) = rjk_j * f^(ℓ - k) ∧
        hasseDerivOp F k (f^(ℓ + c) * (sj j)) = sjk_j * f^(ℓ + c - k) := by
    intro j
    let d := Nat.max (rj j).natDegree (sj j).natDegree
    have hr : (rj j).natDegree ≤ d := Nat.le_max_left _ _
    have hs : (sj j).natDegree ≤ d := Nat.le_max_right _ _
    obtain ⟨rjk_j, sjk_j, hr_eq, hs_eq, -, -⟩ :=
      auxiliary_derivatives (F := F) f f.natDegree d ℓ c rfl (rj j) (sj j) hr hs k hk.le
    exact ⟨rjk_j, sjk_j, hr_eq, hs_eq⟩
  choose rjk sjk hrjk hsjk using h_ex
  refine ⟨rjk, sjk, hrjk, hsjk, ?_⟩
  have h_rewrite :
      f^ℓ *
        Finset.sum (Finset.range J)
          (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q)) =
      Finset.sum (Finset.range J)
        (fun j => (f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) := by
    have h :=
      (Finset.mul_sum
        (s := Finset.range J)
        (f := fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))
        (a := f^ℓ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h_deriv_sum :
      hasseDerivOp F k
        (f^ℓ *
          Finset.sum (Finset.range J)
            (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) =
      Finset.sum (Finset.range J)
        (fun j =>
          hasseDerivOp F k
            ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q))) := by
    simp [hasseDerivOp, h_rewrite, _root_.map_sum]
  have h_term :
      ∀ j : ℕ,
        hasseDerivOp F k
          ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) =
        f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q) := by
    intro j
    have h_split :
        f^ℓ * ((rj j) + (sj j) * f^c) =
          f^ℓ * (rj j) + f^(ℓ + c) * (sj j) := by
      simp [mul_add, pow_add, mul_comm, mul_left_comm]
    have hP_factor :
        hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) := by
      have h_add' :
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            hasseDerivOp F k (f^ℓ * (rj j)) +
              hasseDerivOp F k (f^(ℓ + c) * (sj j)) := by
        simp [hasseDerivOp, h_split]
      have h_basic :
          hasseDerivOp F k (f^ℓ * (rj j)) +
              hasseDerivOp F k (f^(ℓ + c) * (sj j)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) := by
        simp [hrjk j, hsjk j]
      have h_tmp :
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) :=
        h_add'.trans h_basic
      have h_exp : ℓ + c - k = c + (ℓ - k) := by
        have hℓ : ℓ = (ℓ - k) + k := (Nat.sub_add_cancel hk.le).symm
        have h_step : ℓ + c - k = ((ℓ - k) + k) + c - k := by
          have := congrArg (fun n => n + c - k) hℓ
          simpa using this
        have h' : ((ℓ - k) + k) + c - k = (ℓ - k) + c := by
          have htemp : ((ℓ - k) + k) + c = ((ℓ - k) + c) + k := by
            calc
              ((ℓ - k) + k) + c
                  = (ℓ - k) + (k + c) := by
                        simp [Nat.add_assoc]
              _ = (ℓ - k) + (c + k) := by
                        simp [Nat.add_comm]
              _ = ((ℓ - k) + c) + k := by
                        simp [Nat.add_assoc]
          calc
            ((ℓ - k) + k) + c - k
                = ((ℓ - k) + c) + k - k := by
                      simp [htemp]
            _ = (ℓ - k) + c := by
                      simp
        have h1 : ℓ + c - k = (ℓ - k) + c := h_step.trans h'
        have h2 : (ℓ - k) + c = c + (ℓ - k) := Nat.add_comm _ _
        exact h1.trans h2
      have hpow : f^(ℓ + c - k) = f^c * f^(ℓ - k) := by
        have hpow' := congrArg (fun n => f^n) h_exp
        simpa [pow_add] using hpow'
      calc
        hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) := h_tmp
        _ = (rjk j) * f^(ℓ - k) + (sjk j) * (f^c * f^(ℓ - k)) := by
              exact congrArg
                (fun t => (rjk j) * f^(ℓ - k) + (sjk j) * t) hpow
        _ = rjk j * f^(ℓ - k) + sjk j * f^c * f^(ℓ - k) := by
              simp [mul_assoc]
        _ = (rjk j + sjk j * f^c) * f^(ℓ - k) := by
              simp [add_mul, mul_assoc]
        _ = f^(ℓ - k) * (rjk j + sjk j * f^c) := by
              ac_rfl
    have h_prod :=
      hasseDerivOp_mul_Xqpow (F := F) (q := q) (k := k)
        (hq := hq) (hkq := hkq)
        (P := f^ℓ * ((rj j) + (sj j) * f^c)) (j := j)
    calc
      hasseDerivOp F k
          ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) =
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) *
            (Polynomial.X)^(j*q) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h_prod
      _ = f^(ℓ - k) * (rjk j + sjk j * f^c) * (Polynomial.X)^(j*q) := by
            simp [hP_factor]
      _ = f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q) := by
            ac_rfl
  have h_deriv_explicit :
      hasseDerivOp F k
        (f^ℓ *
          Finset.sum (Finset.range J)
            (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) =
      Finset.sum (Finset.range J)
        (fun j =>
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
    simpa [h_term] using h_deriv_sum
  have h_factor :
      Finset.sum (Finset.range J)
        (fun j =>
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
      f^(ℓ - k) *
        Finset.sum (Finset.range J)
          (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
    have h1 :
        Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
        Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * (((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [mul_assoc]
    have h_mul_sum :=
      (Finset.mul_sum
        (s := Finset.range J)
        (f :=
          fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))
        (a := f^(ℓ - k)))
    calc
      Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
          Finset.sum (Finset.range J)
            (fun j =>
              f^(ℓ - k) * (((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))) := h1
      _ = f^(ℓ - k) *
            Finset.sum (Finset.range J)
              (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
            simpa using h_mul_sum.symm
  exact h_deriv_explicit.trans h_factor
/- BEGIN PORTED MODULE StepanovNonSquare -/

lemma stepanov_square_from_eq (F : Type*) [Field F]
    (f : Polynomial F) (r s : Polynomial F) (f₀ : F)
    (hf₀_ne_zero : f₀ ≠ 0) (hs_ne_zero : s ≠ 0)
    (heq : r * r * f = s * s * Polynomial.C f₀) :
    ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f :=
by
  let K := AlgebraicClosure F
  let fK := Polynomial.map (algebraMap F K) f
  let rK := Polynomial.map (algebraMap F K) r
  let sK := Polynomial.map (algebraMap F K) s
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_eq_mul_self (k := K) (algebraMap F K f₀)
  let L := FractionRing (Polynomial K)
  have heqK :
      rK * rK * fK = sK * sK * Polynomial.C (algebraMap F K f₀) := by
    simpa [fK, rK, sK, Polynomial.map_mul, Polynomial.map_C] using
      congrArg (Polynomial.map (algebraMap F K)) heq
  have hrK_ne : rK ≠ 0 := by
    intro hr0
    have h0 : sK * sK * Polynomial.C (algebraMap F K f₀) = 0 := by
      calc
        sK * sK * Polynomial.C (algebraMap F K f₀)
            = rK * rK * fK := heqK.symm
        _ = 0 := by simp [hr0]
    have hsK_ne : sK ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap F K).injective).2 hs_ne_zero
    have hCf0_ne : Polynomial.C (algebraMap F K f₀) ≠ 0 := by
      simp [hf₀_ne_zero]
    exact (mul_ne_zero (mul_ne_zero hsK_ne hsK_ne) hCf0_ne) h0
  let g : L :=
    algebraMap (Polynomial K) L sK / algebraMap (Polynomial K) L rK *
      algebraMap (Polynomial K) L (Polynomial.C α)
  have hrK_ne_alg : algebraMap (Polynomial K) L rK ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff (R := Polynomial K) (K := L)
          (x := rK)).not.mpr hrK_ne
  have hCα_sq : Polynomial.C α * Polynomial.C α =
      Polynomial.C (algebraMap F K f₀) := by
    rw [← Polynomial.C_mul, ← hα]
  have hg_sq : g * g = algebraMap (Polynomial K) L fK := by
    simp only [g]
    calc
      algebraMap (Polynomial K) L sK / algebraMap (Polynomial K) L rK *
              algebraMap (Polynomial K) L (Polynomial.C α) *
            (algebraMap (Polynomial K) L sK / algebraMap (Polynomial K) L rK *
              algebraMap (Polynomial K) L (Polynomial.C α))
          =
            (algebraMap (Polynomial K) L sK *
                  algebraMap (Polynomial K) L (Polynomial.C α) /
                algebraMap (Polynomial K) L rK) *
              (algebraMap (Polynomial K) L sK *
                  algebraMap (Polynomial K) L (Polynomial.C α) /
                algebraMap (Polynomial K) L rK) := by
              ring
      _ =
            (algebraMap (Polynomial K) L sK *
                algebraMap (Polynomial K) L (Polynomial.C α)) *
              (algebraMap (Polynomial K) L sK *
                algebraMap (Polynomial K) L (Polynomial.C α)) /
              (algebraMap (Polynomial K) L rK *
                algebraMap (Polynomial K) L rK) := by
              rw [div_mul_div_comm]
      _ =
            algebraMap (Polynomial K) L
                (sK * Polynomial.C α * (sK * Polynomial.C α)) /
              algebraMap (Polynomial K) L (rK * rK) := by
              simp only [← map_mul]
      _ =
            algebraMap (Polynomial K) L (rK * rK * fK) /
              algebraMap (Polynomial K) L (rK * rK) := by
              congr 2
              calc
                sK * Polynomial.C α * (sK * Polynomial.C α)
                    = sK * sK * (Polynomial.C α * Polynomial.C α) := by
                      ring
                _ = rK * rK * fK := by
                      rw [hCα_sq, heqK.symm]
      _ = algebraMap (Polynomial K) L fK := by
              rw [map_mul, mul_comm, mul_div_assoc,
                div_self (by
                  rw [map_mul]
                  exact mul_ne_zero hrK_ne_alg hrK_ne_alg),
                mul_one]
  obtain ⟨h, hh⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral <|
      IsIntegral.of_pow (by norm_num)
        ((sq g ▸ hg_sq) ▸ isIntegral_algebraMap)
  refine ⟨h, ?_⟩
  refine IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K)) ?_
  rw [map_mul, hh, hg_sq]

lemma stepanov_nonzero_shift_preserves (F : Type*) [Field F] (f : Polynomial F)
    (a : AlgebraicClosure F)
    (hnsq : ¬∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f) :
    ¬∃ g : Polynomial (AlgebraicClosure F),
      g * g =
        (Polynomial.map (algebraMap F (AlgebraicClosure F)) f).comp
          (Polynomial.X + Polynomial.C a) :=
by
  rintro ⟨g, hg_sq⟩
  refine hnsq ⟨g.comp (Polynomial.X - Polynomial.C a), ?_⟩
  have h := congrArg (fun p => p.comp (Polynomial.X - Polynomial.C a)) hg_sq
  simpa [Polynomial.mul_comp, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X] using h

lemma coefficient_transformation_shift (F : Type*) [Field F]
    (a : F) (q J : ℕ) (A : ℕ → Polynomial F) :
    ∑ j ∈ Finset.range J, A j * (Polynomial.X ^ q + Polynomial.C a) ^ j =
      ∑ k ∈ Finset.range J,
        (∑ j ∈ Finset.Ico k J,
            (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) *
          Polynomial.X ^ (k * q) :=
by
  let B : ℕ → ℕ → Polynomial F :=
    fun j k =>
      ((Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) *
        Polynomial.X ^ (k * q)
  have hL :
      ∑ j ∈ Finset.range J, A j * (Polynomial.X ^ q + Polynomial.C a) ^ j =
        ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (j + 1), B j k := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [B, add_pow, Polynomial.smul_eq_C_mul, Finset.mul_sum,
      mul_comm, mul_left_comm, pow_mul]
  have hL2 :
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (j + 1), B j k =
        ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
          (if k ≤ j then B j k else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj_lt : j < J := Finset.mem_range.mp hj
    have h_range :
        Finset.range (j + 1) =
          (Finset.range J).filter (fun k => k ≤ j) := by
      apply Finset.ext
      intro k; constructor
      · intro hk
        have hk_lt : k < j + 1 := Finset.mem_range.mp hk
        have hk_le_j : k ≤ j := Nat.lt_succ_iff.mp hk_lt
        have hk_lt_J : k < J := lt_of_le_of_lt hk_le_j hj_lt
        exact
          (Finset.mem_filter).mpr
            ⟨Finset.mem_range.mpr hk_lt_J, hk_le_j⟩
      · intro hk
        rcases Finset.mem_filter.mp hk with ⟨_, hk_le_j⟩
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le_j)
    calc
      ∑ k ∈ Finset.range (j + 1), B j k
          = ∑ k ∈ (Finset.range J).filter (fun k => k ≤ j), B j k := by
              simp [h_range]
      _ = ∑ k ∈ Finset.range J,
              (if k ≤ j then B j k else 0) := by
            simp [Finset.sum_filter]
  have h_swap :
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
          (if k ≤ j then B j k else 0) =
        ∑ k ∈ Finset.range J, ∑ j ∈ Finset.range J,
          (if k ≤ j then B j k else 0) := by
    let s := Finset.range J
    let t := Finset.range J
    have h1 :=
      (Finset.sum_product' (s := s) (t := t)
        (f := fun j k => (if k ≤ j then B j k else 0)))
    have h2 :=
      (Finset.sum_product_right' (s := s) (t := t)
        (f := fun j k => (if k ≤ j then B j k else 0)))
    calc
      ∑ j ∈ s, ∑ k ∈ t, (if k ≤ j then B j k else 0)
          = (Finset.instSProd.sprod s t).sum
              (fun x => if x.2 ≤ x.1 then B x.1 x.2 else 0) := by
            simpa [s, t] using h1.symm
      _ = ∑ k ∈ t, ∑ j ∈ s, (if k ≤ j then B j k else 0) := by
            simpa [s, t] using h2
  have h_inner2 :
      ∀ k : ℕ,
        ∑ j ∈ Finset.range J, (if k ≤ j then B j k else 0) =
          ∑ j ∈ Finset.Ico k J, B j k := by
    intro k
    have hfilter :
        ∑ j ∈ Finset.range J, (if k ≤ j then B j k else 0) =
          ∑ j ∈ (Finset.range J).filter (fun j => k ≤ j), B j k := by
      simp [Finset.sum_filter]
    have h_Ico :
        (Finset.range J).filter (fun j => k ≤ j) = Finset.Ico k J := by
      ext j
      simp [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range, and_comm]
    calc
      ∑ j ∈ Finset.range J, (if k ≤ j then B j k else 0)
          = ∑ j ∈ (Finset.range J).filter (fun j => k ≤ j), B j k := hfilter
      _ = ∑ j ∈ Finset.Ico k J, B j k := by
            simp [h_Ico]
  have h_factor :
      ∀ k : ℕ,
        ∑ j ∈ Finset.Ico k J, B j k =
          (∑ j ∈ Finset.Ico k J,
              (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) *
            Polynomial.X ^ (k * q) := by
    intro k
    calc
      ∑ j ∈ Finset.Ico k J, B j k
          = ∑ j ∈ Finset.Ico k J,
              ((Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) *
                Polynomial.X ^ (k * q) := by
            simp [B]
      _ =
          (∑ j ∈ Finset.Ico k J,
              (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) *
            Polynomial.X ^ (k * q) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (Finset.sum_mul
                (s := Finset.Ico k J)
                (f :=
                  fun j =>
                    (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j)
                (a := Polynomial.X ^ (k * q))).symm
  calc
    ∑ j ∈ Finset.range J, A j * (Polynomial.X ^ q + Polynomial.C a) ^ j
        = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (j + 1), B j k := hL
    _ = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
            (if k ≤ j then B j k else 0) := hL2
    _ = ∑ k ∈ Finset.range J, ∑ j ∈ Finset.range J,
            (if k ≤ j then B j k else 0) := h_swap
    _ = ∑ k ∈ Finset.range J, ∑ j ∈ Finset.Ico k J, B j k := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact h_inner2 k
    _ = ∑ k ∈ Finset.range J,
            (∑ j ∈ Finset.Ico k J,
                (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) *
              Polynomial.X ^ (k * q) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [h_factor k]

lemma triangular_inversion_shift (F : Type*) [Field F]
    (a : F) (J : ℕ) (A : ℕ → Polynomial F)
    (hR : ∀ k < J,
      ∑ j ∈ Finset.Ico k J,
        (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j = 0) :
    ∀ j < J, A j = 0 :=
by
  revert A hR
  induction J with
  | zero =>
      intro A hR j hj
      exact (Nat.not_lt_zero _ hj).elim
  | succ J IH =>
      intro A hR j hj
      have hA_J : A J = 0 := by
        simpa [Nat.Ico_succ_singleton] using hR J (Nat.lt_succ_self J)
      have hR' :
          ∀ k < J,
            ∑ j ∈ Finset.Ico k J,
              (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j = 0 := by
        intro k hk
        have hIco : Finset.Ico k J.succ = insert J (Finset.Ico k J) := by
          simpa using
            (Finset.insert_Ico_right_eq_Ico_succ (a := k) (b := J)
              (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hk))).symm
        simpa [hIco, Finset.sum_insert, Finset.mem_Ico, hA_J] using
          hR k (Nat.lt_succ_of_lt hk)
      by_cases h_eq : j = J
      · simpa [h_eq] using hA_J
      · exact IH A hR' j (lt_of_le_of_ne (Nat.le_of_lt_succ hj) h_eq)

lemma stepanov_nonzero_minimal_congruence
    (F : Type*) [Field F]
    (f : Polynomial F) (ℓ c q J : ℕ)
    (rj sj : ℕ → Polynomial F)
    (hf : f ≠ 0)
    (hsum : f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) *
          (Polynomial.X) ^ (j * q))) = 0)
    (k : ℕ) (hk : k < J)
    (hk_min : ∀ j < k, rj j = 0 ∧ sj j = 0) :
    Polynomial.X ^ q ∣ (rj k + sj k * f ^ c) :=
by
  have hsum_zero :
      ∑ j ∈ Finset.range J,
        (rj j + sj j * f ^ c) * Polynomial.X ^ (j * q) = 0 := by
    simpa using
      (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero _ hf)
  rw [
    Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (Nat.le_of_lt hk),
    Finset.sum_eq_zero (by
      intro j hj
      obtain ⟨hrj, hsj⟩ := hk_min j (Finset.mem_Ico.mp hj).2
      simp [hrj, hsj]),
    zero_add,
    ← Finset.insert_Ico_succ_left_eq_Ico hk,
    Finset.sum_insert (by simp [Finset.mem_Ico])
  ] at hsum_zero
  have h_dvd_term :
      Polynomial.X ^ ((k + 1) * q) ∣
        (rj k + sj k * f ^ c) * Polynomial.X ^ (k * q) := by
    rw [add_eq_zero_iff_eq_neg.mp hsum_zero]
    refine dvd_neg.mpr ?_
    refine Finset.dvd_sum ?_
    intro x hx
    exact dvd_mul_of_dvd_right
      (pow_dvd_pow Polynomial.X
        (Nat.mul_le_mul_right q (Finset.mem_Ico.mp hx).1)) _
  refine
    (mul_dvd_mul_iff_left (a := Polynomial.X ^ (k * q))
        (pow_ne_zero _ Polynomial.X_ne_zero)).mp ?_
  have hkq : (k + 1) * q = k * q + q := by ring
  simpa [pow_add, hkq, mul_comm, mul_left_comm, mul_assoc] using h_dvd_term

lemma stepanov_nonzero_frobenius_mod (F : Type*) [Field F] [Fintype F]
    (f : Polynomial F) (q : ℕ) (hq : q = Fintype.card F) :
    Polynomial.X ^ q ∣ (f ^ q - Polynomial.C (f.eval 0)) :=
by
  rw [show f ^ q = Polynomial.expand F q f from
        by simpa [hq] using (FiniteField.expand_card f).symm,
      Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub,
      Polynomial.coeff_expand
        (by simpa [hq] using (Fintype.card_pos (α := F)))]
  by_cases hd0 : d = 0
  · subst hd0
    simp [Polynomial.eval, Polynomial.eval₂_at_zero]
  · simp [Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hd0) hd,
      hd0, Polynomial.coeff_C]

lemma stepanov_nonzero_polynomial_equality
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f r s : Polynomial F) (q m c : ℕ)
  (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
  (hc : c = (q - 1) / 2)
  (hrdeg : 2 * r.natDegree + m < q) (hsdeg : 2 * s.natDegree + m < q)
  (hcong : Polynomial.X ^ q ∣ (r + s * f ^ c)) :
  r * r * f = s * s * Polynomial.C (f.eval 0) :=
by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := by
    refine (Nat.odd_iff.mpr ?_)
    simpa [hq] using
      (FiniteField.odd_card_of_char_ne_two (F := F) hF)
  have h2c1 : 2 * c + 1 = q := by
    have hq_pos : 0 < q := by
      simpa [hq] using (Fintype.card_pos (α := F))
    have h2_dvd : 2 ∣ q - 1 := by
      refine ⟨k, ?_⟩
      have := congrArg (fun n => n - 1) hk
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have h2c : 2 * c = q - 1 := by
      simpa [hc, Nat.mul_comm] using
        (Nat.div_two_mul_two_of_even ((even_iff_two_dvd).2 h2_dvd))
    simpa [h2c, Nat.add_comm] using
      (Nat.sub_add_cancel (Nat.succ_le_of_lt hq_pos))
  have hdiv1 : Polynomial.X ^ q ∣ r * r - (s * f ^ c) * (s * f ^ c) := by
    have htmp : Polynomial.X ^ q ∣ (r + s * f ^ c) * (r - s * f ^ c) :=
      dvd_mul_of_dvd_left hcong (r - s * f ^ c)
    have hdsq :
        (r + s * f ^ c) * (r - s * f ^ c) =
          r * r - (s * f ^ c) * (s * f ^ c) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using
        (mul_self_sub_mul_self (a := r) (b := s * f ^ c)).symm
    simpa [hdsq] using htmp
  have hdiv2 : Polynomial.X ^ q ∣ r * r * f - s * s * f ^ (2 * c + 1) := by
    have htmp : Polynomial.X ^ q ∣ f * (r * r - (s * f ^ c) * (s * f ^ c)) :=
      dvd_mul_of_dvd_right hdiv1 f
    have hpow : f ^ c * f ^ c * f = f ^ (2 * c + 1) := by
      have : f ^ c * f ^ c * f = f ^ (c + c + 1) := by
        simp [pow_add, pow_succ, mul_comm]
      simpa [two_mul, Nat.add_assoc] using this
    have hrewrite :
        f * (r * r - (s * f ^ c) * (s * f ^ c)) =
          r * r * f - s * s * f ^ (2 * c + 1) := by
      calc
        f * (r * r - (s * f ^ c) * (s * f ^ c))
            = f * (r * r) - f * ((s * f ^ c) * (s * f ^ c)) := by
                simp [mul_sub]
        _ = r * r * f - s * s * (f ^ c * f ^ c) * f := by
                simp [mul_comm, mul_left_comm, mul_assoc]
        _ = r * r * f - s * s * (f ^ c * f ^ c * f) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
        _ = r * r * f - s * s * f ^ (2 * c + 1) := by
                simp [hpow, mul_comm, mul_assoc]
    simpa [hrewrite] using htmp
  have hdiv3 : Polynomial.X ^ q ∣
      s * s * f ^ q - s * s * Polynomial.C (f.eval 0) := by
    simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc] using
      (dvd_mul_of_dvd_right
        (stepanov_nonzero_frobenius_mod (F := F) (f := f) (q := q) hq) (s * s))
  have hdiv_final : Polynomial.X ^ q ∣
      r * r * f - s * s * Polynomial.C (f.eval 0) := by
    have hdiv2' : Polynomial.X ^ q ∣ r * r * f - s * s * f ^ q := by
      simpa [h2c1] using hdiv2
    have h := dvd_add hdiv2' hdiv3
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hdeg_r2f_lt : (r * r * f).natDegree < q := by
    refine lt_of_le_of_lt ?_ hrdeg
    refine
      (Polynomial.natDegree_mul_le (p := r * r) (q := f)).trans ?_
    have h2 : (r * r).natDegree ≤ 2 * r.natDegree := by
      simpa [two_mul] using (Polynomial.natDegree_mul_le (p := r) (q := r))
    simpa [hfdeg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_le_add_right h2 m
  have hdeg_s2C_lt :
      (s * s * Polynomial.C (f.eval 0)).natDegree < q := by
    have h2s_lt_q : 2 * s.natDegree < q := by
      have :=
        lt_of_le_of_lt
          (Nat.add_le_add_left (Nat.zero_le m) (2 * s.natDegree)) hsdeg
      simpa using this
    refine lt_of_le_of_lt ?_ h2s_lt_q
    refine
      (Polynomial.natDegree_mul_le (p := s * s)
        (q := Polynomial.C (f.eval 0))).trans ?_
    have h2 : (s * s).natDegree ≤ 2 * s.natDegree := by
      simpa [two_mul] using (Polynomial.natDegree_mul_le (p := s) (q := s))
    have hC : (Polynomial.C (f.eval 0 : F)).natDegree = 0 := by simp
    simpa [hC, Nat.add_comm] using h2
  have hdeg_diff_lt :
      (r * r * f - s * s * Polynomial.C (f.eval 0)).natDegree < q := by
    have hdeg_diff_le :
        (r * r * f - s * s * Polynomial.C (f.eval 0)).natDegree ≤
          max (r * r * f).natDegree
            (s * s * Polynomial.C (f.eval 0)).natDegree := by
      simpa [sub_eq_add_neg] using
        (Polynomial.natDegree_add_le (p := r * r * f)
          (q := -(s * s * Polynomial.C (f.eval 0))))
    exact
      lt_of_le_of_lt hdeg_diff_le
        (max_lt_iff.mpr ⟨hdeg_r2f_lt, hdeg_s2C_lt⟩)
  have hdiff_zero : r * r * f - s * s * Polynomial.C (f.eval 0) = 0 := by
    by_contra hne
    have hdeg_ge :
        q ≤ (r * r * f - s * s * Polynomial.C (f.eval 0)).natDegree := by
      have h :=
        Polynomial.natDegree_le_of_dvd (p := (Polynomial.X ^ q : Polynomial F))
          (q := r * r * f - s * s * Polynomial.C (f.eval 0)) hdiv_final hne
      simpa using h
    exact (not_lt_of_ge hdeg_ge hdeg_diff_lt)
  exact sub_eq_zero.mp hdiff_zero

lemma degree_bound_implies_two_mul_add_lt (q m n : ℕ) (hqm : m < q)
    (hn : n ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) : 2 * n + m < q :=
by
  have hx_pos : (0 : ℚ) < ((q : ℚ) - m) / 2 :=
    div_pos (sub_pos.mpr (by exact_mod_cast hqm)) (by norm_num)
  have hn_lt : (n : ℚ) < ((q : ℚ) - m) / 2 :=
    Nat.lt_ceil.mp <| Nat.lt_of_le_pred (Nat.ceil_pos.mpr hx_pos) hn
  exact_mod_cast
    (show (2 : ℚ) * n + m < (q : ℚ) from by nlinarith [hn_lt])

lemma stepanov_nonzero_eval_zero (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q m ℓ J c : ℕ) (hc : c = (q - 1) / 2)
    (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
    (hm_pos : 0 < m)
    (hq6m : q > 6 * m)
    (hf0 : f.eval 0 ≠ 0)
    (rj sj : ℕ → Polynomial F)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hdeg : ∀ j < J,
      (rj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
      (sj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) :
  (f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * (Polynomial.X) ^ (j * q)))) = 0 ↔
    (∀ j < J, rj j = 0 ∧ sj j = 0) :=
by
  classical
  constructor
  · intro hsum
    by_contra h
    push_neg at h
    obtain ⟨j₀, hj₀_lt, hj₀_ne⟩ := h
    have hj₀_or : rj j₀ ≠ 0 ∨ sj j₀ ≠ 0 := by
      by_cases hrj : rj j₀ = 0
      · right; exact hj₀_ne hrj
      · left; exact hrj
    have hP_exists : ∃ k, k < J ∧ (rj k ≠ 0 ∨ sj k ≠ 0) :=
      ⟨j₀, hj₀_lt, hj₀_or⟩
    let k := Nat.find hP_exists
    obtain ⟨hk, hk_nonzero⟩ := Nat.find_spec hP_exists
    have hk_min : ∀ j < k, rj j = 0 ∧ sj j = 0 := fun j hj => by
      have h' : j < J → rj j = 0 ∧ sj j = 0 := by
        simpa [not_and, not_or, not_not] using
          (Nat.find_min hP_exists hj :
            ¬ (j < J ∧ (rj j ≠ 0 ∨ sj j ≠ 0)))
      exact h' (Nat.lt_trans hj hk)
    have heq :=
      stepanov_nonzero_polynomial_equality F hF f (rj k) (sj k) q m c hq hfdeg hc
        (degree_bound_implies_two_mul_add_lt q m (rj k).natDegree (by linarith)
          (hdeg k hk).1)
        (degree_bound_implies_two_mul_add_lt q m (sj k).natDegree (by linarith)
          (hdeg k hk).2)
        (stepanov_nonzero_minimal_congruence F f ℓ c q J rj sj
          (by intro hf; simp [hf] at hf0) hsum k hk hk_min)
    by_cases hsk : sj k = 0
    · have heq' : rj k * rj k * f = 0 := by simpa [hsk] using heq
      have hr_eq_zero : rj k = 0 := by
        rcases mul_eq_zero.mp heq' with hr2 | hf
        · exact mul_self_eq_zero.mp hr2
        · exact (False.elim <| by simp [hf] at hf0)
      exact hk_nonzero.elim (fun hr => hr hr_eq_zero) (fun hs => hs hsk)
    · exact
        hnsq
          (stepanov_square_from_eq F f (rj k) (sj k) (f.eval 0)
            hf0 hsk heq)
  · intro hall
    have hsum_zero : Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        obtain ⟨hrj, hsj⟩ := hall j (Finset.mem_range.mp hj)
        simp [hrj, hsj]
    simp [hsum_zero]

lemma coefficient_transformation_degree_bound
    (F : Type*) [Field F]
    (a : F) (J d : ℕ) (A : ℕ → Polynomial F)
    (hdeg : ∀ j < J, (A j).natDegree ≤ d) :
    ∀ k < J,
      (∑ j ∈ Finset.Ico k J,
         (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j).natDegree ≤ d :=
by
  intro k _
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.Ico k J)
    (f := fun j =>
      (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j)
    (n := d) ?_
  intro j hj
  refine
    ((Polynomial.natDegree_mul_le
          (p := (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k))
          (q := A j)).trans ?_).trans
      (hdeg j (Finset.mem_Ico.1 hj).2)
  have hconst :
      ((Nat.choose j k : F) • (Polynomial.C a) ^ (j - k)).natDegree ≤ 0 :=
    (Polynomial.natDegree_smul_le
        (a := (Nat.choose j k : F))
        (p := (Polynomial.C a) ^ (j - k))).trans
      ((Polynomial.natDegree_pow_le (p := Polynomial.C a) (n := j - k)).trans
        (by simp))
  simpa [Nat.zero_add]
    using Nat.add_le_add_right hconst (A j).natDegree

lemma stepanov_nonzero (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q m ℓ J c : ℕ) (hc : c = (q - 1) / 2)
    (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
    (hm_pos : 0 < m)
    (hq6m : q > 6 * m)
    (rj sj : ℕ → Polynomial F)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hdeg : ∀ j < J, (rj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
                     (sj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) :
  (f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * (Polynomial.X) ^ (j * q)))) = 0 ↔
    (∀ j < J, rj j = 0 ∧ sj j = 0) :=
by
  constructor
  · intro hsum
    by_cases hf0 : f.eval 0 ≠ 0
    · exact
        (stepanov_nonzero_eval_zero (F := F) (hF := hF)
          (f := f) (q := q) (m := m) (ℓ := ℓ) (J := J) (c := c)
          (hc := hc) (hq := hq) (hfdeg := hfdeg) (hm_pos := hm_pos)
          (hq6m := hq6m) (hf0 := hf0)
          (rj := rj) (sj := sj) (hnsq := hnsq) (hdeg := hdeg)).mp hsum
    · have hqm : q > m :=
        lt_of_le_of_lt
          (by
            have h := Nat.mul_le_mul_right m (by decide : (1 : ℕ) ≤ 6)
            simpa using h)
          hq6m
      obtain ⟨a, hfa_ne⟩ :=
        Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f
          (by
            intro hf
            simp [hf] at hfdeg
            omega)
          (by
            rw [Cardinal.mk_fintype, hfdeg, ← hq]
            exact_mod_cast hqm)
      let shift : Polynomial F := Polynomial.X + Polynomial.C a
      let g : Polynomial F := f.comp shift
      let rj' : ℕ → Polynomial F := fun j => (rj j).comp shift
      let sj' : ℕ → Polynomial F := fun j => (sj j).comp shift
      have hg0_ne : g.eval 0 ≠ 0 := by
        simpa [g, shift] using hfa_ne
      have hgdeg : g.natDegree = m := by
        simp [g, shift, hfdeg, Polynomial.natDegree_comp]
      have hmap_g :
          Polynomial.map (algebraMap F (AlgebraicClosure F)) g =
            (Polynomial.map (algebraMap F (AlgebraicClosure F)) f).comp
              (Polynomial.X +
                Polynomial.C (algebraMap F (AlgebraicClosure F) a)) := by
        unfold g shift
        have h :=
          Polynomial.map_comp (algebraMap F (AlgebraicClosure F)) f
            (Polynomial.X + Polynomial.C a)
        have hshift :
            Polynomial.map (algebraMap F (AlgebraicClosure F))
                (Polynomial.X + Polynomial.C a : Polynomial F) =
              (Polynomial.X +
                Polynomial.C (algebraMap F (AlgebraicClosure F) a)
                  : Polynomial (AlgebraicClosure F)) := by
          simp [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
        simpa [hshift] using h
      have hnsq_g :
          ¬ ∃ h : Polynomial (AlgebraicClosure F),
              h * h =
                Polynomial.map (algebraMap F (AlgebraicClosure F)) g := by
        have hnsq_shifted :=
          stepanov_nonzero_shift_preserves (F := F) (f := f)
            (a := algebraMap F (AlgebraicClosure F) a) hnsq
        simpa [hmap_g] using hnsq_shifted
      have hdeg_shifted :
          ∀ j < J,
            (rj' j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
            (sj' j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 := by
        intro j hj
        simpa [rj', sj', shift, Polynomial.natDegree_comp] using hdeg j hj
      have hg1 :
          g ^ ℓ *
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj' j) + (sj' j) * g ^ c) * shift ^ (j * q)) = 0 := by
        simpa [shift, g, rj', sj'] using
          congrArg (fun p : Polynomial F => p.comp shift) hsum
      have hshift_pow :
          ∀ j : ℕ,
            shift ^ (j * q) =
              (Polynomial.X ^ q + Polynomial.C a : Polynomial F) ^ j := by
        intro j
        have h1 : shift ^ (j * q) = (shift ^ q) ^ j := by
          simpa [Nat.mul_comm] using (pow_mul shift q j)
        have h2 :
            shift ^ q = (Polynomial.X ^ q + Polynomial.C a : Polynomial F) := by
          have h :=
            (FiniteField.expand_card
                (Polynomial.X + Polynomial.C a : Polynomial F)).symm
          simpa [shift, hq, map_add, Polynomial.expand_X, Polynomial.expand_C] using h
        simp [h1, h2]
      have hg2 :
          g ^ ℓ *
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj' j) + (sj' j) * g ^ c) *
                    (Polynomial.X ^ q + Polynomial.C a : Polynomial F) ^ j) =
            0 := by
        have hsum_eq :
            Finset.sum (Finset.range J)
                (fun j =>
                  ((rj' j) + (sj' j) * g ^ c) * shift ^ (j * q)) =
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj' j) + (sj' j) * g ^ c) *
                    (Polynomial.X ^ q + Polynomial.C a : Polynomial F) ^ j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [hshift_pow j]
        simpa [hsum_eq] using hg1
      let t : Polynomial F := Polynomial.X ^ q + Polynomial.C a
      let sum_total : Polynomial F :=
        ∑ j ∈ Finset.range J,
          ((rj' j) + (sj' j) * g ^ c) * t ^ j
      have hg2' : g ^ ℓ * sum_total = 0 := by
        simpa [t, sum_total] using hg2
      let sum_r : Polynomial F :=
        ∑ j ∈ Finset.range J, rj' j * t ^ j
      let sum_s_base : Polynomial F :=
        ∑ j ∈ Finset.range J, sj' j * t ^ j
      have hsum_split :
          sum_total = sum_r + g ^ c * sum_s_base := by
        unfold sum_total sum_r sum_s_base
        calc
          (∑ j ∈ Finset.range J,
              ((rj' j) + (sj' j) * g ^ c) * t ^ j)
              = ∑ j ∈ Finset.range J,
                  (rj' j * t ^ j + (sj' j * g ^ c) * t ^ j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    simp [add_mul]
          _ = (∑ j ∈ Finset.range J, rj' j * t ^ j) +
                ∑ j ∈ Finset.range J, (sj' j * g ^ c) * t ^ j := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  (Finset.sum_add_distrib
                    (s := Finset.range J)
                    (f := fun j => rj' j * t ^ j)
                    (g := fun j => (sj' j * g ^ c) * t ^ j))
          _ = (∑ j ∈ Finset.range J, rj' j * t ^ j) +
                g ^ c * ∑ j ∈ Finset.range J, sj' j * t ^ j := by
                have h :
                  ∑ j ∈ Finset.range J, (sj' j * g ^ c) * t ^ j =
                    g ^ c * ∑ j ∈ Finset.range J, sj' j * t ^ j := by
                  have h1 :
                    (∑ j ∈ Finset.range J, (sj' j * g ^ c) * t ^ j) =
                      ∑ j ∈ Finset.range J, g ^ c * (sj' j * t ^ j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ac_rfl
                  have h2 :
                    g ^ c * ∑ j ∈ Finset.range J, sj' j * t ^ j =
                      ∑ j ∈ Finset.range J, g ^ c * (sj' j * t ^ j) := by
                    exact
                      Finset.mul_sum
                        (s := Finset.range J)
                        (f := fun j => sj' j * t ^ j)
                        (a := g ^ c)
                  exact h1.trans h2.symm
                simp [h]
      let R : ℕ → Polynomial F := fun k =>
        ∑ j ∈ Finset.Ico k J,
          (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * rj' j
      let S : ℕ → Polynomial F := fun k =>
        ∑ j ∈ Finset.Ico k J,
          (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * sj' j
      have hcoeff_r :
          sum_r =
            ∑ k ∈ Finset.range J,
              R k * Polynomial.X ^ (k * q) := by
        unfold sum_r R t
        simpa using
          (coefficient_transformation_shift (F := F)
            (a := a) (q := q) (J := J) (A := rj'))
      have hcoeff_s_base :
          sum_s_base =
            ∑ k ∈ Finset.range J,
              S k * Polynomial.X ^ (k * q) := by
        unfold sum_s_base t S
        simpa using
          (coefficient_transformation_shift (F := F)
            (a := a) (q := q) (J := J) (A := sj'))
      have hsum_total_eq :
          sum_total =
            ∑ k ∈ Finset.range J,
              (R k + S k * g ^ c) * Polynomial.X ^ (k * q) := by
        calc
          sum_total = sum_r + g ^ c * sum_s_base := hsum_split
          _ =
              (∑ k ∈ Finset.range J,
                  R k * Polynomial.X ^ (k * q)) +
                g ^ c * sum_s_base := by
                rw [hcoeff_r]
          _ =
              (∑ k ∈ Finset.range J,
                  R k * Polynomial.X ^ (k * q)) +
                g ^ c *
                  (∑ k ∈ Finset.range J,
                    S k * Polynomial.X ^ (k * q)) := by
                rw [hcoeff_s_base]
          _ =
              (∑ k ∈ Finset.range J,
                  R k * Polynomial.X ^ (k * q)) +
                ∑ k ∈ Finset.range J,
                  g ^ c * (S k * Polynomial.X ^ (k * q)) := by
                have hmul :
                    g ^ c *
                        ∑ k ∈ Finset.range J,
                          S k * Polynomial.X ^ (k * q) =
                      ∑ k ∈ Finset.range J,
                        g ^ c * (S k * Polynomial.X ^ (k * q)) := by
                  exact
                    Finset.mul_sum
                      (s := Finset.range J)
                      (f := fun k => S k * Polynomial.X ^ (k * q))
                      (a := g ^ c)
                have :=
                  congrArg
                    (fun p =>
                      (∑ k ∈ Finset.range J,
                          R k * Polynomial.X ^ (k * q)) + p)
                    hmul
                simpa using this
          _ =
              ∑ k ∈ Finset.range J,
                (R k * Polynomial.X ^ (k * q) +
                  g ^ c * (S k * Polynomial.X ^ (k * q))) := by
                have :=
                  Finset.sum_add_distrib
                    (s := Finset.range J)
                    (f := fun k => R k * Polynomial.X ^ (k * q))
                    (g := fun k =>
                      g ^ c * (S k * Polynomial.X ^ (k * q)))
                simpa [add_comm, add_left_comm, add_assoc] using this.symm
          _ =
              ∑ k ∈ Finset.range J,
                (R k + S k * g ^ c) * Polynomial.X ^ (k * q) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                calc
                  R k * Polynomial.X ^ (k * q) +
                      g ^ c * (S k * Polynomial.X ^ (k * q)) =
                      R k * Polynomial.X ^ (k * q) +
                        (S k * g ^ c) * Polynomial.X ^ (k * q) := by
                          ac_rfl
                  _ =
                      (R k + S k * g ^ c) *
                        Polynomial.X ^ (k * q) := by
                        rw [add_mul]
      have hg3 :
          g ^ ℓ *
              Finset.sum (Finset.range J)
                (fun k =>
                  (R k + S k * g ^ c) * Polynomial.X ^ (k * q)) = 0 := by
        simpa [sum_total, hsum_total_eq] using hg2'
      have hdeg_RS :
          ∀ k < J,
            (R k).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
            (S k).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 := by
        intro k hk
        refine ⟨?_, ?_⟩
        · simpa [R] using
            coefficient_transformation_degree_bound
              (F := F) (a := a) (J := J)
              (d := Nat.ceil (((q : ℚ) - m) / 2) - 1)
              (A := rj')
              (hdeg := fun j hj => (hdeg_shifted j hj).1)
              k hk
        · simpa [S] using
            coefficient_transformation_degree_bound
              (F := F) (a := a) (J := J)
              (d := Nat.ceil (((q : ℚ) - m) / 2) - 1)
              (A := sj')
              (hdeg := fun j hj => (hdeg_shifted j hj).2)
              k hk
      have hstep_g : ∀ k < J, R k = 0 ∧ S k = 0 :=
        (stepanov_nonzero_eval_zero (F := F) (hF := hF)
          (f := g) (q := q) (m := m) (ℓ := ℓ) (J := J) (c := c)
          (hc := hc) (hq := hq) (hfdeg := hgdeg) (hm_pos := hm_pos)
          (hq6m := hq6m) (hf0 := hg0_ne)
          (rj := R) (sj := S) (hnsq := hnsq_g) (hdeg := hdeg_RS)).mp hg3
      have hR_eq_zero :
          ∀ k < J,
            ∑ j ∈ Finset.Ico k J,
                (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * rj' j = 0 :=
        fun k hk => by
          simpa [R] using (hstep_g k hk).1
      have hS_eq_zero :
          ∀ k < J,
            ∑ j ∈ Finset.Ico k J,
                (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * sj' j = 0 :=
        fun k hk => by
          simpa [S] using (hstep_g k hk).2
      have hrj'_zero : ∀ j < J, rj' j = 0 :=
        triangular_inversion_shift (F := F) (a := a) (J := J)
          (A := rj') hR_eq_zero
      have hsj'_zero : ∀ j < J, sj' j = 0 :=
        triangular_inversion_shift (F := F) (a := a) (J := J)
          (A := sj') hS_eq_zero
      intro j hj
      have hrj_comp_zero : (rj j).comp (Polynomial.X + Polynomial.C a) = 0 := by
        simpa [rj', shift] using hrj'_zero j hj
      have hsj_comp_zero : (sj j).comp (Polynomial.X + Polynomial.C a) = 0 := by
        simpa [sj', shift] using hsj'_zero j hj
      exact
        ⟨(Polynomial.comp_X_add_C_eq_zero_iff (p := rj j) (t := a)).mp
            hrj_comp_zero,
          (Polynomial.comp_X_add_C_eq_zero_iff (p := sj j) (t := a)).mp
            hsj_comp_zero⟩
  · intro hall
    have :
        Finset.sum (Finset.range J)
            (fun j =>
              ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        obtain ⟨hrj, hsj⟩ := hall j (Finset.mem_range.mp hj)
        simp [hrj, hsj]
    simp [this]
/- BEGIN PORTED MODULE StepanovDegreeBounds -/

lemma stepanov_polynomial_natDegree_le (F : Type*) [Field F] [Fintype F] (f : Polynomial F)
  (q m ℓ c d J : ℕ) (hfdeg : f.natDegree = m) (rj sj : ℕ → Polynomial F)
  (hdegr : ∀ j < J, (rj j).natDegree ≤ d) (hdegs : ∀ j < J, (sj j).natDegree ≤ d) :
  (f^ℓ * (Finset.sum (Finset.range J)
    (fun j => ((rj j) + (sj j) * f^c) * Polynomial.X^(j*q)))).natDegree
      ≤ ℓ * m + d + c * m + (J - 1) * q :=
by
  let fsum : ℕ → Polynomial F :=
    fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)
  have h_fsum_deg : ∀ j < J, (fsum j).natDegree ≤ d + c * m + j * q := by
    intro j hj
    have hdeg_sj_fc : ((sj j) * f ^ c).natDegree ≤ d + c * m :=
      (Polynomial.natDegree_mul_le (p := sj j) (q := f ^ c)).trans
        (Nat.add_le_add (hdegs j hj) (by simp [hfdeg]))
    have hdeg_sum : ((rj j) + (sj j) * f ^ c).natDegree ≤ d + c * m :=
      (Polynomial.natDegree_add_le (p := rj j) (q := (sj j) * f ^ c)).trans
        (max_le_iff.2
          ⟨(hdegr j hj).trans (Nat.le_add_right _ _), hdeg_sj_fc⟩)
    have hmul :
        (((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)).natDegree ≤
          d + c * m + j * q :=
      (Polynomial.natDegree_mul_le
        (p := (rj j) + (sj j) * f ^ c)
        (q := Polynomial.X ^ (j * q))).trans
        (by
          have := Nat.add_le_add_right hdeg_sum (j * q)
          simpa [Polynomial.natDegree_X_pow (j * q)] using this)
    simpa [fsum] using hmul
  have h_sum_deg :
      (Finset.sum (Finset.range J) fsum).natDegree ≤ d + c * m + (J - 1) * q := by
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := Finset.range J) (f := fsum)
        (n := d + c * m + (J - 1) * q) ?_
    intro j hj
    have hj_lt : j < J := Finset.mem_range.mp hj
    exact
      (h_fsum_deg j hj_lt).trans
        (Nat.add_le_add_left
          (Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hj_lt)) _)
  have h_total :
      (f ^ ℓ * Finset.sum (Finset.range J) fsum).natDegree ≤
        ℓ * m + (d + c * m + (J - 1) * q) := by
    have hdeg_fℓ : (f ^ ℓ : Polynomial F).natDegree ≤ ℓ * m := by
      simp [hfdeg]
    exact
      (Polynomial.natDegree_mul_le
        (p := f ^ ℓ)
        (q := Finset.sum (Finset.range J) fsum)).trans
        (Nat.add_le_add hdeg_fℓ h_sum_deg)
  have h_rhs : ℓ * m + (d + c * m + (J - 1) * q) =
      ℓ * m + d + c * m + (J - 1) * q := by
    ac_rfl
  simpa [fsum, h_rhs] using h_total
/- BEGIN PORTED MODULE StepanovVanishing -/

lemma stepanov_vanishing_roots (F : Type*) [Field F] (f g : Polynomial F) (ℓ : ℕ) (x : F)
  (hx : Polynomial.eval x f = 0) :
  ∀ k < ℓ, (hasseDerivOp F k (f ^ ℓ * g)).eval x = 0 :=
by
  intro k hk
  rcases hasseDerivOp_mul_pow_dvd F k ℓ g f with ⟨Q, hQ⟩
  simp [mul_comm, hQ, hx, zero_pow (Nat.sub_ne_zero_of_lt hk)]

lemma stepanov_vanishing_nonzeros (F : Type*) [Field F] [Fintype F]
  (f : Polynomial F) (ℓ q c J : ℕ) (hq : q = Fintype.card F)
  (rj sj : ℕ → Polynomial F) (a x : F) (hkq : ∀ k < ℓ, k < q) (hvan :
    ∀ k < ℓ,
    Finset.sum (Finset.range J)
      (fun j =>
        (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x
          + a *
            ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) / f ^ (ℓ + c - k)).eval x) *
          x ^ j) = 0)
  (hx_ne : f.eval x ≠ 0) (hx_pow : (f.eval x) ^ c = a) :
  ∀ k < ℓ,
  (hasseDerivOp F k
    (f ^ ℓ * (Finset.sum (Finset.range J)
      (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q))))).eval x = 0 :=
by
  intro k hk
  obtain ⟨rjk, sjk, hrjk, hsjk, h_main⟩ :=
    stepanov_form F f ℓ q c J k hk hq (hkq k hk) rj sj
  rw [h_main, Polynomial.eval_mul, mul_eq_zero]
  right
  rw [Polynomial.eval_finset_sum]
  have hx_pow_q : x ^ q = x := by simpa [hq] using FiniteField.pow_card x
  have hrjk_div j : rjk j = hasseDerivOp F k (f ^ ℓ * rj j) / f ^ (ℓ - k) := by
    simpa using
      (EuclideanDomain.eq_div_of_mul_eq_left
        (pow_ne_zero _ (fun hf0 => hx_ne (by simp [hf0])))
        (hrjk j).symm)
  have hsjk_div j :
      sjk j = hasseDerivOp F k (f ^ (ℓ + c) * sj j) / f ^ (ℓ + c - k) := by
    simpa using
      (EuclideanDomain.eq_div_of_mul_eq_left
        (pow_ne_zero _ (fun hf0 => hx_ne (by simp [hf0])))
        (hsjk j).symm)
  simp_rw [fun j =>
    show
      Polynomial.eval x ((rjk j + sjk j * f ^ c) * Polynomial.X ^ (j * q)) =
        (Polynomial.eval x (hasseDerivOp F k (f ^ ℓ * rj j) / f ^ (ℓ - k)) +
            a *
              Polynomial.eval x
                (hasseDerivOp F k (f ^ (ℓ + c) * sj j) / f ^ (ℓ + c - k))) *
          x ^ j by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        mul_comm j q, pow_mul, hx_pow_q, Polynomial.eval_add, hrjk_div j,
        hsjk_div j, hx_pow]
      ring]
  exact hvan k hk
/- BEGIN PORTED MODULE StepanovSystem -/

lemma stepanov_sigma_degree_bound_fin
    (F : Type*) [Field F]
    (d k m J : ℕ) (a : F)
    (rjk sjk : Fin J → Polynomial F)
    (hdeg_r : ∀ j : Fin J, (rjk j).natDegree ≤ d + k * (m - 1))
    (hdeg_s : ∀ j : Fin J, (sjk j).natDegree ≤ d + k * (m - 1)) :
    (∑ j : Fin J, (rjk j + Polynomial.C a * sjk j) * Polynomial.X ^ (j : ℕ)).natDegree
      ≤ J - 1 + d + k * (m - 1) :=
by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  have hmul :=
    Polynomial.natDegree_mul_le
      (p := rjk j + Polynomial.C a * sjk j) (q := Polynomial.X ^ (j : ℕ))
  have h_sum : (rjk j + Polynomial.C a * sjk j).natDegree ≤ d + k * (m - 1) := by
    have :=
      (Polynomial.natDegree_add_le (rjk j) (Polynomial.C a * sjk j)).trans
        (max_le_max (hdeg_r j) (Polynomial.natDegree_C_mul_le a _))
    simpa [hdeg_s j] using this
  calc
    ((rjk j + Polynomial.C a * sjk j) * Polynomial.X ^ (j : ℕ)).natDegree
        ≤ (rjk j + Polynomial.C a * sjk j).natDegree + (j : ℕ) := by
          simpa [Polynomial.natDegree_X_pow] using hmul
    _ ≤ d + k * (m - 1) + (j : ℕ) :=
      Nat.add_le_add_right h_sum _
    _ ≤ J - 1 + d + k * (m - 1) := by
      have := add_le_add_left (Nat.le_pred_of_lt j.isLt) (d + k * (m - 1))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

lemma stepanov_system_constraint_count
    (ℓ J d m q : ℕ) (B : ℕ)
    (hℓ_pos : 0 < ℓ) (hm_ge_two : 2 ≤ m)
    (hq6m : 6 * m < q)
    (_hℓ : ℓ ≤ q / 3)
    (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
    (_hJ : 1 ≤ J)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1))) :
    B ≤ ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 ∧
    (B : ℝ) <
      (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
        (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
by
  have h_sum :
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
        ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
    have h_split :
        ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
          (∑ k ∈ Finset.range ℓ, (J + d)) +
            ∑ k ∈ Finset.range ℓ, k * (m - 1) := by
      calc
        ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
            ∑ k ∈ Finset.range ℓ, ((J + d) + k * (m - 1)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk; simp [add_assoc]
        _ = (∑ k ∈ Finset.range ℓ, (J + d)) +
              ∑ k ∈ Finset.range ℓ, k * (m - 1) := by
              simp [Finset.sum_add_distrib]
    have h_lin1 :
        ∑ k ∈ Finset.range ℓ, k * (m - 1) =
          (∑ k ∈ Finset.range ℓ, k) * (m - 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Finset.sum_mul (s := Finset.range ℓ)
          (f := fun k : ℕ => k) (a := m - 1)).symm
    have h_sum_id :
        ∑ k ∈ Finset.range ℓ, k = ℓ * (ℓ - 1) / 2 :=
      Finset.sum_range_id ℓ
    have h_even : Even (ℓ * (ℓ - 1)) := Nat.even_mul_pred_self ℓ
    have h_mul_div :
        (ℓ * (ℓ - 1) / 2) * (m - 1) =
          ℓ * (ℓ - 1) * (m - 1) / 2 := by
      have hL :
          2 * ((ℓ * (ℓ - 1) / 2) * (m - 1)) =
            (ℓ * (ℓ - 1)) * (m - 1) := by
        have htmp :=
          Nat.two_mul_div_two_of_even (n := ℓ * (ℓ - 1)) h_even
        calc
          2 * ((ℓ * (ℓ - 1) / 2) * (m - 1)) =
              (2 * (ℓ * (ℓ - 1) / 2)) * (m - 1) := by
                ac_rfl
          _ = (ℓ * (ℓ - 1)) * (m - 1) := by
                simp [htmp]
      have hR :
          2 * (ℓ * (ℓ - 1) * (m - 1) / 2) =
            ℓ * (ℓ - 1) * (m - 1) :=
        Nat.two_mul_div_two_of_even
          (n := ℓ * (ℓ - 1) * (m - 1)) (h_even.mul_right (m - 1))
      have h_eq0 :
          2 * ((ℓ * (ℓ - 1) / 2) * (m - 1)) =
            2 * (ℓ * (ℓ - 1) * (m - 1) / 2) := by
        calc
          2 * ((ℓ * (ℓ - 1) / 2) * (m - 1)) =
              (ℓ * (ℓ - 1)) * (m - 1) := hL
          _ = 2 * (ℓ * (ℓ - 1) * (m - 1) / 2) := by
                simp [hR]
      have h_eq :
          ((ℓ * (ℓ - 1) / 2) * (m - 1)) * 2 =
            (ℓ * (ℓ - 1) * (m - 1) / 2) * 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq0
      have hne : (2 : ℕ) ≠ 0 := by decide
      exact mul_right_cancel₀ hne h_eq
    calc
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
          (∑ k ∈ Finset.range ℓ, (J + d)) +
            ∑ k ∈ Finset.range ℓ, k * (m - 1) := h_split
      _ = ℓ * (J + d) + (ℓ * (ℓ - 1) / 2) * (m - 1) := by
        simp [Finset.sum_const, Finset.card_range, h_lin1, h_sum_id]
      _ = ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
        calc
          ℓ * (J + d) + (ℓ * (ℓ - 1) / 2) * (m - 1)
              = ℓ * J + ℓ * d + (ℓ * (ℓ - 1) / 2) * (m - 1) := by
                ring
          _ = ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
                simp [h_mul_div]
  have hB_nat :
      B ≤ ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
    simpa [h_sum] using hB
  have hB_real_le :
      (B : ℝ) ≤
        ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hB_nat
  have hx_pos : (0 : ℚ) < ((q : ℚ) - m) / 2 := by
    have hm_lt_q : m < q := by
      have hm_le_6m : m ≤ 6 * m := by
        simpa [Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_right m (show (1 : ℕ) ≤ 6 from by decide)
      exact lt_of_le_of_lt hm_le_6m hq6m
    have : (m : ℚ) < (q : ℚ) := by exact_mod_cast hm_lt_q
    exact div_pos (sub_pos.mpr this) (by norm_num)
  have hd_lt_rat : (d : ℚ) < ((q : ℚ) - m) / 2 :=
    Nat.lt_ceil.mp <| Nat.lt_of_le_pred (Nat.ceil_pos.mpr hx_pos) (by simp [hd])
  have hd_lt_real : (d : ℝ) < ((q : ℝ) - (m : ℝ)) / 2 := by
    exact_mod_cast hd_lt_rat
  have hEd_lt :
      (ℓ : ℝ) * (d : ℝ) <
        (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) :=
    mul_lt_mul_of_pos_left hd_lt_real (by exact_mod_cast hℓ_pos)
  have hS_cast :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) =
        (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          ((ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) := by
    simp [Nat.cast_add, Nat.cast_mul, add_assoc]
  have h_div_le :
      ((ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) ≤
        ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 := by
    simpa [Nat.cast_mul, mul_assoc, div_eq_mul_inv] using
      (Nat.cast_div_le (α := ℝ)
        (m := ℓ * (ℓ - 1) * (m - 1)) (n := 2))
  have hℓ_sub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    have hℓ_ge1 : 1 ≤ ℓ := Nat.succ_le_of_lt hℓ_pos
    simpa using (Nat.cast_sub (R := ℝ) hℓ_ge1)
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have hm_ge1 : 1 ≤ m :=
      le_trans (show (1 : ℕ) ≤ 2 by decide) hm_ge_two
    simpa using (Nat.cast_sub (R := ℝ) hm_ge1)
  have hCf_eq :
      ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 =
        (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    simp [hℓ_sub, hm_sub, mul_assoc]
  have hS_le_target1 :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) ≤
        (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    have h' :=
      add_le_add_left
        (add_le_add_left h_div_le ((ℓ : ℝ) * (d : ℝ)))
        ((ℓ : ℝ) * (J : ℝ))
    simpa [hS_cast, hCf_eq, add_assoc, add_comm, add_left_comm] using h'
  have hAEC_lt :
      (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 <
        (ℓ : ℝ) * (J : ℝ) +
          (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    linarith
  have hS_lt_target :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) <
        (ℓ : ℝ) *
          ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
            (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by
    have h' :
        ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) <
          (ℓ : ℝ) * (J : ℝ) +
            (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 :=
      lt_of_le_of_lt hS_le_target1 hAEC_lt
    have h_target_eq :
        (ℓ : ℝ) * (J : ℝ) +
            (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 =
          (ℓ : ℝ) *
            ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
              (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by
      ring
    simpa [h_target_eq] using h'
  have hB_lt :
      (B : ℝ) <
        (ℓ : ℝ) *
          ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
            (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
    lt_of_le_of_lt hB_real_le hS_lt_target
  exact ⟨hB_nat, hB_lt⟩

lemma stepanov_monotone_in_J
    {J₁ J₂ D ℓ x C : ℝ}
    (hA : 2 * J₁ * D > ℓ * (J₁ + x) + C)
    (hD_nonneg : 0 ≤ 2 * D - ℓ)
    (hJmono : J₁ ≤ J₂) :
  2 * J₂ * D > ℓ * (J₂ + x) + C :=
by
  have hmono :
      2 * J₁ * D - ℓ * (J₁ + x) ≤ 2 * J₂ * D - ℓ * (J₂ + x) :=
    sub_nonneg.mp <| by
      have h : 0 ≤ (J₂ - J₁) * (2 * D - ℓ) :=
        mul_nonneg (sub_nonneg.mpr hJmono) hD_nonneg
      have :
          (2 * J₂ * D - ℓ * (J₂ + x)) -
            (2 * J₁ * D - ℓ * (J₁ + x)) =
            (J₂ - J₁) * (2 * D - ℓ) := by
        ring
      simpa [this] using h
  simpa [add_comm] using
    (lt_sub_iff_add_lt).1 <|
      lt_of_lt_of_le
        ((lt_sub_iff_add_lt).2 (by simpa [add_comm] using hA))
        hmono

lemma stepanov_twoD_sub_ell_pos
    (q m ℓ : ℕ) (hq6m : q > 6 * m) (hℓ : ℓ ≤ q / 3) :
  0 < 2 * (Int.ceil (((q : ℝ) - (m : ℝ)) / 2) : ℝ) - (ℓ : ℝ) :=
by
  have hm_lt_qdiv6 : (m : ℝ) < (q : ℝ) / 6 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < (6 : ℝ))).mpr <|
      by
        have h : (6 : ℝ) * (m : ℝ) < (q : ℝ) := by
          exact_mod_cast (by simpa [Nat.mul_comm] using hq6m : 6 * m < q)
        simpa [mul_comm] using h
  have hℓ_le_qdiv3 : (ℓ : ℝ) ≤ (q : ℝ) / 3 := by
    have h1 : (ℓ : ℝ) ≤ ((q / 3 : ℕ) : ℝ) := by exact_mod_cast hℓ
    have h2 : ((q / 3 : ℕ) : ℝ) ≤ (q : ℝ) / 3 := by
      simpa using (Nat.cast_div_le (α := ℝ) (m := q) (n := 3))
    exact le_trans h1 h2
  set x : ℝ := ((q : ℝ) - (m : ℝ)) / 2 with hx
  have h_lt : (ℓ : ℝ) < 2 * (Int.ceil x : ℝ) := by
    have h_ell_lt_qm : (ℓ : ℝ) < (q : ℝ) - (m : ℝ) := by
      have h : (q : ℝ) / 2 < (q : ℝ) - (m : ℝ) - (ℓ : ℝ) := by
        nlinarith [hm_lt_qdiv6, hℓ_le_qdiv3]
      nlinarith [h]
    have h_qm_le : (q : ℝ) - (m : ℝ) ≤ 2 * (Int.ceil x : ℝ) := by
      have hx_two : (2 : ℝ) * x = (q : ℝ) - (m : ℝ) := by
        have : x + x = (q : ℝ) - (m : ℝ) := by simp [hx, add_halves]
        simpa [two_mul] using this
      have := (mul_le_mul_of_nonneg_left (Int.le_ceil x) (by norm_num) :
        (2 : ℝ) * x ≤ (2 : ℝ) * (Int.ceil x : ℝ))
      simpa [hx_two] using this
    exact lt_of_lt_of_le h_ell_lt_qm h_qm_le
  exact sub_pos.mpr (by simpa [hx] using h_lt)

lemma stepanov_system_dimension_inequality_nat
    (q m ℓ : ℕ)
    (hm_ge_two : 2 ≤ m) (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
    (hℓ_pos : 0 < ℓ)
    (B : ℕ)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ,
      (Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) +
        (Nat.ceil (((q : ℚ) - m) / 2) - 1) + k * (m - 1))) :
    let J := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
    2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B :=
by
  intro J
  -- basic integer setup
  set d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1 with hd
  have hB_le : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
    simpa [J, hd, add_comm, add_left_comm, add_assoc] using hB
  have hq6m_nat : 6 * m < q := by simpa [Nat.mul_comm] using hq6m
  have hq_pos_nat : 0 < q := lt_of_le_of_lt (Nat.zero_le (6 * m)) hq6m_nat
  have hm_lt_q : m < q :=
    lt_of_le_of_lt
      (by
        have h16 : (1 : ℕ) ≤ 6 := by decide
        have := Nat.mul_le_mul_right m h16
        simpa [Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this)
      hq6m_nat
  -- positivity of the expression defining J
  have hJ_expr_pos :
      0 < ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) := by
    have hℓ_posℚ : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ_pos
    have h_half_pos : (0 : ℚ) < (ℓ : ℚ) / 2 :=
      div_pos hℓ_posℚ (by norm_num : (0 : ℚ) < 2)
    have hq_posℚ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq_pos_nat
    have h_div_nonneg :
        (0 : ℚ) ≤ ((ℓ : ℚ) ^ 2 * (m : ℚ)) / (q : ℚ) :=
      div_nonneg
        (mul_nonneg (pow_two_nonneg _) (by exact_mod_cast (Nat.zero_le m)))
        (le_of_lt hq_posℚ)
    have h_add :
        (0 : ℚ) < (ℓ : ℚ) / 2 + ((ℓ : ℚ) ^ 2 * (m : ℚ)) / (q : ℚ) :=
      add_pos_of_pos_of_nonneg h_half_pos h_div_nonneg
    simpa [add_comm] using h_add
  have hJ_pos : 1 ≤ J :=
    (Nat.one_le_ceil_iff
      (a := ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)))).2
      hJ_expr_pos
  -- apply constraint-count inequality and simplify its RHS a bit
  have hB_real_small :
      (B : ℝ) <
        (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
          (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
    (stepanov_system_constraint_count ℓ J d m q B
      hℓ_pos hm_ge_two hq6m_nat hl hd hJ_pos hB_le).2
  -- some simple arithmetic bounds
  have hℓ_nonneg : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Nat.zero_le ℓ)
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm_ge_two
  have hm1_nonneg : 0 ≤ (m : ℝ) - 1 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hm_pos)
    exact sub_nonneg.mpr hm1
  -- compare the quadratic term in ℓ with a simpler upper bound
  have hcoef_le :
      ((ℓ : ℝ) - 1) * ((m : ℝ) - 1) ≤ (ℓ : ℝ) * ((m : ℝ) - 1) := by
    have htmp : (ℓ : ℝ) - 1 ≤ (ℓ : ℝ) :=
      sub_le_self _ (show (0 : ℝ) ≤ 1 by norm_num)
    exact mul_le_mul_of_nonneg_right htmp hm1_nonneg
  have hcoef_div_le :
      (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 ≤
        (ℓ : ℝ) * ((m : ℝ) - 1) / 2 := by
    have h_half_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_right hcoef_le h_half_nonneg
    simpa [div_eq_mul_inv, mul_assoc] using this
  have hterm_mul_le :
      (ℓ : ℝ) * ((((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) ≤
        (ℓ : ℝ) * (((ℓ : ℝ) * ((m : ℝ) - 1)) / 2) :=
    mul_le_mul_of_nonneg_left hcoef_div_le hℓ_nonneg
  have h_end :
      (ℓ : ℝ) * (((ℓ : ℝ) * ((m : ℝ) - 1)) / 2) =
        (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 := by
    simp [pow_two, mul_assoc, div_eq_mul_inv]
  have h_constr_le_Bmax_J :
      (ℓ : ℝ) *
          ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
            (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2)
        ≤ (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 := by
    calc
      (ℓ : ℝ) *
            ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
              (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2)
          = (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
              (ℓ : ℝ) * ((((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by
            ring
      _ ≤ (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) * (((ℓ : ℝ) * ((m : ℝ) - 1)) / 2) :=
        by linarith
      _ = (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 := by
        simp [h_end]
  have hB_lt_Bmax_J :
      (B : ℝ) <
        (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
          (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 :=
    lt_of_lt_of_le hB_real_small h_constr_le_Bmax_J
  -- switch to a more convenient notation over ℝ
  set Jreal : ℝ :=
      (ℓ : ℝ) / 2 + ((ℓ : ℝ) ^ 2 * (m : ℝ)) / (q : ℝ) with hJreal_def
  set xR : ℝ := ((q : ℝ) - (m : ℝ)) / 2 with hxR_def
  set D : ℝ := (Int.ceil xR : ℝ) with hD_def
  set C : ℝ := (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 with hC_def
  -- nonnegativity of 2D − ℓ
  have hD_nonneg : 0 ≤ 2 * D - (ℓ : ℝ) := by
    have hpos := stepanov_twoD_sub_ell_pos q m ℓ hq6m hl
    have : 0 < 2 * (Int.ceil xR : ℝ) - (ℓ : ℝ) := by
      simpa [xR, hxR_def, D, hD_def] using hpos
    exact le_of_lt this
  -- relate Jreal and J (ceil over ℚ vs ℝ)
  set tQ : ℚ :=
      (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) with htQ_def
  have htQ_le_ceil : (tQ : ℚ) ≤ Nat.ceil tQ := Nat.le_ceil tQ
  have hJreal_le_J : Jreal ≤ (J : ℝ) := by
    have : (tQ : ℝ) ≤ (Nat.ceil tQ : ℝ) := by exact_mod_cast htQ_le_ceil
    simpa [Jreal, tQ, hJreal_def, htQ_def] using this
  -- define A_real and Bmax_real
  set A_real : ℝ := 2 * Jreal * D with hAreal_def
  set Bmax_real : ℝ :=
      (ℓ : ℝ) * (Jreal + xR) + C with hBmax_def
  -- lower bound on A_real
  have hA_ge : Jreal * ((q : ℝ) - (m : ℝ)) ≤ A_real := by
    have hx_le_ceil : xR ≤ (Int.ceil xR : ℝ) := Int.le_ceil xR
    have hJreal_nonneg : (0 : ℝ) ≤ Jreal := by
      have h1 : (0 : ℝ) ≤ (ℓ : ℝ) / 2 :=
        div_nonneg hℓ_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h2 :
          (0 : ℝ) ≤ ((ℓ : ℝ) ^ 2 * (m : ℝ)) / (q : ℝ) := by
        have hnum : (0 : ℝ) ≤ (ℓ : ℝ) ^ 2 * (m : ℝ) :=
          mul_nonneg (pow_two_nonneg _) (by exact_mod_cast (Nat.zero_le m))
        have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
        exact div_nonneg hnum (le_of_lt hq_pos)
      have := add_nonneg h1 h2
      simpa [Jreal, hJreal_def] using this
    have h2J_nonneg : (0 : ℝ) ≤ 2 * Jreal :=
      mul_nonneg (by norm_num) hJreal_nonneg
    have hmul :
        (2 * Jreal) * xR ≤
          (2 * Jreal) * (Int.ceil xR : ℝ) :=
      mul_le_mul_of_nonneg_left hx_le_ceil h2J_nonneg
    have hx_two : (2 : ℝ) * xR = (q : ℝ) - (m : ℝ) := by
      have : xR + xR = (q : ℝ) - (m : ℝ) := by
        simp [xR, add_halves]
      simpa [two_mul] using this
    have hA_left :
        (2 * Jreal) * xR = Jreal * ((q : ℝ) - (m : ℝ)) := by
      calc
        (2 * Jreal) * xR = Jreal * (2 * xR) := by ac_rfl
        _ = Jreal * ((q : ℝ) - (m : ℝ)) := by simp [hx_two]
    have hA_eq :
        (2 * Jreal) * (Int.ceil xR : ℝ) = A_real := by
      simp [A_real, hAreal_def, D]
    have hA_aux : (2 * Jreal) * xR ≤ A_real := by
      simpa [hA_eq] using hmul
    simpa [hA_left] using hA_aux
  -- key inequality Jreal*(q-m) > Bmax_real
  have hJ_gt_Bmax : Bmax_real < Jreal * ((q : ℝ) - (m : ℝ)) := by
    -- first rewrite the difference in a more symmetric way
    have hD_eq :
        Jreal * ((q : ℝ) - (m : ℝ)) - Bmax_real =
          (Jreal - (ℓ : ℝ) / 2) *
              ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
            (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      have :
          Jreal * ((q : ℝ) - (m : ℝ)) -
              ((ℓ : ℝ) * (Jreal + xR) +
                (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2) =
            (Jreal - (ℓ : ℝ) / 2) *
                ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
              (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
        have :
            Jreal * ((q : ℝ) - (m : ℝ)) -
                ((ℓ : ℝ) *
                    (Jreal + ((q : ℝ) - (m : ℝ)) / 2) +
                      (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2) =
              (Jreal - (ℓ : ℝ) / 2) *
                  ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
                (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
          ring_nf
        simpa [xR, hxR_def] using this
      simpa [Bmax_real, hBmax_def] using this
    have h_eqJ :
        Jreal - (ℓ : ℝ) / 2 =
          (ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ) := by
      simp [Jreal, sub_eq_add_neg, add_comm, add_assoc]
    have hJ_minus_pos : 0 < Jreal - (ℓ : ℝ) / 2 := by
      have hℓ_sq_pos : 0 < (ℓ : ℝ) ^ 2 := by
        have hℓ_pos' : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
        have := pow_pos hℓ_pos' (2 : ℕ)
        simpa [pow_two] using this
      have hpos_num : 0 < (ℓ : ℝ) ^ 2 * (m : ℝ) :=
        mul_pos hℓ_sq_pos (by exact_mod_cast hm_pos)
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
      have : 0 < (ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ) :=
        div_pos hpos_num hq_pos
      simpa [h_eqJ] using this
    -- obtain that q/2 < q − m − ℓ
    have hq6m_real : (6 : ℝ) * (m : ℝ) < (q : ℝ) := by exact_mod_cast hq6m_nat
    have hm_lt_qdiv6 : (m : ℝ) < (q : ℝ) / 6 := by
      have h6pos : (0 : ℝ) < (6 : ℝ) := by norm_num
      have : (m : ℝ) * 6 < (q : ℝ) := by
        simpa [mul_comm] using hq6m_real
      exact (lt_div_iff₀ h6pos).mpr this
    have hℓ_le_qdiv3 : (ℓ : ℝ) ≤ (q : ℝ) / 3 := by
      have hℓ_le_nat : (ℓ : ℝ) ≤ ((q / 3 : ℕ) : ℝ) := by
        exact_mod_cast hl
      have hqdiv3_le : ((q / 3 : ℕ) : ℝ) ≤ (q : ℝ) / 3 := by
        simpa using (Nat.cast_div_le (α := ℝ) (m := q) (n := 3))
      exact le_trans hℓ_le_nat hqdiv3_le
    have h_qmℓ_gt :
        (q : ℝ) / 2 < (q : ℝ) - (m : ℝ) - (ℓ : ℝ) := by
      nlinarith [hm_lt_qdiv6, hℓ_le_qdiv3]
    -- compare two products using the previous inequality
    have h_prod_gt :
        (Jreal - (ℓ : ℝ) / 2) *
            ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) >
          (Jreal - (ℓ : ℝ) / 2) * ((q : ℝ) / 2) :=
      mul_lt_mul_of_pos_left h_qmℓ_gt hJ_minus_pos
    have h_prod_eq :
        (Jreal - (ℓ : ℝ) / 2) * ((q : ℝ) / 2) =
          (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      have hq_ne : (q : ℝ) ≠ 0 := by
        have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
        exact ne_of_gt hq_pos
      calc
        (Jreal - (ℓ : ℝ) / 2) * ((q : ℝ) / 2)
            = ((ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ)) * ((q : ℝ) / 2) := by
              simp [h_eqJ]
        _ = (((ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ)) * (q : ℝ)) / 2 := by
              simp [div_eq_mul_inv, mul_assoc]
        _ = (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
              simp [div_eq_mul_inv, hq_ne, mul_assoc]
    have hmain :
        (Jreal - (ℓ : ℝ) / 2) *
            ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) >
          (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      simpa [h_prod_eq] using h_prod_gt
    have hD_pos :
        Jreal * ((q : ℝ) - (m : ℝ)) - Bmax_real > 0 := by
      have hD2_pos :
          (Jreal - (ℓ : ℝ) / 2) *
              ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
            (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 > 0 :=
        sub_pos.mpr hmain
      simpa [hD_eq] using hD2_pos
    exact sub_pos.mp hD_pos
  -- combine to get Bmax_real < A_real
  have hA_gt_Bmax : Bmax_real < A_real :=
    lt_of_lt_of_le hJ_gt_Bmax hA_ge
  -- monotonicity in J
  have hA_gt_Bmax_J :
      2 * (J : ℝ) * D >
        (ℓ : ℝ) * ((J : ℝ) + xR) + C :=
    stepanov_monotone_in_J (J₁ := Jreal) (J₂ := (J : ℝ)) (D := D)
      (ℓ := (ℓ : ℝ)) (x := xR) (C := C)
      (by
        have :
            (ℓ : ℝ) * (Jreal + xR) + C <
              2 * Jreal * D := by
          simpa [A_real, hAreal_def, Bmax_real, hBmax_def] using hA_gt_Bmax
        simpa using this)
      (by simpa [D, hD_def] using hD_nonneg)
      hJreal_le_J
  have hB_lt_A_real :
      (B : ℝ) < 2 * (J : ℝ) * D :=
    lt_of_lt_of_le hB_lt_Bmax_J (le_of_lt hA_gt_Bmax_J)
  -- convert the statement back to ℚ / ℕ
  set xQ : ℚ := ((q : ℚ) - m) / 2 with hxQ_def
  have hxQ_nonneg : 0 ≤ xQ := by
    have hsub_nonneg : 0 ≤ (q : ℚ) - m :=
      sub_nonneg.mpr (by exact_mod_cast (le_of_lt hm_lt_q))
    have htwo_nonneg : (0 : ℚ) ≤ 2 := by norm_num
    exact div_nonneg hsub_nonneg htwo_nonneg
  have h_natInt_expr :
      (Nat.ceil (((q : ℚ) - m) / 2) : ℝ) =
        (Int.ceil (((q : ℝ) - (m : ℝ)) / 2) : ℝ) := by
    have h1 : (Nat.ceil xQ : ℝ) = (Int.ceil xQ : ℝ) := by
      exact_mod_cast
        (Int.natCast_ceil_eq_ceil (R := ℚ) (a := xQ) hxQ_nonneg)
    have h2 : (Int.ceil xQ : ℝ) = (Int.ceil (xQ : ℝ) : ℝ) := by
      exact_mod_cast (Rat.ceil_cast (α := ℝ) xQ).symm
    have hx : (xQ : ℝ) = xR := by
      simp [xQ, xR]
    calc
      (Nat.ceil (((q : ℚ) - m) / 2) : ℝ)
          = (Nat.ceil xQ : ℝ) := rfl
      _ = (Int.ceil xQ : ℝ) := h1
      _ = (Int.ceil (xQ : ℝ) : ℝ) := h2
      _ = (Int.ceil xR : ℝ) := by simp [hx]
  have hA_nat_real :
      (2 * J * Nat.ceil (((q : ℚ) - m) / 2) : ℝ) =
        (2 * (J : ℝ)) * (Int.ceil xR : ℝ) := by
    simp [h_natInt_expr, xR]
  have hB_lt_A_nat_real :
      (B : ℝ) <
        (2 * J * Nat.ceil (((q : ℚ) - m) / 2) : ℝ) := by
    simpa [hA_nat_real, D, hD_def] using hB_lt_A_real
  exact
    (by
      exact_mod_cast hB_lt_A_nat_real :
        2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B)

lemma exists_nonzero_solution_of_finrank_lt
    (F : Type*) [Field F]
    (V W : Type*) [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (L : V →ₗ[F] W)
    (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 :=
by
  obtain ⟨v, hv_mem, hv_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (p := LinearMap.ker L)
      (by
        intro hker
        have hk0 : Module.finrank F (LinearMap.ker L) = 0 := by
          simp [hker]
        exact
          (ne_of_lt
            (lt_of_le_of_lt (Submodule.finrank_le (s := LinearMap.range L)) h))
            (by
              simpa [hk0] using
                LinearMap.finrank_range_add_finrank_ker (f := L)))
  refine ⟨v, hv_ne, ?_⟩
  simpa using hv_mem

lemma natDegree_le_of_mem_degreeLT_succ
    (F : Type*) [Semiring F] (d : ℕ) (p : Polynomial.degreeLT F (d + 1)) :
    (p : Polynomial F).natDegree ≤ d :=
by
  have h := p.2
  simp only [Polynomial.mem_degreeLT] at h
  refine Nat.lt_succ_iff.mp ?_
  by_cases hp : (p : Polynomial F) = 0
  · simp [hp]
  · rw [Polynomial.degree_eq_natDegree hp] at h
    exact WithBot.coe_lt_coe.mp h

lemma stepanov_dimension_inequality_ceil
    (F : Type*) [Field F]
    (ℓ d m q B : ℕ)
    (hℓ_pos : 0 < ℓ) (hm_ge_two : 2 ≤ m)
    (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
    (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ,
      (Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) + d + k * (m - 1))) :
  let J := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
  Module.finrank F (Fin B → F) <
    Module.finrank F (Fin (2 * J) → Polynomial.degreeLT F (d + 1)) :=
by
  intro J
  have hceil_nat : 1 ≤ Nat.ceil (((q : ℚ) - m) / 2) := by
    refine Nat.one_le_ceil_iff.mpr ?_
    have hm_lt_q : m < q :=
      lt_of_le_of_lt
        (by
          simpa [Nat.one_mul] using
            Nat.mul_le_mul_right m (show (1 : ℕ) ≤ 6 by decide))
        (by simpa using hq6m)
    have : (0 : ℚ) < (q : ℚ) - m :=
      sub_pos.mpr (by exact_mod_cast hm_lt_q)
    simpa using div_pos this (show (0 : ℚ) < (2 : ℚ) by norm_num)
  have hA_gt_B :
      2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B :=
    stepanov_system_dimension_inequality_nat q m ℓ hm_ge_two hq6m hl hℓ_pos B
      (by simpa [hd] using hB)
  simpa [ Module.finrank_pi_fintype,
          Module.finrank_fintype_fun_eq_card,
          LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F (d + 1)),
          hd, Nat.sub_add_cancel hceil_nat ] using hA_gt_B

noncomputable def polyMulRightLinear (F : Type*) [Field F] (g : Polynomial F) :
    Polynomial F →ₗ[F] Polynomial F :=
{ toFun := fun p => p * g
  map_add' := by
    intro p q
    simp [add_mul]
  map_smul' := by
    intro a p
    simp }

noncomputable def polyDivRightLinear (F : Type*) [Field F] {g : Polynomial F} (hg : g ≠ 0) :
    (LinearMap.range (polyMulRightLinear (F:=F) g)) →ₗ[F] Polynomial F :=
  (LinearEquiv.ofInjective (polyMulRightLinear (F:=F) g)
      (fun _ _ => mul_right_cancel₀ hg)).symm.toLinearMap

noncomputable def stepanovHasseQuotMap
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) :
    Polynomial F →ₗ[F] Polynomial F := by
  let g : Polynomial F := f ^ (r - k)
  let mulG : Polynomial F →ₗ[F] Polynomial F := polyMulRightLinear (F := F) g
  let numMap : Polynomial F →ₗ[F] Polynomial F :=
    (Polynomial.hasseDeriv k).comp (polyMulRightLinear (F := F) (f ^ r))
  have hmem : ∀ p, numMap p ∈ LinearMap.range mulG := by
    intro p
    have hdiv :
        f ^ (r - k) ∣ hasseDerivOp F k (p * f ^ r) :=
      hasseDerivOp_mul_pow_dvd F k r p f
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨q, ?_⟩
    have hq' : hasseDerivOp F k (p * f ^ r) = q * f ^ (r - k) := by
      simpa [mul_comm] using hq
    simpa [numMap, mulG, g, hasseDerivOp, polyMulRightLinear] using hq'.symm
  exact
    (polyDivRightLinear (F := F) (g := g) (pow_ne_zero _ hf)).comp
      (LinearMap.codRestrict (LinearMap.range mulG) numMap hmem)

lemma stepanovHasseQuotMap_mul
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p * f ^ (r - k) =
      hasseDerivOp F k (p * f ^ r) :=
by
  set g : Polynomial F := f ^ (r - k) with hgdef
  set numMap : Polynomial F →ₗ[F] Polynomial F :=
    (Polynomial.hasseDeriv k).comp (polyMulRightLinear (F := F) (f ^ r)) with hnumMap
  have hmem : ∀ p, numMap p ∈ LinearMap.range (polyMulRightLinear (F := F) g) := by
    intro p
    rcases hasseDerivOp_mul_pow_dvd F k r p f with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simpa [numMap, g, hasseDerivOp, polyMulRightLinear, mul_comm] using hq.symm
  set z : LinearMap.range (polyMulRightLinear (F := F) g) :=
    LinearMap.codRestrict (LinearMap.range (polyMulRightLinear (F := F) g)) numMap hmem p
      with hz
  calc
    stepanovHasseQuotMap (F := F) (f := f) hf r k p * f ^ (r - k)
        = polyMulRightLinear (F := F) g
            (polyDivRightLinear (F := F) (g := g) (pow_ne_zero _ hf) z) := by
          rfl
    _ = z := by
          exact congrArg Subtype.val
            ((LinearEquiv.ofInjective (polyMulRightLinear (F := F) g)
              (fun _ _ => mul_right_cancel₀ (pow_ne_zero _ hf))).apply_symm_apply z)
    _ = numMap p := rfl
    _ = hasseDerivOp F k (p * f ^ r) := by
      simp [numMap, polyMulRightLinear, LinearMap.comp_apply, hasseDerivOp]

lemma stepanovHasseQuotMap_eq_div
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p =
      hasseDerivOp F k (p * f ^ r) / f ^ (r - k) :=
by
  refine mul_right_cancel₀ (pow_ne_zero (r - k) hf) ?_
  refine (stepanovHasseQuotMap_mul (F := F) (f := f) hf r k p).trans ?_
  simpa [mul_comm] using
    (EuclideanDomain.mul_div_cancel'
      (a := hasseDerivOp F k (p * f ^ r))
      (b := f ^ (r - k))
      (pow_ne_zero (r - k) hf)
      (hasseDerivOp_mul_pow_dvd F k r p f)).symm

lemma stepanovHasseQuotMap_eq_div_left
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p =
      hasseDerivOp F k (f ^ r * p) / f ^ (r - k) :=
by simpa [mul_comm] using stepanovHasseQuotMap_eq_div (F := F) hf r k p

lemma stepanovHasseQuotMap_natDegree_le
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (m d r k : ℕ) (hfdeg : f.natDegree = m) (hk : k ≤ r)
    (p : Polynomial F) (hp : p.natDegree ≤ d) :
    (stepanovHasseQuotMap (F := F) (f := f) hf r k p).natDegree
      ≤ d + k * (m - 1) :=
by
  obtain ⟨rjk, _, hr_eq, -, hdeg_rjk, -⟩ :=
    auxiliary_derivatives (F := F) f m d r 0 hfdeg p 0 hp (by simp) k hk
  have h_eq :
      stepanovHasseQuotMap (F := F) (f := f) hf r k p = rjk := by
    refine mul_right_cancel₀ (pow_ne_zero (r - k) hf) ?_
    have hmul :=
      stepanovHasseQuotMap_mul (F := F) (f := f) hf r k p
    have hr_eq' : hasseDerivOp F k (p * f ^ r) = rjk * f ^ (r - k) := by
      simpa [mul_comm] using hr_eq
    simpa [hmul] using hr_eq'
  simpa [h_eq] using hdeg_rjk

lemma finrank_stepanov_constraint_space
    (F : Type*) [Field F] (ℓ J d m : ℕ) :
    Module.finrank F (∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1))) =
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) :=
by
  calc
    Module.finrank F (∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1)))
        = ∑ k : Fin ℓ, (J + d + k * (m - 1)) := by
          simp [Module.finrank_pi_fintype,
            Module.finrank_fintype_fun_eq_card,
            LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F _)]
    _ = ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
          simpa using
            (Fin.sum_univ_eq_sum_range (n := ℓ) (fun k => J + d + k * (m - 1)))

lemma stepanov_system_has_solution
  (F : Type*) [Field F] [Fintype F]
  (f : Polynomial F) (q m ℓ : ℕ) (a : F)
  (_hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
  (hm_ge_two : 2 ≤ m) (_hm_pos : 0 < m) (hℓ_pos : 0 < ℓ)
  (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
  (hJ_pos :
      1 ≤ Nat.ceil (((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)))) :
  let d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1
  let J : ℕ := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
  ∃ rj sj : ℕ → Polynomial F,
    (∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) ∧
    (∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d) ∧
    (∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ ((q - 1) / 2) = a →
      ∀ k < ℓ,
        Finset.sum (Finset.range J)
          (fun j =>
            (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
              a *
                ((hasseDerivOp F k (f ^ (ℓ + ((q - 1) / 2)) * sj j)) /
                    f ^ (ℓ + ((q - 1) / 2) - k)).eval x) *
              x ^ j) = 0) :=
by
  set d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1 with hd
  set J : ℕ := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) with hJdef
  simp [d, J]
  have hf : f ≠ 0 := by
    rintro hf0
    have hm0 : m = 0 := by simpa [hf0] using hfdeg.symm
    have : (2 : ℕ) ≤ 0 := by simp [hm0] at hm_ge_two
    exact (by decide : ¬ (2 ≤ 0)) this
  let c : ℕ := (q - 1) / 2
  let V := Fin (2 * J) → Polynomial.degreeLT F (d + 1)
  let W := ∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1))
  let finLeft : Fin J → Fin (2 * J) := fun j =>
    ⟨j, lt_of_lt_of_le j.isLt (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))⟩
  let finRight : Fin J → Fin (2 * J) := fun j =>
    ⟨J + j, by simp [two_mul, add_comm]⟩
  let piProj : Fin (2 * J) → V →ₗ[F] Polynomial.degreeLT F (d + 1) := fun i =>
    { toFun := fun v => v i
      map_add' := by intro v w; rfl
      map_smul' := by intro a v; rfl }
  let rjMap : Fin J → V →ₗ[F] Polynomial F := fun j =>
    (Polynomial.degreeLT F (d + 1)).subtype.comp (piProj (finLeft j))
  let sjMap : Fin J → V →ₗ[F] Polynomial F := fun j =>
    (Polynomial.degreeLT F (d + 1)).subtype.comp (piProj (finRight j))
  let rjkMap : Fin ℓ → Fin J → V →ₗ[F] Polynomial F := fun k j =>
    (stepanovHasseQuotMap (F := F) (f := f) hf ℓ k.1).comp (rjMap j)
  let sjkMap : Fin ℓ → Fin J → V →ₗ[F] Polynomial F := fun k j =>
    (stepanovHasseQuotMap (F := F) (f := f) hf (ℓ + c) k.1).comp (sjMap j)
  let sigmaMap : Fin ℓ → V →ₗ[F] Polynomial F := fun k =>
    Finset.sum (Finset.univ : Finset (Fin J))
      (fun j =>
        (polyMulRightLinear (F := F) (Polynomial.X ^ (j : ℕ))).comp
          (rjkMap k j + a • sjkMap k j))
  have h_sigma_deg :
      ∀ k : Fin ℓ, ∀ v : V,
        (sigmaMap k v).natDegree ≤ J - 1 + d + k * (m - 1) := by
    intro k v
    let rjkFin : Fin J → Polynomial F := fun j => rjkMap k j v
    let sjkFin : Fin J → Polynomial F := fun j => sjkMap k j v
    have hdeg_r : ∀ j : Fin J, (rjkFin j).natDegree ≤ d + k * (m - 1) := by
      intro j
      have hk_le : k.1 ≤ ℓ := Nat.le_of_lt k.isLt
      simp only [rjkFin, rjkMap, rjMap]
      exact
        stepanovHasseQuotMap_natDegree_le (F := F) hf m d ℓ k.1 hfdeg hk_le
          _ (natDegree_le_of_mem_degreeLT_succ F d (piProj (finLeft j) v))
    have hdeg_s : ∀ j : Fin J, (sjkFin j).natDegree ≤ d + k * (m - 1) := by
      intro j
      have hk_le : k.1 ≤ ℓ + c := le_trans (Nat.le_of_lt k.isLt) (Nat.le_add_right _ _)
      simp only [sjkFin, sjkMap, sjMap]
      exact
        stepanovHasseQuotMap_natDegree_le (F := F) hf m d (ℓ + c) k.1 hfdeg hk_le
          _ (natDegree_le_of_mem_degreeLT_succ F d (piProj (finRight j) v))
    have hdeg_sum :=
      stepanov_sigma_degree_bound_fin (F := F) (d := d) (k := k) (m := m) (J := J)
        (a := a) rjkFin sjkFin hdeg_r hdeg_s
    have hsum :
        sigmaMap k v =
          ∑ j : Fin J, (rjkFin j + Polynomial.C a * sjkFin j) * Polynomial.X ^ (j : ℕ) := by
      simp [sigmaMap, rjkFin, sjkFin, polyMulRightLinear,
        LinearMap.add_apply, LinearMap.smul_apply, Polynomial.smul_eq_C_mul]
    simpa [hsum] using hdeg_sum
  let sigmaMapLT :
      (k : Fin ℓ) → V →ₗ[F] Polynomial.degreeLT F (J + d + k * (m - 1)) :=
    fun k =>
      LinearMap.codRestrict (Polynomial.degreeLT F (J + d + k * (m - 1))) (sigmaMap k) (by
        intro v
        by_cases hzero : sigmaMap k v = 0
        · simp [hzero]
        · have hdeg_nat : (sigmaMap k v).natDegree < J + d + k * (m - 1) := by
            have hlt : J - 1 + d + k * (m - 1) < J + d + k * (m - 1) := by
              omega
            exact lt_of_le_of_lt (h_sigma_deg k v) hlt
          have hdeg : (sigmaMap k v).degree < (J + d + k * (m - 1) : ℕ) :=
            (Polynomial.natDegree_lt_iff_degree_lt hzero).1 hdeg_nat
          simpa [Polynomial.mem_degreeLT] using hdeg)
  let L : V →ₗ[F] W := LinearMap.pi (fun k => sigmaMapLT k)
  set B : ℕ := ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) with hBdef
  have hW_finrank : Module.finrank F W = B := by
    simpa [W, hBdef] using finrank_stepanov_constraint_space F ℓ J d m
  have h_dim :
      Module.finrank F (Fin B → F) <
        Module.finrank F V := by
    have hB_le : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
      simp [B]
    have h := stepanov_dimension_inequality_ceil
      (F := F) (ℓ := ℓ) (d := d) (m := m) (q := q) (B := B)
      hℓ_pos hm_ge_two hq6m hl hd
      (by
        simpa [J, hJdef, add_comm, add_left_comm, add_assoc] using hB_le)
    simpa [J, hJdef, V] using h
  have hB_lt : B < Module.finrank F V := by
    have hFin : Module.finrank F (Fin B → F) = B := by simp
    simpa [hFin] using h_dim
  have hW_lt : Module.finrank F W < Module.finrank F V := by
    simpa [hW_finrank] using hB_lt
  obtain ⟨v, hv_ne, hv_zero⟩ :=
    exists_nonzero_solution_of_finrank_lt (L := L) (h := by simpa [V] using hW_lt)
  let rj : ℕ → Polynomial F := fun j =>
    if hj : j < J then (rjMap ⟨j, hj⟩ v) else 0
  let sj : ℕ → Polynomial F := fun j =>
    if hj : j < J then (sjMap ⟨j, hj⟩ v) else 0
  have h_nonzero : ∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0 := by
    by_contra h
    push_neg at h
    have hv_zero' : v = 0 := by
      funext i
      change v i = 0
      have hi : (i : ℕ) < J ∨ J ≤ (i : ℕ) := lt_or_ge (i : ℕ) J
      cases hi with
      | inl hlt =>
          have : rj i = 0 := (h i hlt).1
          simpa [rj, hlt, rjMap, piProj, finLeft] using this
      | inr hge =>
          have hj : (i : ℕ) - J < J := by
            have hlt : (i : ℕ) < 2 * J := i.isLt
            omega
          have : sj ((i : ℕ) - J) = 0 := (h ((i : ℕ) - J) hj).2
          have hidx : finRight ⟨(i : ℕ) - J, hj⟩ = i := by
            ext
            simp [finRight, Nat.add_sub_of_le hge]
          simpa [sj, hj, sjMap, piProj, hidx] using this
    exact hv_ne hv_zero'
  have hdeg :
      ∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d := by
    intro j hj
    have hr : (rj j).natDegree ≤ d := by
      simp [rj, hj, rjMap, piProj, finLeft,
        natDegree_le_of_mem_degreeLT_succ]
    have hs : (sj j).natDegree ≤ d := by
      simp [sj, hj, sjMap, piProj, finRight,
        natDegree_le_of_mem_degreeLT_succ]
    exact ⟨hr, hs⟩
  have hvan :
      ∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ c = a →
        ∀ k < ℓ,
          Finset.sum (Finset.range J)
            (fun j =>
              (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
                  a *
                    ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) /
                        f ^ (ℓ + c - k)).eval x) *
                x ^ j) = 0 := by
    intro x _hx _hxa k hk
    have hLk : sigmaMapLT ⟨k, hk⟩ v = 0 := by
      change L v ⟨k, hk⟩ = (0 : W) ⟨k, hk⟩
      exact congrArg (fun f => f ⟨k, hk⟩) hv_zero
    have hpoly_zero : sigmaMap ⟨k, hk⟩ v = 0 := by
      have := congrArg Subtype.val hLk
      simpa [sigmaMapLT] using this
    have hsum_eval :
        (sigmaMap ⟨k, hk⟩ v).eval x =
          Finset.sum (Finset.range J)
            (fun j =>
              (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
                  a *
                    ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) /
                        f ^ (ℓ + c - k)).eval x) *
                x ^ j) := by
      classical
      let p : Fin J → Polynomial F := fun j =>
        hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k) +
          Polynomial.C a *
            (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) / f ^ (ℓ + c - k))
      have hsum_poly :
          sigmaMap ⟨k, hk⟩ v =
            ∑ j : Fin J,
              p j * Polynomial.X ^ (j : ℕ) := by
        simp [p, sigmaMap, rjkMap, sjkMap, stepanovHasseQuotMap_eq_div_left,
          polyMulRightLinear, LinearMap.comp_apply, LinearMap.add_apply,
          LinearMap.smul_apply, Polynomial.smul_eq_C_mul]
      have hsum_eval_fin :
          (sigmaMap ⟨k, hk⟩ v).eval x =
            ∑ j : Fin J,
              (p j).eval x * x ^ (j : ℕ) := by
        have :=
          (Polynomial.eval_finset_sum (s := (Finset.univ : Finset (Fin J)))
            (g := fun j : Fin J => p j * Polynomial.X ^ (j : ℕ)) (x := x))
        simpa [hsum_poly] using this
      have hsum_eval_fin' :
          (sigmaMap ⟨k, hk⟩ v).eval x =
            ∑ j : Fin J,
              ((hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k)).eval x +
                a *
                  (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) /
                    f ^ (ℓ + c - k)).eval x) *
                x ^ (j : ℕ) := by
        simpa [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          mul_add, mul_assoc] using hsum_eval_fin
      let G : Fin J → F := fun j =>
        ((hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k)).eval x +
            a *
              (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) /
                f ^ (ℓ + c - k)).eval x) *
          x ^ (j : ℕ)
      have hsum_eval_finG :
          (sigmaMap ⟨k, hk⟩ v).eval x = ∑ j : Fin J, G j := by
        simpa [G] using hsum_eval_fin'
      let GNat : ℕ → F := fun j =>
        if hj : j < J then G ⟨j, hj⟩ else 0
      have hsum_eval_finGNat :
          (sigmaMap ⟨k, hk⟩ v).eval x = ∑ j : Fin J, GNat j := by
        refine hsum_eval_finG.trans ?_
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [GNat, j.isLt]
      have hsum_range := (Fin.sum_univ_eq_sum_range (n := J) (f := GNat))
      refine (hsum_eval_finGNat.trans hsum_range).trans ?_
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj' : j < J := by
        simpa using (Finset.mem_range.mp hj)
      simp [GNat, G, rj, sj, hj']
    have : (sigmaMap ⟨k, hk⟩ v).eval x = 0 := by
      simp [hpoly_zero]
    simpa [hsum_eval] using this
  refine ⟨rj, sj, h_nonzero, hdeg, hvan⟩

lemma stepanov_constructed_nonzero
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q m ℓ J c d : ℕ)
  (hq : q = Fintype.card F) (hfdeg : f.natDegree = m) (hc : c = (q - 1) / 2)
  (hm_pos : 0 < m)
  (hq6m : q > 6 * m)
  (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (rj sj : ℕ → Polynomial F)
  (hdeg : ∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d)
  (hnz : ∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) :
  f^ℓ * (Finset.sum (Finset.range J)
    (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) ≠ 0 :=
by
  intro hz
  have hzero :=
    (stepanov_nonzero F hF f q m ℓ J c hc hq hfdeg hm_pos hq6m rj sj hnsq
      (by simpa [hd] using hdeg)).1 hz
  rcases hnz with ⟨j, hj, h_or⟩
  exact h_or.elim (· (hzero j hj).1) (· (hzero j hj).2)
/- BEGIN PORTED MODULE StepanovPolynomial -/

noncomputable def S_a (F : Type*) [Field F] (f : Polynomial F) (c : ℕ) (a : F) : Set F :=
  {x | Polynomial.eval x f = 0 ∨ (Polynomial.eval x f) ^ c = a}

theorem stepanov_polynomial
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q ℓ : ℕ) (a : F)
  (hq : q = Fintype.card F) (hm3 : 3 ≤ f.natDegree)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (hq6m : q > 6 * f.natDegree) (hℓ_pos : 0 < ℓ) (hl : ℓ ≤ q / 3) :
  ∃ r : Polynomial F,
    r ≠ 0 ∧
    ((r.natDegree : ℝ) <
      ((f.natDegree * q : ℕ) : ℝ) +
        ((ℓ * q : ℕ) : ℝ) / 2 +
        ((ℓ * ℓ * f.natDegree : ℕ) : ℝ)) ∧
    (∀ x ∈ S_a F f ((q - 1) / 2) a, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) :=
by
  set m : ℕ := f.natDegree with hm_def
  have hfdeg : f.natDegree = m := by simp [hm_def]
  have hm3' : 3 ≤ m := by simpa [hm_def] using hm3
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm3'
  have hm_ge_two : 2 ≤ m := le_trans (by decide : 2 ≤ 3) hm3'
  have h6mq : 6 * m < q := by simpa [hm_def] using hq6m
  have hq_pos_nat : 0 < q := lt_of_le_of_lt (Nat.zero_le _) h6mq
  let c : ℕ := (q - 1) / 2
  have hc : c = (q - 1) / 2 := rfl
  let d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1
  have hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1 := rfl
  set Jreal : ℚ := (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) with hJreal_def
  set J : ℕ := Nat.ceil Jreal with hJ_def
  have hJ_expr_pos :
      0 < (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) := by
    have hhalf_pos : (0 : ℚ) < (ℓ : ℚ) / 2 :=
      div_pos (by exact_mod_cast hℓ_pos) (by norm_num)
    have hdiv_nonneg :
        (0 : ℚ) ≤ (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) :=
      div_nonneg
        (mul_nonneg (pow_two_nonneg _) (by exact_mod_cast (Nat.zero_le m)))
        (le_of_lt (by exact_mod_cast hq_pos_nat))
    exact add_pos_of_pos_of_nonneg hhalf_pos hdiv_nonneg
  have hJ_pos :
      1 ≤ Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) :=
    Nat.one_le_ceil_iff.mpr hJ_expr_pos
  have h_system' :
      ∃ rj sj : ℕ → Polynomial F,
        (∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) ∧
        (∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d) ∧
        (∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ c = a →
          ∀ k < ℓ,
            Finset.sum (Finset.range J)
              (fun j =>
                (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
                    a *
                      ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) /
                          f ^ (ℓ + c - k)).eval x) *
                  x ^ j) = 0) := by
    simpa [d, hd, J, hJ_def, Jreal, hJreal_def, c, hc] using
      (stepanov_system_has_solution
        (F := F) (f := f) (q := q) (m := m) (ℓ := ℓ) (a := a)
        hq hfdeg hm_ge_two hm_pos hℓ_pos (by simpa [hm_def] using hq6m) hl hJ_pos)
  rcases h_system' with ⟨rj, sj, hnz, hdeg, hvan⟩
  set R : Polynomial F :=
    f ^ ℓ *
      Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)) with hR_def
  have hdegr : ∀ j < J, (rj j).natDegree ≤ d := fun j hj => (hdeg j hj).1
  have hdegs : ∀ j < J, (sj j).natDegree ≤ d := fun j hj => (hdeg j hj).2
  have hR_ne_zero : R ≠ 0 := by
    simpa [R, hR_def] using
      (stepanov_constructed_nonzero
        (F := F) (hF := hF) (f := f) (q := q) (m := m) (ℓ := ℓ)
        (J := J) (c := c) (d := d)
        hq hfdeg hc hm_pos (by simpa [hm_def] using hq6m) hd hnsq rj sj (by
          intro j hj; exact ⟨hdegr j hj, hdegs j hj⟩) hnz)
  have hdeg_nat_le :
      R.natDegree ≤ ℓ * m + d + c * m + (J - 1) * q := by
    simpa [R, hR_def] using
      (stepanov_polynomial_natDegree_le
        (F := F) (f := f) (q := q) (m := m) (ℓ := ℓ)
        (c := c) (d := d) (J := J)
        hfdeg rj sj hdegr hdegs)
  let Jm1 : ℕ := J - 1
  have hdeg_le_coreJ :
      (R.natDegree : ℚ)
        ≤ (ℓ : ℚ) * (m : ℚ) + (d : ℚ) + (c : ℚ) * (m : ℚ)
          + (Jm1 : ℚ) * (q : ℚ) := by
    have : (R.natDegree : ℚ) ≤ ((ℓ * m + d + c * m + Jm1 * q : ℕ) : ℚ) := by
      exact_mod_cast (by simpa [Jm1] using hdeg_nat_le)
    simpa [Nat.cast_add, Nat.cast_mul] using this
  set core : ℚ := (ℓ : ℚ) * (m : ℚ) + (d : ℚ) + (c : ℚ) * (m : ℚ) with hcore_def
  have hdeg_core_le :
      (R.natDegree : ℚ) ≤ core + (Jm1 : ℚ) * (q : ℚ) := by
    simpa [core, add_assoc] using hdeg_le_coreJ
  have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq_pos_nat
  have hm_pos' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm_pos
  have hℓ_le_q_div3 : (ℓ : ℚ) ≤ (q : ℚ) / 3 := by
    have h1 : (ℓ : ℚ) ≤ ((q / 3 : ℕ) : ℚ) := by exact_mod_cast hl
    exact le_trans h1 (by simpa using (Nat.cast_div_le (α := ℚ) (m := q) (n := 3)))
  have hℓm_le : (ℓ : ℚ) * (m : ℚ) ≤ (q : ℚ) / 3 * (m : ℚ) :=
    mul_le_mul_of_nonneg_right hℓ_le_q_div3 (le_of_lt hm_pos')
  have hx1_le_hx2 : (((q : ℚ) - (m : ℚ)) / 2) ≤ (q : ℚ) / 2 := by
    simpa [sub_eq_add_neg] using
      (div_le_div_of_nonneg_right
        (sub_le_self _ (by exact_mod_cast (Nat.zero_le m))) (by norm_num))
  have hceil_le :
      Nat.ceil (((q : ℚ) - (m : ℚ)) / 2)
        ≤ Nat.ceil ((q : ℚ) / 2) :=
    Nat.ceil_le_ceil hx1_le_hx2
  have hd_le_ceil_x1 :
      d ≤ Nat.ceil (((q : ℚ) - (m : ℚ)) / 2) := by
    simp [hd]
  have hd_le_ceil_x2 : d ≤ Nat.ceil ((q : ℚ) / 2) :=
    le_trans hd_le_ceil_x1 hceil_le
  have hd_le : (d : ℚ) ≤ (q : ℚ) / 2 + 1 := by
    have hx2_nonneg : (0 : ℚ) ≤ (q : ℚ) / 2 :=
      div_nonneg (le_of_lt hq_pos) (by norm_num)
    exact le_trans (by exact_mod_cast hd_le_ceil_x2)
      (le_of_lt (Nat.ceil_lt_add_one hx2_nonneg))
  have h2c_le_q1_nat : 2 * c ≤ q - 1 := by
    simpa [c, hc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.div_mul_le_self (q - 1) 2)
  have h2c_le_q1 : (2 : ℚ) * (c : ℚ) ≤ (q : ℚ) - 1 := by
    have hq_ge_one : 1 ≤ q := Nat.succ_le_of_lt hq_pos_nat
    simpa [Nat.cast_mul, Nat.cast_sub hq_ge_one, mul_comm, mul_left_comm, mul_assoc] using
      (show ((2 * c : ℕ) : ℚ) ≤ ((q - 1 : ℕ) : ℚ) from by exact_mod_cast h2c_le_q1_nat)
  have hc_le : (c : ℚ) ≤ ((q : ℚ) - 1) / 2 := by
    have h2_pos : (0 : ℚ) < (2 : ℚ) := by norm_num
    have hq1_eq' :
        (2 : ℚ) * (((q : ℚ) - 1) / 2) = (q : ℚ) - 1 := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm,
        (two_ne_zero : (2 : ℚ) ≠ 0)]
    have h2c_le : (2 : ℚ) * (c : ℚ)
        ≤ (2 : ℚ) * (((q : ℚ) - 1) / 2) := by
      simpa [hq1_eq'] using h2c_le_q1
    exact (le_of_mul_le_mul_left h2c_le h2_pos)
  have hcm_le : (c : ℚ) * (m : ℚ)
      ≤ ((q : ℚ) - 1) / 2 * (m : ℚ) :=
    mul_le_mul_of_nonneg_right hc_le (le_of_lt hm_pos')
  have h_d_add_c :
      (d : ℚ) + (c : ℚ) * (m : ℚ)
        ≤ (q : ℚ) / 2 + 1 + ((q : ℚ) - 1) / 2 * (m : ℚ) :=
    add_le_add hd_le hcm_le
  have hcore_le :
      core ≤ (q : ℚ) / 3 * (m : ℚ) + (q : ℚ) / 2 + 1
                + ((q : ℚ) - 1) / 2 * (m : ℚ) := by
    simpa [core, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using (add_le_add hℓm_le h_d_add_c)
  let B2 : ℚ :=
    (q : ℚ) / 3 * (m : ℚ) + (q : ℚ) / 2 + 1
      + ((q : ℚ) - 1) / 2 * (m : ℚ)
  have hcore_le_B2 : core ≤ B2 := by
    simpa [B2, add_comm, add_left_comm, add_assoc] using hcore_le
  have h_num_pos :
      0 < (q : ℚ) * ((m : ℚ) - 3) + 3 * ((m : ℚ) - 2) := by
    refine add_pos_of_nonneg_of_pos ?_ ?_
    · exact mul_nonneg (le_of_lt hq_pos) (sub_nonneg.mpr (by exact_mod_cast hm3'))
    · have hm_gt2_nat : 2 < m := lt_of_lt_of_le (by decide : 2 < 3) hm3'
      exact mul_pos (by norm_num) (sub_pos.mpr (by exact_mod_cast hm_gt2_nat))
  have h_eq :
      6 * ((m : ℚ) * (q : ℚ) - B2)
        = (q : ℚ) * ((m : ℚ) - 3) + 3 * ((m : ℚ) - 2) := by
    simpa [B2] using (by ring :
      6 * ((m : ℚ) * (q : ℚ) -
            ((q : ℚ) / 3 * (m : ℚ) + (q : ℚ) / 2 + 1
              + ((q : ℚ) - 1) / 2 * (m : ℚ)))
        = (q : ℚ) * ((m : ℚ) - 3) + 3 * ((m : ℚ) - 2))
  have h6Δ_pos : 0 < 6 * ((m : ℚ) * (q : ℚ) - B2) := by
    simpa [h_eq] using h_num_pos
  have hΔ_pos : 0 < (m : ℚ) * (q : ℚ) - B2 := by
    have h6Δ_pos' : 0 < ((m : ℚ) * (q : ℚ) - B2) * 6 := by
      simpa [mul_comm] using h6Δ_pos
    exact pos_of_mul_pos_left h6Δ_pos' (by norm_num)
  have hB2_lt : B2 < (m : ℚ) * (q : ℚ) := sub_pos.mp hΔ_pos
  have hcore_lt_mq : core < (m : ℚ) * (q : ℚ) :=
    lt_of_le_of_lt hcore_le_B2 hB2_lt
  have hcore_lt_mq_addJm1 :
      core + (Jm1 : ℚ) * (q : ℚ)
        < (m : ℚ) * (q : ℚ) + (Jm1 : ℚ) * (q : ℚ) :=
    by linarith
  have hdeg_lt_mqJm1_rat :
      (R.natDegree : ℚ) < (m : ℚ) * (q : ℚ) + (Jm1 : ℚ) * (q : ℚ) :=
    lt_of_le_of_lt hdeg_core_le hcore_lt_mq_addJm1
  have hJreal_nonneg : (0 : ℚ) ≤ Jreal := by
    have h1 : (0 : ℚ) ≤ (ℓ : ℚ) / 2 :=
      div_nonneg (by exact_mod_cast (Nat.zero_le ℓ)) (by norm_num)
    have hnum : (0 : ℚ) ≤ (ℓ : ℚ) ^ 2 * (m : ℚ) := by
      have hℓsq_nonneg : (0 : ℚ) ≤ (ℓ : ℚ) ^ 2 := by
        simp
      exact mul_nonneg hℓsq_nonneg (by exact_mod_cast (Nat.zero_le m))
    have h2 : (0 : ℚ) ≤ (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) :=
      div_nonneg hnum (le_of_lt hq_pos)
    have := add_nonneg h1 h2
    simpa [Jreal, hJreal_def] using this
  have hJm1_le_Jreal : (Jm1 : ℚ) ≤ Jreal := by
    have hceil_sub : (Nat.ceil Jreal : ℚ) - 1 ≤ Jreal := by
      have h1 : (Nat.ceil Jreal : ℚ) ≤ Jreal + 1 :=
        le_of_lt (Nat.ceil_lt_add_one hJreal_nonneg)
      linarith
    have hJ_eq : J = Nat.ceil Jreal := by simp [hJ_def]
    have hJ_ge_one : 1 ≤ J := by
      simpa [Jreal, hJreal_def, hJ_def] using hJ_pos
    have hJm1_cast : (Jm1 : ℚ) = (J : ℚ) - 1 := by
      simpa [Jm1] using (Nat.cast_sub (R := ℚ) hJ_ge_one)
    simpa [hJ_def, hJm1_cast] using hceil_sub
  have hJm1q_le : (Jm1 : ℚ) * (q : ℚ) ≤ Jreal * (q : ℚ) := by
    exact mul_le_mul_of_nonneg_right hJm1_le_Jreal (le_of_lt hq_pos)
  have hJrealq_eq :
      Jreal * (q : ℚ) =
        (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    simp [Jreal, div_eq_mul_inv, mul_add,
      mul_comm, mul_assoc, (ne_of_gt hq_pos)]
  have hJm1q_le_target :
      (Jm1 : ℚ) * (q : ℚ)
        ≤ (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    simpa [hJrealq_eq] using hJm1q_le
  have h_total_le :
      (m : ℚ) * (q : ℚ) + (Jm1 : ℚ) * (q : ℚ)
        ≤ (m : ℚ) * (q : ℚ)
          + (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    linarith
  have hdeg_lt_target_Q :
      (R.natDegree : ℚ)
        < (m : ℚ) * (q : ℚ)
          + (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) :=
    lt_of_lt_of_le hdeg_lt_mqJm1_rat h_total_le
  have hdeg_lt_target_R :
      (R.natDegree : ℝ)
        < ((m * q : ℕ) : ℝ)
          + ((ℓ * q : ℕ) : ℝ) / 2
          + ((ℓ ^ 2 * m : ℕ) : ℝ) := by
    have h' :
        (R.natDegree : ℝ) <
          ((m : ℚ) * (q : ℚ)
            + (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) : ℝ) := by
      exact_mod_cast hdeg_lt_target_Q
    simpa [Nat.cast_mul, pow_two, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using h'
  refine ⟨R, hR_ne_zero, ?_, ?_⟩
  · simpa [hm_def, pow_two, Nat.mul_assoc] using hdeg_lt_target_R
  · intro x hx k hk
    rcases hx with hx_zero | hx_pow
    · simpa using
        (stepanov_vanishing_roots
          (F := F) (f := f)
          (g :=
            Finset.sum (Finset.range J)
              (fun j =>
                ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)))
          (ℓ := ℓ) (x := x) hx_zero k hk)
    · by_cases hx0 : f.eval x = 0
      · simpa using
          (stepanov_vanishing_roots
            (F := F) (f := f)
            (g :=
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)))
            (ℓ := ℓ) (x := x) hx0 k hk)
      · have hvan_x :
            ∀ k' < ℓ,
              Finset.sum (Finset.range J)
                (fun j =>
                  (((hasseDerivOp F k' (f ^ ℓ * rj j)) /
                        f ^ (ℓ - k')).eval x
                      +
                      a *
                        ((hasseDerivOp F k' (f ^ (ℓ + c) * sj j)) /
                            f ^ (ℓ + c - k')).eval x) *
                    x ^ j) = 0 :=
          hvan x hx0 hx_pow
        have h_all_k :=
          stepanov_vanishing_nonzeros
            (F := F) (f := f) (ℓ := ℓ) (q := q)
            (c := c) (J := J) hq rj sj a x
            (fun k' hk' => lt_of_lt_of_le hk' (le_trans hl (Nat.div_le_self _ _)))
            hvan_x hx0 hx_pow
        exact h_all_k k hk
/- BEGIN PORTED MODULE RiemannHypothesisHEC -/

noncomputable def hyperellipticCurve (F : Type*) [Field F] (f : Polynomial F) : Set (F × F) :=
  {p | p.2 ^ 2 = Polynomial.eval p.1 f}

lemma hasse_vanishing_card_bound
  (F : Type*) [Field F] [DecidableEq F]
  (r : Polynomial F) (ℓ : ℕ)
  (S : Finset F)
  (hr : r ≠ 0)
  (hℓ_pos : 0 < ℓ)
  (hvan : ∀ x ∈ S, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) :
  (S.card : ℝ) ≤ (r.natDegree : ℝ) / ℓ :=
by
  let s : F → Polynomial F := fun x => (Polynomial.X - Polynomial.C x) ^ ℓ
  have hpair_all : Pairwise fun x y : F => IsCoprime (s x) (s y) := by
    have hlin :
        Pairwise fun x y : F =>
          IsCoprime (Polynomial.X - Polynomial.C x)
            (Polynomial.X - Polynomial.C y) := by
      simpa [Function.onFun] using
        (Polynomial.pairwise_coprime_X_sub_C (K := F)
          (s := fun x : F => x) (H := fun {x} {y} h => h))
    exact hlin.mono fun x y hcop => by
      simpa [s] using (IsCoprime.pow hcop : _)
  have hprod_dvd : (∏ x ∈ S, s x) ∣ r := by
    refine
      Finset.prod_dvd_of_coprime (t := S) (s := s) (z := r) ?_ ?_
    · intro x hx y hy hxy
      simpa [Function.onFun] using hpair_all hxy
    · intro x hx
      simpa [s] using
        hasse_divisibility (F := F) (f := r) (a := x) (ℓ := ℓ) (hvan x hx)
  have hP_nat_eq :
      ((∏ x ∈ S, s x : Polynomial F).natDegree) = S.card * ℓ := by
    calc
      ((∏ x ∈ S, s x : Polynomial F).natDegree)
          = ∑ x ∈ S, (s x).natDegree := by
              simpa using
                (Polynomial.natDegree_prod_of_monic (s := S) (f := s)
                  (by
                    intro x hx
                    simpa [s] using (Polynomial.monic_X_sub_C x).pow ℓ))
      _ = ∑ x ∈ S, ℓ := by
            simp [s]
      _ = S.card * ℓ := by simp
  have h_nat' : S.card * ℓ ≤ r.natDegree := by
    have hnat_le :
        ((∏ x ∈ S, s x : Polynomial F).natDegree) ≤ r.natDegree :=
      (Polynomial.natDegree_le_iff_degree_le).2
        ((Polynomial.degree_le_of_dvd
            (p := ∏ x ∈ S, s x) (q := r) hprod_dvd hr).trans
          (Polynomial.degree_le_natDegree (p := r)))
    simpa [hP_nat_eq] using hnat_le
  have hℓ_pos' : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
  have h_real_mul : (S.card : ℝ) * (ℓ : ℝ) ≤ (r.natDegree : ℝ) := by
    exact_mod_cast h_nat'
  have hne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos'
  simpa [mul_comm, mul_left_comm, mul_assoc, hne, div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right h_real_mul (inv_nonneg.mpr hℓ_pos'.le))

lemma ceil_sqrt_le_div_three
  (q : ℕ) (hq : 15 ≤ q) :
  Nat.ceil (Real.sqrt q) ≤ q / 3 :=
by
  set k : ℕ := q / 3 with hk
  have hk_ge5 : 5 ≤ k := by
    have : 5 * 3 ≤ q := by simpa using hq
    simpa [hk] using (Nat.le_div_iff_mul_le (by decide : 0 < 3)).2 this
  have hq_le_2plus3k : q ≤ 2 + 3 * k := by
    have hmod : q % 3 ≤ 2 :=
      Nat.lt_succ_iff.mp (Nat.mod_lt q (by decide : 0 < 3))
    have h : q % 3 + k * 3 ≤ 2 + k * 3 := Nat.add_le_add_right hmod _
    simpa [hk, Nat.mod_add_div, Nat.mul_comm] using h
  have h2plus3k_le_kk : 2 + 3 * k ≤ k * k := by
    have h2_le_k : 2 ≤ k := (by decide : 2 ≤ 5).trans hk_ge5
    have h4_le_k : 4 ≤ k := (by decide : 4 ≤ 5).trans hk_ge5
    calc
      2 + 3 * k ≤ k + 3 * k := Nat.add_le_add_right h2_le_k _
      _ = 4 * k := by ring_nf
      _ ≤ k * k := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left k h4_le_k
  have h_sqrt_le : Real.sqrt (q : ℝ) ≤ k := by
    refine (Real.sqrt_le_iff).2 ?_
    refine ⟨?_, ?_⟩
    · exact_mod_cast (Nat.zero_le k)
    · have : (q : ℝ) ≤ (k : ℝ) * k := by
        exact_mod_cast (hq_le_2plus3k.trans h2plus3k_le_kk)
      simpa [pow_two] using this
  have : Nat.ceil (Real.sqrt (q : ℝ)) ≤ k := Nat.ceil_le.2 h_sqrt_le
  simpa [hk] using this

lemma riemann_hypothesis_stepanov_bound
  (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q : ℕ) (a : F)
  (hq : q = Fintype.card F)
  (hm3 : 3 ≤ f.natDegree)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (hq6m : q > 6 * f.natDegree)
  [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) a)] :
  (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
    < (q : ℝ) / 2 + 2 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  set m : ℕ := f.natDegree with hm_def
  have h18_lt_q : 18 < q := by
    have : 18 ≤ 6 * m := by
      have : 3 ≤ m := by simpa [hm_def] using hm3
      have := Nat.mul_le_mul_left 6 this
      simpa using this
    exact lt_of_le_of_lt this (by simpa [hm_def] using hq6m)
  have h15_le_q : (15 : ℕ) ≤ q :=
    le_trans (by decide : (15 : ℕ) ≤ 19) (Nat.succ_le_of_lt h18_lt_q)
  have hq_pos_nat : 0 < q := lt_trans (by decide : 0 < 18) h18_lt_q
  set ℓ : ℕ := Nat.ceil (Real.sqrt q) with hℓ_def
  have hℓ_le_q_div3 : ℓ ≤ q / 3 := by
    simpa [ℓ, hℓ_def] using ceil_sqrt_le_div_three q h15_le_q
  have h_sqrt_le_ℓ : Real.sqrt q ≤ (ℓ : ℝ) := by
    have hceil : Real.sqrt q ≤ (Nat.ceil (Real.sqrt q) : ℝ) :=
      Nat.le_ceil (Real.sqrt q)
    simpa [ℓ, hℓ_def] using hceil
  have hℓ_pos_real : 0 < (ℓ : ℝ) :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hq_pos_nat)) h_sqrt_le_ℓ
  have hℓ_pos : 0 < ℓ := by exact_mod_cast hℓ_pos_real
  obtain ⟨R, hR_ne, hdegR, hvan⟩ :=
    stepanov_polynomial (F := F) (hF := hF) (f := f) (q := q) (ℓ := ℓ) (a := a)
      hq hm3 hnsq hq6m hℓ_pos hℓ_le_q_div3
  set Sfin : Finset F :=
    Finset.univ.filter (fun x : F => x ∈ S_a F f ((q - 1) / 2) a) with hSfin_def
  have hvan_S : ∀ x ∈ Sfin, ∀ k < ℓ, (hasseDerivOp F k R).eval x = 0 := by
    intro x hx k hk
    rcases Finset.mem_filter.mp hx with ⟨_, hx_sa⟩
    exact hvan x hx_sa k hk
  have h_card_Sfin_le :
      (Sfin.card : ℝ) ≤ (R.natDegree : ℝ) / (ℓ : ℝ) :=
    hasse_vanishing_card_bound (F := F) (r := R) (ℓ := ℓ) (S := Sfin)
      hR_ne hℓ_pos hvan_S
  have h_card_subtype_eq :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        = (Sfin.card : ℝ) := by
    exact_mod_cast (by
      simp [Sfin] :
        Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} = Sfin.card)
  have h_card_le :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        ≤ (R.natDegree : ℝ) / (ℓ : ℝ) := by
    simpa [h_card_subtype_eq] using h_card_Sfin_le
  have hdegR' :
      (R.natDegree : ℝ)
        < (m : ℝ) * (q : ℝ)
          + (ℓ : ℝ) * (q : ℝ) / 2
          + (ℓ : ℝ) ^ 2 * (m : ℝ) := by
    have hfdeg : f.natDegree = m := by simp [hm_def]
    have h1 : ((f.natDegree * q : ℕ) : ℝ) = (m : ℝ) * (q : ℝ) := by
      simp [hfdeg, Nat.cast_mul, mul_comm]
    have h2 : ((ℓ * q : ℕ) : ℝ) = (ℓ : ℝ) * (q : ℝ) := by
      simp [Nat.cast_mul, mul_comm]
    have h3 : ((ℓ * ℓ * f.natDegree : ℕ) : ℝ)
        = (ℓ : ℝ) ^ 2 * (m : ℝ) := by
      simp [hfdeg, Nat.cast_mul, pow_two, mul_comm]
    simpa [h1, h2, h3] using hdegR
  have hq_le_ℓsq : (q : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
    have h_sq_le :
        Real.sqrt q * Real.sqrt q ≤ (ℓ : ℝ) * (ℓ : ℝ) :=
      mul_self_le_mul_self (a := Real.sqrt q) (b := (ℓ : ℝ))
        (Real.sqrt_nonneg _) h_sqrt_le_ℓ
    have hsq_eq : Real.sqrt q * Real.sqrt q = (q : ℝ) := by simp
    simpa [hsq_eq, pow_two] using h_sq_le
  have h_mq_le_mℓsq :
      (m : ℝ) * (q : ℝ)
        ≤ (m : ℝ) * (ℓ : ℝ) ^ 2 := by
    have :=
      mul_le_mul_of_nonneg_left hq_le_ℓsq
        (by exact_mod_cast (Nat.zero_le m) : 0 ≤ (m : ℝ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hdegR_upper :
      (R.natDegree : ℝ)
        < (ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
    have h1 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ) :=
      by linarith
    have h2 :
        (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ)
          = 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      calc
        (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ)
            = (m : ℝ) * (ℓ : ℝ) ^ 2 + (m : ℝ) * (ℓ : ℝ) ^ 2 := by
              simp [mul_comm]
        _ = 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by ring
    have h3 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      simpa [h2] using h1
    have h4 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) * (q : ℝ) / 2
          + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ (ℓ : ℝ) * (q : ℝ) / 2
            + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      have := add_le_add_left h3 ((ℓ : ℝ) * (q : ℝ) / 2)
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact lt_of_lt_of_le hdegR' h4
  have hdeg_div_main :
      (R.natDegree : ℝ) / (ℓ : ℝ)
        < (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
    have hdeg_div :
        (R.natDegree : ℝ) / (ℓ : ℝ)
          < ((ℓ : ℝ) * (q : ℝ) / 2
              + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ) := by
      have := mul_lt_mul_of_pos_right hdegR_upper (inv_pos.mpr hℓ_pos_real)
      simpa [div_eq_mul_inv] using this
    have h_upper_simpl :
        ((ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
          = (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
      have hneq : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos_real
      calc
        ((ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
            = (ℓ : ℝ) * (q : ℝ) / 2 / (ℓ : ℝ)
                + (2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ) := by
                  field_simp [add_comm, add_left_comm, add_assoc]
        _ = (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
          have h1 : (ℓ : ℝ) * (q : ℝ) / 2 / (ℓ : ℝ) = (q : ℝ) / 2 := by
            field_simp [hneq, mul_comm, mul_left_comm, mul_assoc]
          have h2 : (2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
              = 2 * (m : ℝ) * (ℓ : ℝ) := by
            field_simp [hneq, pow_two, mul_comm, mul_left_comm, mul_assoc]
          simp [h1, h2]
    simpa [h_upper_simpl] using hdeg_div
  have :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        < (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) :=
    lt_of_le_of_lt h_card_le hdeg_div_main
  simpa [m, hm_def, ℓ, hℓ_def] using this

lemma riemann_hypothesis_upper_bound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      < (q : ℝ) + 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  classical
  set c := (q - 1) / 2 with hc_def
  set m := f.natDegree with hm_def
  have h_stepanov := riemann_hypothesis_stepanov_bound F hF f q 1 hq hm3 hnsq hq6m
  let curveSet := {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f}
  let S1_set := {x : F // x ∈ S_a F f c 1}
  have h_two_S1_bound :
      2 * (Fintype.card S1_set : ℝ) <
        (q : ℝ) + 4 * (m : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
    simp [hm_def, hc_def, S1_set] at h_stepanov ⊢
    linarith [h_stepanov]
  have h_N_le_2S1 : (Fintype.card curveSet : ℝ) ≤ 2 * (Fintype.card S1_set : ℝ) := by
    have h_proj : ∀ p : curveSet, (p.val.1 : F) ∈ S_a F f c 1 := by
      intro ⟨⟨x, y⟩, hp⟩
      simp [S_a]
      by_cases hfx : Polynomial.eval x f = 0
      · left; exact hfx
      · right
        have hfx_sq : IsSquare (Polynomial.eval x f) :=
          ⟨y, by ring_nf; simpa using hp.symm⟩
        have hfx_ne : Polynomial.eval x f ≠ 0 := hfx
        rw [FiniteField.isSquare_iff hodd hfx_ne] at hfx_sq
        have hcard_eq : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
          have hcard_pos : 0 < Fintype.card F := Fintype.card_pos
          have : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hodd
          omega
        rw [hcard_eq] at hfx_sq
        simpa [hc_def, hq] using hfx_sq
    let proj : curveSet → S1_set := fun p => ⟨p.val.1, h_proj p⟩
    have h_count : Fintype.card curveSet ≤ 2 * Fintype.card S1_set := by
      have h_sigma : Fintype.card curveSet =
          Fintype.card ((y : S1_set) × {x : curveSet // proj x = y}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv proj).symm
      rw [h_sigma, Fintype.card_sigma]
      have h_fiber_le : ∀ y : S1_set, Fintype.card {x : curveSet // proj x = y} ≤ 2 := by
        intro ⟨x, hx⟩
        have h_card_sq_roots : Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f} ≤ 2 := by
          by_cases h0 : Polynomial.eval x f = 0
          · have h_unique : {y' : F // y' ^ 2 = Polynomial.eval x f} ≃ {y' : F // y' = 0} := by
              refine Equiv.subtypeEquiv (Equiv.refl F) ?_
              intro y'
              simp only [Equiv.refl_apply, h0, sq_eq_zero_iff]
            rw [Fintype.card_congr h_unique, Fintype.card_unique]
            norm_num
          · let p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (Polynomial.eval x f)
            have hp_ne : p ≠ 0 := by
              simp only [p, ne_eq, sub_eq_zero]
              intro h_eq
              have h_deg1 : (Polynomial.X ^ 2 : Polynomial F).natDegree = 2 :=
                Polynomial.natDegree_X_pow 2
              have h_deg2 : (Polynomial.C (Polynomial.eval x f) : Polynomial F).natDegree = 0 :=
                Polynomial.natDegree_C _
              have : (2 : ℕ) = 0 := by rw [← h_deg1, h_eq, h_deg2]
              norm_num at this
            have h_deg : p.natDegree ≤ 2 := by
              simp only [p]
              calc (Polynomial.X ^ 2 - Polynomial.C (Polynomial.eval x f)).natDegree
                  ≤ max (Polynomial.X ^ 2 : Polynomial F).natDegree
                      (Polynomial.C (Polynomial.eval x f)).natDegree :=
                    Polynomial.natDegree_sub_le _ _
                _ = max 2 0 := by simp [Polynomial.natDegree_C]
                _ = 2 := by norm_num
            have h_roots : ∀ y' : F, p.IsRoot y' ↔ y' ^ 2 = Polynomial.eval x f := by
              intro y'
              simp only [p, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
                Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
            have h_card_roots : Multiset.card p.roots ≤ p.natDegree := Polynomial.card_roots' p
            have h_inj : Function.Injective (fun (y' : {y' : F // y' ^ 2 = Polynomial.eval x f}) =>
                (⟨y'.val, (Polynomial.mem_roots hp_ne).mpr ((h_roots y'.val).mpr y'.property)⟩ :
                  {y' : F // y' ∈ p.roots})) := by
              intro ⟨a, ha⟩ ⟨b, hb⟩ h
              simp only [Subtype.mk.injEq] at h
              exact Subtype.ext h
            have h_card_le_roots : Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f} ≤
                Fintype.card {y' : F // y' ∈ p.roots} := Fintype.card_le_of_injective _ h_inj
            have h_fintype_le_multiset :
                Fintype.card {y' : F // y' ∈ p.roots} ≤ Multiset.card p.roots := by
              calc Fintype.card {y' : F // y' ∈ p.roots}
                  ≤ Fintype.card p.roots.toFinset := by
                    refine Fintype.card_le_of_injective
                      (fun ⟨y', hy'⟩ => ⟨y', Multiset.mem_toFinset.mpr hy'⟩) ?_
                    intro ⟨a, ha⟩ ⟨b, hb⟩ h
                    simp only [Subtype.mk.injEq] at h
                    exact Subtype.ext h
                _ = p.roots.toFinset.card := Fintype.card_coe p.roots.toFinset
                _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le p.roots
            calc Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f}
                ≤ Fintype.card {y' : F // y' ∈ p.roots} := h_card_le_roots
              _ ≤ Multiset.card p.roots := h_fintype_le_multiset
              _ ≤ p.natDegree := h_card_roots
              _ ≤ 2 := h_deg
        have h_fiber_inj : Function.Injective (fun (p' : {p' : curveSet // proj p' = ⟨x, hx⟩}) =>
            (⟨p'.val.val.2, by
              have hp := p'.val.property
              have hpx : proj p'.val = ⟨x, hx⟩ := p'.property
              simp only [proj] at hpx
              have hx_eq : p'.val.val.1 = x := Subtype.ext_iff.mp hpx
              simp only [hx_eq] at hp
              exact hp⟩ : {y' : F // y' ^ 2 = Polynomial.eval x f})) := by
          intro ⟨⟨⟨x1, y1⟩, hp1⟩, hproj1⟩ ⟨⟨⟨x2, y2⟩, hp2⟩, hproj2⟩ h
          simp only [Subtype.mk.injEq] at h
          simp only [proj] at hproj1 hproj2
          have hx1_eq : x1 = x := Subtype.ext_iff.mp hproj1
          have hx2_eq : x2 = x := Subtype.ext_iff.mp hproj2
          simp only [Subtype.mk.injEq]
          refine Subtype.ext ?_
          simp only [Prod.mk.injEq]
          exact ⟨hx1_eq.trans hx2_eq.symm, h⟩
        exact le_trans (Fintype.card_le_of_injective _ h_fiber_inj) h_card_sq_roots
      calc ∑ y : S1_set, Fintype.card {x : curveSet // proj x = y}
          ≤ ∑ _ : S1_set, 2 := Finset.sum_le_sum (fun y _ => h_fiber_le y)
        _ = 2 * Fintype.card S1_set := by simp [Finset.sum_const, Finset.card_univ]; ring
    exact_mod_cast h_count
  have h := lt_of_le_of_lt h_N_le_2S1 h_two_S1_bound
  simpa [curveSet, S1_set, hc_def, hm_def] using h

lemma curve_count_ge_two_times_N1
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      ≥
        2 *
          (Fintype.card
              {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
                Polynomial.eval x f ≠ 0} : ℝ) :=
by
  classical
  subst hq
  set c := (Fintype.card F - 1) / 2 with hc_def
  let N1 := {x : F // (Polynomial.eval x f) ^ c = 1 ∧ Polynomial.eval x f ≠ 0}
  let C := {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f}
  let C_from_N1 :=
    {p : C // p.val.1 ∈ {x : F | (Polynomial.eval x f) ^ c = 1 ∧ Polynomial.eval x f ≠ 0}}
  have h1 : Fintype.card C ≥ Fintype.card C_from_N1 :=
    Fintype.card_le_of_embedding (Function.Embedding.subtype _)
  have hcard_div : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    have _ := FiniteField.odd_card_of_char_ne_two hodd
    have _ : 0 < Fintype.card F := Fintype.card_pos
    omega
  have h2 : Fintype.card C_from_N1 = 2 * Fintype.card N1 := by
    let proj : C_from_N1 → N1 := fun ⟨⟨⟨x, y⟩, hp⟩, hx⟩ => ⟨x, hx⟩
    have h_fiber_card : ∀ x : N1, Fintype.card {p : C_from_N1 // proj p = x} = 2 := by
      intro ⟨x, ⟨hxc, hx_ne⟩⟩
      have hfx_ne : Polynomial.eval x f ≠ 0 := hx_ne
      have h_euler := FiniteField.isSquare_iff hodd hfx_ne
      rw [hcard_div] at h_euler
      have hfx_sq : IsSquare (Polynomial.eval x f) := h_euler.mpr hxc
      obtain ⟨r, hr⟩ := hfx_sq.exists_mul_self
      have hr' : r ^ 2 = Polynomial.eval x f := by rw [sq]; exact hr.symm
      have hr_ne : r ≠ 0 := by
        intro h; rw [h, sq, mul_zero] at hr'; exact hfx_ne hr'.symm
      have h_roots : ∀ y : F, y ^ 2 = Polynomial.eval x f ↔ y = r ∨ y = -r := by
        intro y
        constructor
        · intro hy
          have : y ^ 2 = r ^ 2 := by
            simpa [hr'.symm] using hy
          rw [sq_eq_sq_iff_eq_or_eq_neg] at this
          exact this
        · intro h_or
          cases h_or with
          | inl h => rw [h, hr']
          | inr h => rw [h, neg_sq, hr']
      have hr_ne_neg : r ≠ -r := by
        intro h
        have h2r : r + r = 0 := by
          have : r - (-r) = 0 := sub_eq_zero.mpr h
          simp only [sub_neg_eq_add] at this
          exact this
        have h2_times_r : (2 : F) * r = 0 := by rw [two_mul]; exact h2r
        rw [mul_eq_zero] at h2_times_r
        cases h2_times_r with
        | inl h2 =>
          have := CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_two h2
          exact hodd this
        | inr h0 => exact hr_ne h0
      have h_sq_roots : Fintype.card {y : F // y ^ 2 = Polynomial.eval x f} = 2 := by
        have h_equiv : {y : F // y ^ 2 = Polynomial.eval x f} ≃ ({r, -r} : Finset F) := by
          refine {
            toFun := fun ⟨y, hy⟩ => by
              have hy_or := (h_roots y).mp hy
              refine ⟨y, ?_⟩
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact hy_or
            invFun := fun ⟨y, hy⟩ => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              refine ⟨y, (h_roots y).mpr hy⟩
            left_inv := fun ⟨y, hy⟩ => by simp
            right_inv := fun ⟨y, hy⟩ => by simp
          }
        rw [Fintype.card_congr h_equiv]
        have : ({r, -r} : Finset F).card = 2 := by
          rw [Finset.card_insert_of_notMem, Finset.card_singleton]
          simp only [Finset.mem_singleton]
          exact hr_ne_neg
        simp only [Fintype.card_coe]
        exact this
      have h_fiber_equiv : {p : C_from_N1 // proj p = ⟨x, ⟨hxc, hx_ne⟩⟩} ≃
          {y : F // y ^ 2 = Polynomial.eval x f} := by
        refine {
          toFun := fun ⟨⟨⟨⟨x', y⟩, hp⟩, hx'⟩, hproj⟩ => by
            simp only [proj] at hproj
            have hx'_eq : x' = x := Subtype.ext_iff.mp hproj
            exact ⟨y, by simp only [← hx'_eq]; exact hp⟩
          invFun := fun ⟨y, hy⟩ => by
            refine ⟨⟨⟨⟨x, y⟩, hy⟩, ?_⟩, rfl⟩
            simp only [Set.mem_setOf_eq]
            exact ⟨hxc, hx_ne⟩
          left_inv := by
            intro ⟨⟨⟨⟨x', y⟩, hp⟩, hx'⟩, hproj⟩
            simp only [proj] at hproj
            have hx'_eq : x' = x := Subtype.ext_iff.mp hproj
            simp only [Subtype.mk.injEq]
            subst hx'_eq
            rfl
          right_inv := fun ⟨y, hy⟩ => rfl
        }
      rw [Fintype.card_congr h_fiber_equiv, h_sq_roots]
    calc
      Fintype.card C_from_N1
          = Fintype.card ((x : N1) × {p : C_from_N1 // proj p = x}) := by
            exact Fintype.card_congr (Equiv.sigmaFiberEquiv proj).symm
      _ = ∑ x : N1, Fintype.card {p : C_from_N1 // proj p = x} := Fintype.card_sigma
      _ = ∑ _x : N1, 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact h_fiber_card x
      _ = 2 * Fintype.card N1 := by
          simp [Finset.sum_const, Finset.card_univ, mul_comm]
  have h3 : (Fintype.card C : ℝ) ≥ 2 * (Fintype.card N1 : ℝ) := by
    have h3' : (Fintype.card C : ℝ) ≥ (Fintype.card C_from_N1 : ℝ) := by exact_mod_cast h1
    simpa [h2, Nat.cast_mul] using h3'
  simpa [C, N1, hc_def] using h3

lemma partition_N1_eq_q_sub_S_neg1
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hodd : ringChar F ≠ 2)
    [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) (-1))] :
    (Fintype.card
        {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
          Polynomial.eval x f ≠ 0} : ℝ)
      = (q : ℝ) -
        (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) (-1)} : ℝ) :=
by
  subst hq
  set c := (Fintype.card F - 1) / 2 with hc_def
  have hcard_div : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    have _ := FiniteField.odd_card_of_char_ne_two hodd
    have _ : 0 < Fintype.card F := Fintype.card_pos
    omega
  have h1_ne_neg1 : (1 : F) ≠ -1 := by
    intro h
    have h2 : (2 : F) = 0 := by
      calc
        (2 : F) = 1 - (-1) := by ring
        _ = 1 - 1 := by rw [← h]
        _ = 0 := by ring
    exact hodd (CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_two h2)
  let N1 :=
    Finset.univ.filter (fun x : F => (Polynomial.eval x f) ^ c = 1 ∧
      Polynomial.eval x f ≠ 0)
  let Sn1 := Finset.univ.filter (fun x : F => x ∈ S_a F f c (-1))
  have h_compl : N1 = Sn1ᶜ := by
    ext x
    simp only [N1, Sn1, S_a, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl, Set.mem_setOf_eq, not_or]
    constructor
    · rintro ⟨h1, hne⟩
      refine ⟨hne, ?_⟩
      intro hm1
      exact h1_ne_neg1 (h1.symm.trans hm1)
    · intro h
      have h' : Polynomial.eval x f ≠ 0 ∧
          (Polynomial.eval x f) ^ c ≠ -1 := by
        simpa [not_or] using h
      have h_euler := FiniteField.pow_dichotomy hodd h'.1
      rw [hcard_div] at h_euler
      rcases h_euler with h1 | hm1'
      · exact ⟨h1, h'.1⟩
      · exact (h'.2 hm1').elim
  have hN1_card_real :
      (N1.card : ℝ) = (Fintype.card F : ℝ) - (Sn1.card : ℝ) := by
    have hN1_card : N1.card = Fintype.card F - Sn1.card := by
      simp [h_compl, Finset.card_compl]
    have hSn1_le : Sn1.card ≤ Fintype.card F :=
      Finset.card_le_card (Finset.subset_univ _)
    simp [hN1_card, Nat.cast_sub hSn1_le]
  have h_N1_eq :
      Fintype.card {x : F // (Polynomial.eval x f) ^ c = 1 ∧
        Polynomial.eval x f ≠ 0} = N1.card :=
    Fintype.card_subtype _
  have h_S_eq :
      Fintype.card {x : F // x ∈ S_a F f c (-1)} = Sn1.card :=
    Fintype.card_subtype _
  simp only [hc_def] at h_N1_eq h_S_eq
  convert
      (by
        simp only [h_N1_eq, h_S_eq, hN1_card_real] :
          (Fintype.card {x : F // (Polynomial.eval x f) ^
              ((Fintype.card F - 1) / 2) = 1 ∧
              Polynomial.eval x f ≠ 0} : ℝ) =
            (Fintype.card F : ℝ) -
              (Fintype.card {x : F // x ∈ S_a F f
                ((Fintype.card F - 1) / 2) (-1)} : ℝ)) using 4

lemma riemann_hypothesis_lower_bound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      > (q : ℝ) - 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  classical
  linarith [ curve_count_ge_two_times_N1 F f q hq hodd,
            partition_N1_eq_q_sub_S_neg1 F f q hq hodd,
            riemann_hypothesis_stepanov_bound F hF f q (-1) hq hm3 hnsq hq6m ]

theorem riemann_hypothesis_hec
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) :
    |((q : ℝ) - (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ))|
      < (5 : ℝ) * (f.natDegree : ℝ) * Real.sqrt (q : ℝ) :=
by
  have hm_pos : (0 : ℝ) < (f.natDegree : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num) hm3)
  have hq_pos : (0 : ℝ) < (q : ℝ) :=
    Nat.cast_pos.mpr
      (Nat.lt_trans (Nat.mul_pos (by norm_num)
        (Nat.lt_of_lt_of_le (by norm_num) hm3)) hq6m)
  by_cases hchar2 : ringChar F = 2
  · have hN_eq_q :
        Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} = q := by
      haveI : CharP F 2 := hchar2 ▸ ringChar.charP F
      haveI : ExpChar F 2 := .prime Nat.prime_two
      let frob := frobeniusEquiv F 2
      simpa [hq] using
        (Fintype.card_congr {
          toFun := fun ⟨⟨x, _⟩, _⟩ => x
          invFun := fun x => ⟨(x, frob.symm (Polynomial.eval x f)), frob.apply_symm_apply _⟩
          left_inv := fun ⟨⟨_, _⟩, hy⟩ =>
            Subtype.ext (Prod.ext rfl (frob.injective
              (by
                simp only [frobeniusEquiv_def, hy, frob,
                  RingEquiv.apply_symm_apply])))
          right_inv := fun _ => rfl
        })
    simp [hN_eq_q, sub_self, abs_zero]
    positivity
  · set N : ℝ :=
      (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
    have h_abs :
        |(q : ℝ) - N| <
          4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
      have h_upper :=
        riemann_hypothesis_upper_bound F hchar2 f q hq hm3 hnsq hq6m hchar2
      have h_lower :=
        riemann_hypothesis_lower_bound F hchar2 f q hq hm3 hnsq hq6m hchar2
      rw [abs_sub_lt_iff]; constructor <;> linarith
    have h_ceil_bound : (Nat.ceil (Real.sqrt q) : ℝ) ≤ Real.sqrt q + 1 := by
      have := Nat.ceil_lt_add_one (Real.sqrt_nonneg q)
      linarith
    have h_q_ge_18 : (18 : ℕ) ≤ q := by
      have : 6 * 3 ≤ 6 * f.natDegree := Nat.mul_le_mul_left 6 hm3
      omega
    have h_sqrt_gt_4 : (4 : ℝ) < Real.sqrt q := by
      rw [show (4 : ℝ) = Real.sqrt 16 by
        simpa only [show (4 : ℝ) ^ 2 = 16 by norm_num] using
          (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)).symm]
      apply Real.sqrt_lt_sqrt (by norm_num)
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 16 < 18) h_q_ge_18
    calc
      |(q : ℝ) - N| <
          4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := h_abs
      _ ≤ 4 * (f.natDegree : ℝ) * (Real.sqrt q + 1) := by
        nlinarith [h_ceil_bound]
      _ = 4 * (f.natDegree : ℝ) * Real.sqrt q +
            4 * (f.natDegree : ℝ) := by ring
      _ < 4 * (f.natDegree : ℝ) * Real.sqrt q +
            (f.natDegree : ℝ) * Real.sqrt q := by
        nlinarith [hm_pos, h_sqrt_gt_4]
      _ = 5 * (f.natDegree : ℝ) * Real.sqrt q := by ring

#print axioms riemann_hypothesis_hec

#print axioms riemann_hypothesis_hec


end Update150_Component_5
/- END COMPONENT: OtherInputsHECFlat.lean -/

/- BEGIN COMPONENT: Erdos374_CurveInput149.lean -/
section Update150_Component_6



/-!
Adapter from the proved Math Inc. curve estimate to the precise finite-field
input retained by the candidate proof. No analytic premise is added here.
-/

namespace Erdos374.ExternalInputs149

open RemainingAnalytic115.RemainingAnalytic141

theorem coarseHyperellipticCount : CoarseHyperellipticCount141 := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro f hdeg hnsq hsize
  exact riemann_hypothesis_hec (ZMod p) f p (ZMod.card p).symm hdeg hnsq hsize

end Erdos374.ExternalInputs149

#print axioms Erdos374.ExternalInputs149.coarseHyperellipticCount


end Update150_Component_6
/- END COMPONENT: Erdos374_CurveInput149.lean -/

/- BEGIN COMPONENT: Erdos374_AnalyticClosure150.lean -/
section Update150_Component_7




/-!
Update 150: discharge quantitative PNT and the coarse finite-field curve input
using source proofs rebuilt with the same Lean and Mathlib versions.

The candidate's MainStatement is unchanged. This is STILL CONDITIONAL:
Harman's almost-all short-interval input and polynomial-range reciprocal-prime
sampling are explicit, unconstructed arguments of the final theorems.
-/

namespace Erdos374.AnalyticClosure150

open RemainingAnalytic115.RemainingAnalytic127
open RemainingAnalytic115.RemainingAnalytic134
open RemainingAnalytic115.RemainingAnalytic141
open SamplingPolynomial149

/-- Closed quantitative PNT input, from the rebuilt PNT+ proof. -/
theorem pntInput : PsiMediumPNT134 := ExternalInputs149.psiMediumPNT

/-- Closed curve-count input, from the rebuilt finite-field proof. -/
theorem curveInput : CoarseHyperellipticCount141 :=
  ExternalInputs149.coarseHyperellipticCount

/-- The weaker theta remainder is also closed. -/
theorem thetaInput : ThetaLogSqRemainder127 :=
  thetaLogSqRemainder_from_mediumPNT134 pntInput

/-- Exactly two analytic inputs remain, both visible in the theorem's type. -/
theorem candidate_main150
    (HF : DensityZero forwardBadIntervals141)
    (HS : PolynomialReciprocalPrimeSampling) : MainStatement :=
  candidate_main_from_polynomial_sampling149 pntInput curveInput HF HS

theorem positive_lower_density150
    (HF : DensityZero forwardBadIntervals141)
    (HS : PolynomialReciprocalPrimeSampling) : PositiveLowerDensity D6 :=
  positive_lower_density_from_polynomial_sampling149 pntInput curveInput HF HS

/-- Compatibility with the previous stronger sampling interface. -/
theorem candidate_main_from_original_sampling150
    (HF : DensityZero forwardBadIntervals141)
    (HS : SamplingClosure147.ReciprocalPrimeSampling) : MainStatement :=
  candidate_main150 HF (polynomial_sampling_of_sampling HS)

#print axioms pntInput
#print axioms curveInput
#print axioms thetaInput
#print axioms candidate_main150
#print axioms positive_lower_density150
#check candidate_main150
#check positive_lower_density150

run_cmd do
  let targets : List Lean.Name := [
    ``pntInput, ``curveInput, ``thetaInput,
    ``candidate_main150, ``positive_lower_density150,
    ``candidate_main_from_original_sampling150]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#eval "UPDATE 150: PNT and curves constructed; Harman and prime sampling remain premises"

end Erdos374.AnalyticClosure150


end Update150_Component_7
/- END COMPONENT: Erdos374_AnalyticClosure150.lean -/

/- BEGIN COMPONENT: SamplerConstantClosed150.lean -/
section Update150_Component_8



/-! Kernel-closed constant-test consequences of the imported quantitative PNT.
Nonconstant reciprocal-prime sampling remains a separate open input. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Erdos374.SamplerConstantClosed150
open RemainingAnalytic115.RemainingAnalytic141
open SamplingClosure147 UniformC3_147

theorem theta_logPower_real (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| * (Real.log x) ^ k ≤ ε * x := by
  obtain ⟨c, hc, hPNT⟩ := ExternalInputs149.psiMediumPNT
  obtain ⟨C, hC, hbound⟩ := Asymptotics.isBigO_iff'.mp hPNT
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
  exact hreal

lemma inv_log_pow_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ k) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  have hpow0 : (Real.log t) ^ k ≠ 0 := pow_ne_zero k hl0
  exact ContinuousAt.continuousWithinAt (by fun_prop)

lemma theta_kernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * (Real.log t) ^ 2)) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set
    (Set.Icc_subset_Icc ha le_rfl)

lemma integral_inv_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / Real.log t) =
      b / Real.log b - a / Real.log a + ∫ t in a..b, 1 / (Real.log t) ^ 2 := by
  have h1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b := by
    simpa using inv_log_pow_integrable ha hab 1
  have h2 := inv_log_pow_integrable ha hab 2
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ => x / Real.log x)
      (1 / Real.log t - 1 / (Real.log t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have ht0 : t ≠ 0 := by linarith
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    convert (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hl0 using 1
    · rfl
    · simp only [id_eq]
      field_simp <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (h1.sub h2)
  rw [intervalIntegral.integral_sub h1 h2] at hi
  linarith

/-- Exact Abel-summation identity for the prime-count discrepancy on a real band. -/
theorem primeCount_discrepancy_eq {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (Nat.primeCounting ⌊b⌋₊ : ℝ) - (Nat.primeCounting ⌊a⌋₊ : ℝ) -
        (∫ t in a..b, 1 / Real.log t) =
      (Chebyshev.theta b - b) / Real.log b -
        (Chebyshev.theta a - a) / Real.log a +
      ∫ t in a..b,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2) := by
  have ha1 : 1 < a := by linarith
  have hTb := theta_kernel_integrable (le_refl (2 : ℝ)) (ha.trans hab)
  have hTa := theta_kernel_integrable (le_refl (2 : ℝ)) ha
  have hTab := theta_kernel_integrable ha hab
  have hi := intervalIntegral.integral_add_adjacent_intervals hTa hTab
  have hpa := Chebyshev.primeCounting_eq_theta_div_log_add_integral ha
  have hpb := Chebyshev.primeCounting_eq_theta_div_log_add_integral (ha.trans hab)
  rw [hpb, hpa, integral_inv_log ha1 hab,
    intervalIntegral.integral_sub hTab (inv_log_pow_integrable ha1 hab 2)]
  simp only [sub_div]
  linarith

/-- A finite estimate, with the theta errors supplied throughout one dyadic band. -/
theorem dyadic_discrepancy_bound {a : ℝ} (ha : 2 ≤ a) (hLa : 1 ≤ Real.log a)
    (hθ : ∀ t ∈ Set.Icc a (2 * a),
      |Chebyshev.theta t - t| * (Real.log t) ^ 6 ≤ t) :
    |(Nat.primeCounting ⌊2 * a⌋₊ : ℝ) - (Nat.primeCounting ⌊a⌋₊ : ℝ) -
      ∫ t in a..(2 * a), 1 / Real.log t| ≤ 4 * a / (Real.log a) ^ 6 := by
  have ha0 : 0 < a := by linarith
  have hab : a ≤ 2 * a := by linarith
  have hL0 : 0 < Real.log a := by linarith
  have hp0 : 0 < (Real.log a) ^ 6 := pow_pos hL0 6
  have herr : ∀ t ∈ Set.Icc a (2 * a),
      |Chebyshev.theta t - t| ≤ t / (Real.log a) ^ 6 := by
    intro t ht
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha0 ht.1
    apply (le_div_iff₀ hp0).mpr
    exact le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hL0.le hlog 6) (abs_nonneg _)) (hθ t ht)
  have hend : ∀ t ∈ Set.Icc a (2 * a),
      |(Chebyshev.theta t - t) / Real.log t| ≤ t / (Real.log a) ^ 6 := by
    intro t ht
    have hlog : 1 ≤ Real.log t := hLa.trans (Real.log_le_log ha0 ht.1)
    rw [abs_div, abs_of_pos (show 0 < Real.log t by linarith)]
    exact (div_le_self (abs_nonneg _) hlog).trans (herr t ht)
  have hk : ∀ t ∈ Set.Icc a (2 * a),
      |Chebyshev.theta t / (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2| ≤
        1 / (Real.log a) ^ 6 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have hlog : 1 ≤ Real.log t := hLa.trans (Real.log_le_log ha0 ht.1)
    have hlog0 : 0 < Real.log t := by linarith
    have hlog2 : 1 ≤ (Real.log t) ^ 2 := by nlinarith
    have heq : Chebyshev.theta t / (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2 =
        (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2) := by
      field_simp <;> ring
    rw [heq, abs_div, abs_of_pos (show 0 < t * (Real.log t) ^ 2 by positivity)]
    calc
      _ ≤ (t / (Real.log a) ^ 6) / (t * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right (herr t ht) (by positivity)
      _ = (1 / (Real.log a) ^ 6) / (Real.log t) ^ 2 := by
        field_simp
      _ ≤ 1 / (Real.log a) ^ 6 := div_le_self (by positivity) hlog2
  have hInt := (theta_kernel_integrable ha hab).sub
    (inv_log_pow_integrable (by linarith : 1 < a) hab 2)
  have hi : |∫ t in a..(2 * a),
      (Chebyshev.theta t / (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2)| ≤
        a / (Real.log a) ^ 6 := by
    calc
      _ ≤ ∫ t in a..(2 * a),
          |Chebyshev.theta t / (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..(2 * a), 1 / (Real.log a) ^ 6 :=
        intervalIntegral.integral_mono_on hab hInt.abs intervalIntegrable_const hk
      _ = a / (Real.log a) ^ 6 := by rw [intervalIntegral.integral_const]; simp; ring
  rw [primeCount_discrepancy_eq ha hab]
  have hA := hend a ⟨le_rfl, hab⟩
  have hB := hend (2 * a) ⟨hab, le_rfl⟩
  have htri := abs_add_le
    ((Chebyshev.theta (2 * a) - 2 * a) / Real.log (2 * a) -
      (Chebyshev.theta a - a) / Real.log a)
    (∫ t in a..(2 * a),
      (Chebyshev.theta t / (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2))
  have hsub := abs_sub
    ((Chebyshev.theta (2 * a) - 2 * a) / Real.log (2 * a))
    ((Chebyshev.theta a - a) / Real.log a)
  calc
    _ ≤ _ := htri
    _ ≤ _ := add_le_add hsub le_rfl
    _ ≤ (2 * a / (Real.log a) ^ 6 + a / (Real.log a) ^ 6) +
        a / (Real.log a) ^ 6 := add_le_add (add_le_add hB hA) hi
    _ = _ := by ring

/-- The zero Fourier mode is closed using the proved quantitative PNT. -/
theorem dyadic_primeCount_unconditional :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P →
      |(Nat.primeCounting (2 * P) : ℝ) - (Nat.primeCounting P : ℝ) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), 1 / Real.log t| ≤
        4 * (P : ℝ) / (Real.log (P : ℝ)) ^ 6 := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (theta_logPower_real 6 1 (by norm_num))
  obtain ⟨N, hN⟩ := exists_nat_ge x₀
  obtain ⟨NL, hNL⟩ := RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127 1
  refine ⟨max 2 (max N NL), ?_⟩
  intro P hP
  have hP2 : 2 ≤ P := by omega
  have hPN : N ≤ P := by omega
  have hPL : NL ≤ P := by omega
  have hθ : ∀ t ∈ Set.Icc (P : ℝ) (2 * (P : ℝ)),
      |Chebyshev.theta t - t| * (Real.log t) ^ 6 ≤ t := by
    intro t ht
    have hx : x₀ ≤ t := hN.trans ((Nat.cast_le.mpr hPN).trans ht.1)
    simpa only [one_mul] using hx₀ t hx
  have h := dyadic_discrepancy_bound (by exact_mod_cast hP2) (hNL P hPL) hθ
  have hfloor : ⌊2 * (P : ℝ)⌋₊ = 2 * P := by
    rw [show 2 * (P : ℝ) = ((2 * P : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_natCast]
  simpa only [hfloor, Nat.floor_natCast] using h

/-- Uniform sampling for every constant real test function, with C = 4.
No analytic hypothesis is an argument of this theorem. -/
theorem constant_sampling_unconditional :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → ∀ a : ℝ,
      |(∑ p ∈ openPrimeBand P, a) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), a / Real.log t| ≤
        4 * c3Size (fun _ : ℝ × ℝ => a) * (P : ℝ) /
          (Real.log (P : ℝ)) ^ 6 := by
  obtain ⟨P₀, hP₀⟩ := dyadic_primeCount_unconditional
  refine ⟨P₀, ?_⟩
  intro P hP a
  have hid : (∑ p ∈ openPrimeBand P, a) -
      (∫ t in (P : ℝ)..(2 * (P : ℝ)), a / Real.log t) =
      a * ((Nat.primeCounting (2 * P) : ℝ) - (Nat.primeCounting P : ℝ) -
        ∫ t in (P : ℝ)..(2 * (P : ℝ)), 1 / Real.log t) := by
    rw [Finset.sum_const, nsmul_eq_mul, openPrimeBand_card_real]
    simp only [div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hid, abs_mul, c3Size_const]
  calc
    _ ≤ |a| * (4 * (P : ℝ) / (Real.log (P : ℝ)) ^ 6) :=
      mul_le_mul_of_nonneg_left (hP₀ P hP) (abs_nonneg a)
    _ = _ := by ring

#print axioms theta_logPower_real
#print axioms primeCount_discrepancy_eq
#print axioms dyadic_discrepancy_bound
#print axioms dyadic_primeCount_unconditional
#print axioms constant_sampling_unconditional
run_cmd do
  let targets : List Lean.Name := [
    ``theta_logPower_real,
    ``primeCount_discrepancy_eq,
    ``dyadic_discrepancy_bound,
    ``dyadic_primeCount_unconditional,
    ``constant_sampling_unconditional]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
end Erdos374.SamplerConstantClosed150
end



end Update150_Component_8
/- END COMPONENT: SamplerConstantClosed150.lean -/

/- BEGIN COMPONENT: HarmanBoundary150.lean -/
section Update150_Component_9


/-!
A measure-to-integer bridge for the remaining Harman input.

This file does not prove Harman's analytic exceptional-measure estimate.
It proves that its real-start formulation, with exponent 41/400, suffices
for Repair149's integer forward input at exponent 21/200. Only prime
existence is required; no asymptotic formula or second moment is assumed.
-/

noncomputable section
open MeasureTheory

namespace Erdos374.HarmanBoundary150

open RemainingAnalytic115.RemainingAnalytic141

def realForwardExponent150 : ℝ := 41 / 400

def realForwardBad150 : Set ℝ :=
  {x | ¬ ∃ p : ℕ, p.Prime ∧ x ≤ (p : ℝ) ∧
    (p : ℝ) ≤ x + x ^ realForwardExponent150}

/-- The continuous exceptional-measure theorem still to be formalized.
This asks only for a prime in almost every short interval. -/
def RealForwardExceptionalMeasure150 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ X : ℝ, Y ≤ X →
    volume.real (realForwardBad150 ∩ Set.Icc 1 X) < ε * X

/-- Bounded exceptional sets have finite outer measure, so `volume.real`
cannot hide an infinite measure by mapping it to zero. -/
theorem bounded_exception_measure_finite150 (X : ℝ) :
    volume (realForwardBad150 ∩ Set.Icc 1 X) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_right)

theorem exponent_ledger150 :
    (1 : ℝ) / 10 < realForwardExponent150 ∧
      realForwardExponent150 < harmanForwardExponent141 := by
  norm_num [realForwardExponent150, harmanForwardExponent141]

/-- Exponent slack absorbs the half-unit thickening of an integer start. -/
theorem halfUnit_scale150 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℝ,
      x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1 / 2) →
      x + x ^ realForwardExponent150 ≤
        (n : ℝ) + (n : ℝ) ^ harmanForwardExponent141 := by
  obtain ⟨N, hN⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := harmanForwardExponent141 - realForwardExponent150) (C := 4)
    (by norm_num [harmanForwardExponent141, realForwardExponent150])
  refine ⟨max N 1, ?_⟩
  intro n hn x hx
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_max_right N 1) hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hβ : 0 ≤ realForwardExponent150 := by norm_num [realForwardExponent150]
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ realForwardExponent150 :=
    Real.one_le_rpow hn1 hβ
  have hpow4 := hN n (le_trans (le_max_left N 1) hn)
  have hsplit : (n : ℝ) ^ harmanForwardExponent141 =
      (n : ℝ) ^ realForwardExponent150 *
        (n : ℝ) ^ (harmanForwardExponent141 - realForwardExponent150) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have h2 : (2 : ℝ) ^ realForwardExponent150 ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by norm_num [realForwardExponent150])
      _ = 2 := Real.rpow_one 2
  have hx0 : 0 ≤ x := le_trans hn0.le hx.1
  have hx2 : x ≤ 2 * (n : ℝ) := by linarith [hx.2]
  have hxpow := Real.rpow_le_rpow hx0 hx2 hβ
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le] at hxpow
  have hsmall : x ^ realForwardExponent150 ≤
      2 * (n : ℝ) ^ realForwardExponent150 := by
    nlinarith [Real.rpow_nonneg hn0.le realForwardExponent150]
  rw [hsplit]
  nlinarith [hx.2]

theorem halfUnit_bad150 {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → ∀ x : ℝ,
      x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1 / 2) →
      x + x ^ realForwardExponent150 ≤
        (n : ℝ) + (n : ℝ) ^ harmanForwardExponent141)
    {n : ℕ} (hn : N ≤ n) (hbad : n ∈ forwardBadIntervals141) :
    Set.Ico (n : ℝ) ((n : ℝ) + 1 / 2) ⊆ realForwardBad150 := by
  intro x hx hprime
  rcases hprime with ⟨p, hp, hxp, hpx⟩
  have hnp : n ≤ p := by exact_mod_cast le_trans hx.1 hxp
  apply hbad
  refine ⟨p, hp, hnp, ?_⟩
  rw [Nat.cast_sub hnp]
  linarith [hN n hn x hx]

/-- Disjoint half-unit intervals turn an exceptional-measure bound into a
count of exceptional integers. The exceptional set itself need not be measurable. -/
theorem halfUnit_count_le_measure150 (s : Finset ℕ) (E : Set ℝ) (X : ℝ)
    (hs : ∀ n ∈ s, 1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
    (hE : ∀ n ∈ s, Set.Ico (n : ℝ) ((n : ℝ) + 1 / 2) ⊆ E) :
    (s.card : ℝ) / 2 ≤ volume.real (E ∩ Set.Icc 1 (X + 1)) := by
  have hd : Set.PairwiseDisjoint (s : Set ℕ)
      (fun n => Set.Ico (n : ℝ) ((n : ℝ) + 1 / 2)) := by
    intro n _ m _ hnm
    apply Set.disjoint_left.mpr
    intro x hxn hxm
    rcases lt_or_gt_of_ne hnm with hnm | hmn
    · have hgap : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hnm
      linarith [hxn.2, hxm.1]
    · have hgap : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hmn
      linarith [hxm.2, hxn.1]
  have hvol : volume.real (⋃ n ∈ s,
      Set.Ico (n : ℝ) ((n : ℝ) + 1 / 2)) = (s.card : ℝ) / 2 := by
    rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_Ico)
      (fun _ _ => by simp)]
    simp [Real.volume_real_Ico, div_eq_mul_inv]
  rw [← hvol]
  apply measureReal_mono
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨hE n hn hxn, ?_, ?_⟩
    · exact le_trans (hs n hn).1 hxn.1
    · linarith [(hs n hn).2, hxn.2]
  · exact ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_right)

/-- A proved adapter from real-start exceptional measure at .1025 to the exact
integer-start density hypothesis at .105. The analytic premise remains explicit. -/
theorem forward_density_from_real_measure150
    (H : RealForwardExceptionalMeasure150) : DensityZero forwardBadIntervals141 := by
  classical
  obtain ⟨M, hM⟩ := halfUnit_scale150
  let S : Set ℕ := forwardBadIntervals141 ∩ Set.Ici M
  have hS : DensityZero S := by
    intro ε hε
    obtain ⟨Y, hY⟩ := H (ε / 4) (by linarith)
    obtain ⟨N, hN⟩ := exists_nat_ge Y
    refine ⟨max N 1, ?_⟩
    intro X hX
    have hXN : N ≤ X := le_trans (le_max_left N 1) hX
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right N 1) hX
    have hX0 : (0 : ℝ) < X := by linarith
    have hYX : Y ≤ (X : ℝ) + 1 := by
      have : (N : ℝ) ≤ X := by exact_mod_cast hXN
      linarith
    let s := (Finset.Icc 1 X).filter (fun n => n ∈ S)
    have hcard : prefixCount S X = s.card := by
      unfold prefixCount
      apply congrArg Finset.card
      ext n
      simp [s]
    have hs1 : ∀ n ∈ s, 1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ (X : ℝ) := by
      intro n hn
      have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      constructor
      · exact_mod_cast hnI.1
      · exact_mod_cast hnI.2
    have hsE : ∀ n ∈ s,
        Set.Ico (n : ℝ) ((n : ℝ) + 1 / 2) ⊆ realForwardBad150 := by
      intro n hn
      have hnS := (Finset.mem_filter.mp hn).2
      exact halfUnit_bad150 hM hnS.2 hnS.1
    have hbound : (prefixCount S X : ℝ) / 2 ≤
        volume.real (realForwardBad150 ∩ Set.Icc 1 ((X : ℝ) + 1)) := by
      rw [hcard]
      exact halfUnit_count_le_measure150 s realForwardBad150 (X : ℝ) hs1 hsE
    have hmeasure := hY ((X : ℝ) + 1) hYX
    rw [sub_zero, abs_of_nonneg (proportion_nonneg S X)]
    change (prefixCount S X : ℝ) / (X : ℝ) < ε
    apply (div_lt_iff₀ hX0).mpr
    nlinarith
  apply densityZero_mono (T := S ∪ Initial M) ?_
    (densityZero_union hS (densityZero_initial M))
  intro n hn
  by_cases hMn : M ≤ n
  · exact Or.inl ⟨hn, hMn⟩
  · exact Or.inr (Nat.lt_of_not_ge hMn)

end Erdos374.HarmanBoundary150

#print axioms Erdos374.HarmanBoundary150.forward_density_from_real_measure150

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.HarmanBoundary150.bounded_exception_measure_finite150,
    ``Erdos374.HarmanBoundary150.exponent_ledger150,
    ``Erdos374.HarmanBoundary150.halfUnit_scale150,
    ``Erdos374.HarmanBoundary150.halfUnit_bad150,
    ``Erdos374.HarmanBoundary150.halfUnit_count_le_measure150,
    ``Erdos374.HarmanBoundary150.forward_density_from_real_measure150]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#eval "HARMAN BOUNDARY 150: real-measure to integer-density bridge checked; analytic measure estimate remains a premise"

end

end Update150_Component_9
/- END COMPONENT: HarmanBoundary150.lean -/

/- BEGIN COMPONENT: Erdos374_RealBoundary150.lean -/
section Update150_Component_10



/-!
An alternative final interface matching the real-start short-interval source.
Both remaining analytic estimates are still explicit hypotheses.
-/

namespace Erdos374.AnalyticClosure150

open HarmanBoundary150 SamplingPolynomial149

theorem candidate_main_from_real_measure150
    (HF : RealForwardExceptionalMeasure150)
    (HS : PolynomialReciprocalPrimeSampling) : MainStatement :=
  candidate_main150 (forward_density_from_real_measure150 HF) HS

theorem positive_lower_density_from_real_measure150
    (HF : RealForwardExceptionalMeasure150)
    (HS : PolynomialReciprocalPrimeSampling) : PositiveLowerDensity D6 :=
  positive_lower_density150 (forward_density_from_real_measure150 HF) HS

#check candidate_main_from_real_measure150
#print axioms candidate_main_from_real_measure150
#print axioms positive_lower_density_from_real_measure150

run_cmd do
  for target in [``candidate_main_from_real_measure150,
      ``positive_lower_density_from_real_measure150] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Erdos374.AnalyticClosure150


end Update150_Component_10
/- END COMPONENT: Erdos374_RealBoundary150.lean -/

#check Erdos374.AnalyticClosure150.candidate_main150
#print axioms Erdos374.AnalyticClosure150.candidate_main150
#print axioms Erdos374.AnalyticClosure150.positive_lower_density150
run_cmd do
  for target in [``Erdos374.AnalyticClosure150.candidate_main150,
      ``Erdos374.AnalyticClosure150.positive_lower_density150,
      ``Erdos374.AnalyticClosure150.candidate_main_from_real_measure150,
      ``Erdos374.SamplerConstantClosed150.constant_sampling_unconditional,
      ``Erdos374.HarmanBoundary150.forward_density_from_real_measure150] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "UPDATE 150 FINAL AXIOM AUDIT PASSED: PNT, curves and constant sampling proved; TWO analytic premises remain"

end Update151_Component_1
/- END COMPONENT: Erdos374_Update150.lean -/

/- BEGIN COMPONENT: WeightedPrimeSampling151.lean -/
section Update151_Component_2


/-! Quantitative partial summation for complex prime weights.
The final bound uses the already proved quantitative PNT. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Erdos374.WeightedPrimeSampling151
open SamplingClosure147 SamplerConstantClosed150

def primeLog (n : ℕ) : ℂ := if n.Prime then (Real.log (n : ℝ) : ℂ) else 0

lemma primeLog_sum (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLog n = (Chebyshev.theta x : ℂ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp only [primeLog, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

lemma deriv_integrableOn {a b : ℝ} {g g' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Set.Icc a b)) :
    IntegrableOn (deriv g) (Set.Icc a b) := by
  apply hc.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (hd t ht).deriv.symm

/-- Exact complex Abel summation against the prime logarithm measure. -/
theorem weighted_theta_abel {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {g g' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Set.Icc a b)) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * primeLog n =
      g b * (Chebyshev.theta b : ℂ) - g a * (Chebyshev.theta a : ℂ) -
        ∫ t in a..b, g' t * (Chebyshev.theta t : ℂ) := by
  have h := sum_mul_eq_sub_sub_integral_mul primeLog ha hab
    (fun t ht => (hd t ht).differentiableAt) (deriv_integrableOn hd hc)
  simp_rw [primeLog_sum] at h
  rw [← intervalIntegral.integral_of_le hab] at h
  convert h using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [(hd t (by simpa only [Set.uIcc_of_le hab] using ht)).deriv]

lemma weighted_theta_kernel_integrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {g' : ℝ → ℂ} (hc : ContinuousOn g' (Set.Icc a b)) :
    IntervalIntegrable (fun t => g' t * (Chebyshev.theta t : ℂ)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have h := integrableOn_mul_sum_Icc primeLog (m := 0) ha hc.integrableOn_Icc
  simpa only [primeLog_sum] using h

lemma continuousOn_of_hasDerivAt {a b : ℝ} {g g' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t) :
    ContinuousOn g (Set.Icc a b) :=
  fun t ht => (hd t ht).continuousAt.continuousWithinAt

lemma weighted_identity_integral {a b : ℝ} (hab : a ≤ b) {g g' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Set.Icc a b)) :
    (∫ t in a..b, g t) = g b * (b : ℂ) - g a * (a : ℂ) -
      ∫ t in a..b, g' t * (t : ℂ) := by
  have hgc := continuousOn_of_hasDerivAt hd
  have hgi : IntervalIntegrable g volume a b := hgc.intervalIntegrable_of_Icc hab
  have hti : IntervalIntegrable (fun t => g' t * (t : ℂ)) volume a b :=
    (hc.mul Complex.continuous_ofReal.continuousOn).intervalIntegrable_of_Icc hab
  have hder : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => g t * (t : ℂ)) (g' t * (t : ℂ) + g t) t := by
    intro t ht
    simpa only [mul_one] using! (hd t (by simpa only [Set.uIcc_of_le hab] using ht)).mul
      (Complex.hasDerivAt_ofReal t)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hti.add hgi)
  rw [intervalIntegral.integral_add hti hgi] at hi
  linear_combination hi

/-- Discrepancy identity, retaining both endpoint errors and the actual derivative. -/
theorem weighted_theta_discrepancy_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {g g' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Set.Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * primeLog n) - (∫ t in a..b, g t) =
      g b * ((Chebyshev.theta b - b : ℝ) : ℂ) -
        g a * ((Chebyshev.theta a - a : ℝ) : ℂ) -
        ∫ t in a..b, g' t * ((Chebyshev.theta t - t : ℝ) : ℂ) := by
  have hti : IntervalIntegrable (fun t => g' t * (t : ℂ)) volume a b :=
    (hc.mul Complex.continuous_ofReal.continuousOn).intervalIntegrable_of_Icc hab
  rw [weighted_theta_abel ha hab hd hc, weighted_identity_integral hab hd hc]
  simp only [Complex.ofReal_sub, mul_sub]
  rw [intervalIntegral.integral_sub (weighted_theta_kernel_integrable ha hab hc) hti]
  ring

/-- A uniform theta-error bound controls arbitrary continuously differentiable
complex weights by endpoint size and total variation. -/
theorem weighted_theta_discrepancy_le {a b R : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : 0 ≤ R) {g g' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Set.Icc a b))
    (hθ : ∀ t ∈ Set.Icc a b, |Chebyshev.theta t - t| ≤ R) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * primeLog n) - (∫ t in a..b, g t)‖ ≤
      R * (‖g a‖ + ‖g b‖ + ∫ t in a..b, ‖g' t‖) := by
  have hi : ‖∫ t in a..b, g' t * ((Chebyshev.theta t - t : ℝ) : ℂ)‖ ≤
      (∫ t in a..b, ‖g' t‖) * R := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · apply Filter.Eventually.of_forall
      intro t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hθ t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
    · exact (hc.norm.intervalIntegrable_of_Icc hab).mul_const R
  have haE : ‖g a * ((Chebyshev.theta a - a : ℝ) : ℂ)‖ ≤ ‖g a‖ * R := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hθ a ⟨le_rfl, hab⟩) (norm_nonneg _)
  have hbE : ‖g b * ((Chebyshev.theta b - b : ℝ) : ℂ)‖ ≤ ‖g b‖ * R := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hθ b ⟨hab, le_rfl⟩) (norm_nonneg _)
  rw [weighted_theta_discrepancy_eq ha hab hd hc]
  calc
    _ ≤ (‖g b * ((Chebyshev.theta b - b : ℝ) : ℂ)‖ +
          ‖g a * ((Chebyshev.theta a - a : ℝ) : ℂ)‖) +
          ‖∫ t in a..b, g' t * ((Chebyshev.theta t - t : ℝ) : ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (‖g b‖ * R + ‖g a‖ * R) + (∫ t in a..b, ‖g' t‖) * R :=
      add_le_add (add_le_add hbE haE) hi
    _ = _ := by ring

def logQuotient (f : ℝ → ℂ) (t : ℝ) : ℂ := f t / (Real.log t : ℂ)

def logQuotientD (f f' : ℝ → ℂ) (t : ℝ) : ℂ :=
  f' t / (Real.log t : ℂ) - f t / ((t : ℂ) * (Real.log t : ℂ) ^ 2)

lemma logQuotient_hasDerivAt {f f' : ℝ → ℂ} {t : ℝ}
    (ht : 1 < t) (hd : HasDerivAt f (f' t) t) :
    HasDerivAt (logQuotient f) (logQuotientD f f' t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  have hlc : (Real.log t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl0
  have h := hd.div ((Real.hasDerivAt_log ht0).ofReal_comp) hlc
  apply h.congr_deriv
  simp only [logQuotientD, Complex.ofReal_inv]
  field_simp <;> ring

lemma logQuotientD_continuousOn {a b : ℝ} (ha : 1 < a) {f f' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Set.Icc a b)) :
    ContinuousOn (logQuotientD f f') (Set.Icc a b) := by
  have hfc := continuousOn_of_hasDerivAt hd
  intro t ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  have hlc : (Real.log t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl0
  have hpow : (Real.log t : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hlc
  have hden : (t : ℂ) * (Real.log t : ℂ) ^ 2 ≠ 0 := mul_ne_zero htc hpow
  have hfc' := hfc t ht
  have hdc' := hc t ht
  unfold logQuotientD
  have hlogr : ContinuousWithinAt Real.log (Set.Icc a b) t :=
    (Real.continuousAt_log ht0).continuousWithinAt
  have hlogc : ContinuousWithinAt (fun t : ℝ => (Real.log t : ℂ)) (Set.Icc a b) t :=
    Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hlogr
  have htc' : ContinuousWithinAt (fun t : ℝ => (t : ℂ)) (Set.Icc a b) t :=
    Complex.continuous_ofReal.continuousWithinAt
  exact (hdc'.div hlogc hlc).sub (hfc'.div (htc'.mul (hlogc.pow 2)) hden)

lemma logQuotient_norm_le {a t M : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hL : 1 ≤ Real.log a) (ht : a ≤ t) (hf : ‖f t‖ ≤ M) :
    ‖logQuotient f t‖ ≤ M := by
  have hlog : 1 ≤ Real.log t := hL.trans (Real.log_le_log ha ht)
  rw [logQuotient, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < Real.log t)]
  exact (div_le_self (norm_nonneg _) hlog).trans hf

lemma logQuotientD_norm_le {a t M : ℝ} {f f' : ℝ → ℂ}
    (ha : 0 < a) (hL : 1 ≤ Real.log a) (ht : a ≤ t) (hf : ‖f t‖ ≤ M) :
    ‖logQuotientD f f' t‖ ≤ ‖f' t‖ + M / a := by
  have ht0 : 0 < t := ha.trans_le ht
  have hlog : 1 ≤ Real.log t := hL.trans (Real.log_le_log ha ht)
  have hlog0 : 0 < Real.log t := by linarith
  have hlog2 : 1 ≤ (Real.log t) ^ 2 := by nlinarith
  have hden : a ≤ t * (Real.log t) ^ 2 :=
    ht.trans (le_mul_of_one_le_right ht0.le hlog2)
  unfold logQuotientD
  calc
    _ ≤ ‖f' t / (Real.log t : ℂ)‖ +
        ‖f t / ((t : ℂ) * (Real.log t : ℂ) ^ 2)‖ := norm_sub_le _ _
    _ = ‖f' t‖ / Real.log t + ‖f t‖ / (t * (Real.log t) ^ 2) := by
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0, abs_of_pos hlog0]
    _ ≤ ‖f' t‖ + M / a := by
      apply add_le_add (div_le_self (norm_nonneg _) hlog)
      exact (div_le_div_of_nonneg_left (norm_nonneg _) ha hden).trans
        (div_le_div_of_nonneg_right hf ha.le)

lemma prime_band_eq_weighted_quotient (P : ℕ) (f : ℝ → ℂ) :
    (∑ n ∈ Finset.Ioc P (2 * P), logQuotient f n * primeLog n) =
      ∑ p ∈ openPrimeBand P, f p := by
  rw [openPrimeBand, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hp.one_lt
    have hl0 : (Real.log (n : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos hn1))
    simp only [primeLog, logQuotient, if_pos hp]
    exact div_mul_cancel₀ _ hl0
  · simp [primeLog, hp]

/-- Finite prime sampling from a uniform theta-error bound on one band. -/
theorem weighted_prime_discrepancy_of_theta {P : ℕ} {R M V : ℝ}
    (hP : 2 ≤ P) (hL : 1 ≤ Real.log (P : ℝ)) (hR : 0 ≤ R)
    {f f' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (P : ℝ) (2 * (P : ℝ)), HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Set.Icc (P : ℝ) (2 * (P : ℝ))))
    (hM : ∀ t ∈ Set.Icc (P : ℝ) (2 * (P : ℝ)), ‖f t‖ ≤ M)
    (hV : (∫ t in (P : ℝ)..(2 * (P : ℝ)), ‖f' t‖) ≤ V)
    (hθ : ∀ t ∈ Set.Icc (P : ℝ) (2 * (P : ℝ)), |Chebyshev.theta t - t| ≤ R) :
    ‖(∑ p ∈ openPrimeBand P, f p) -
      (∫ t in (P : ℝ)..(2 * (P : ℝ)), f t / (Real.log t : ℂ))‖ ≤
      R * (3 * M + V) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hP1 : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
  have hab : (P : ℝ) ≤ 2 * (P : ℝ) := by linarith
  have hg : ∀ t ∈ Set.Icc (P : ℝ) (2 * (P : ℝ)),
      HasDerivAt (logQuotient f) (logQuotientD f f' t) t := by
    intro t ht
    exact logQuotient_hasDerivAt (hP1.trans_le ht.1) (hd t ht)
  have hgc := logQuotientD_continuousOn hP1 hd hc
  have hgi : IntervalIntegrable (logQuotientD f f') volume (P : ℝ) (2 * (P : ℝ)) :=
    hgc.intervalIntegrable_of_Icc hab
  have hfi : IntervalIntegrable (fun t => ‖f' t‖) volume (P : ℝ) (2 * (P : ℝ)) :=
    hc.norm.intervalIntegrable_of_Icc hab
  have hgV : (∫ t in (P : ℝ)..(2 * (P : ℝ)), ‖logQuotientD f f' t‖) ≤ V + M := by
    calc
      _ ≤ ∫ t in (P : ℝ)..(2 * (P : ℝ)), (‖f' t‖ + M / (P : ℝ)) :=
        intervalIntegral.integral_mono_on hab hgi.norm
          (hfi.add intervalIntegrable_const)
          (fun t ht => logQuotientD_norm_le hP0 hL ht.1 (hM t ht))
      _ = (∫ t in (P : ℝ)..(2 * (P : ℝ)), ‖f' t‖) + M := by
        rw [intervalIntegral.integral_add hfi intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        field_simp
        ring
      _ ≤ V + M := add_le_add hV le_rfl
  have hgA : ‖logQuotient f (P : ℝ)‖ ≤ M :=
    logQuotient_norm_le hP0 hL le_rfl (hM _ ⟨le_rfl, hab⟩)
  have hgB : ‖logQuotient f (2 * (P : ℝ))‖ ≤ M :=
    logQuotient_norm_le hP0 hL hab (hM _ ⟨hab, le_rfl⟩)
  have h := weighted_theta_discrepancy_le hP0.le hab hR hg hgc hθ
  have hfloor : ⌊2 * (P : ℝ)⌋₊ = 2 * P := by
    rw [show 2 * (P : ℝ) = ((2 * P : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
  simp only [Nat.floor_natCast, hfloor, prime_band_eq_weighted_quotient] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hR
  linarith only [hgA, hgB, hgV]


end Erdos374.WeightedPrimeSampling151
end
end Update151_Component_2
end Update152_Component_1

end
