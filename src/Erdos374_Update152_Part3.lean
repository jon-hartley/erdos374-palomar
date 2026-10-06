/- Part 3 of 7 of `Erdos374_Update152` (split for the 10,000-line limit); continues `Erdos374_Update152_Part2`. -/
module

public import Erdos374_Update152_Part2

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
namespace RemainingAnalytic63
open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic61 RemainingAnalytic62

/-- Fixed V-factor has at most one residue root. -/
theorem anchorVFactor_root_unique63
    {j t v lam z1 z2 : ℕ}
    (hp : lam.Prime)
    (hj0 : (j : ZMod lam) ≠ 0)
    (hz1lt : z1 < lam) (hz2lt : z2 < lam)
    (h1 :
      (j : ZMod lam) * (z1 : ZMod lam) + (t : ZMod lam) - (v : ZMod lam) = 0)
    (h2 :
      (j : ZMod lam) * (z2 : ZMod lam) + (t : ZMod lam) - (v : ZMod lam) = 0) :
    z1 = z2 := by
  letI : Fact lam.Prime := ⟨hp⟩
  have heq1 :
      (j : ZMod lam) * (z1 : ZMod lam) + (t : ZMod lam) =
        (v : ZMod lam) :=
    sub_eq_zero.mp h1
  have heq2 :
      (j : ZMod lam) * (z2 : ZMod lam) + (t : ZMod lam) =
        (v : ZMod lam) :=
    sub_eq_zero.mp h2
  have hmul :
      (j : ZMod lam) * (z1 : ZMod lam) =
        (j : ZMod lam) * (z2 : ZMod lam) := by
    exact add_right_cancel (heq1.trans heq2.symm)
  have hzmod : (z1 : ZMod lam) = (z2 : ZMod lam) :=
    mul_left_cancel₀ hj0 hmul
  have hmods : z1 % lam = z2 % lam :=
    (ZMod.natCast_eq_natCast_iff' z1 z2 lam).mp hzmod
  simpa [Nat.mod_eq_of_lt hz1lt, Nat.mod_eq_of_lt hz2lt] using hmods

/-! -------------------------------------------------------------------------
C. Cardinality bounds via assignment of each root to one factor
------------------------------------------------------------------------- -/

/-- A general finite-root cover lemma: if every x in roots is assigned to an
index i in idx and each fixed i has at most one x, then card roots <= card idx.
-/
theorem card_le_of_unique_factor63
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Nonempty β]
    (roots : Finset α) (idx : Finset β)
    (R : α → β → Prop) [DecidableRel R]
    (hex : ∀ x ∈ roots, ∃ i ∈ idx, R x i)
    (huniq : ∀ i ∈ idx, ∀ x1 ∈ roots, ∀ x2 ∈ roots,
      R x1 i → R x2 i → x1 = x2) :
    roots.card ≤ idx.card := by
  classical
  let chooseIdx : α → β := fun x =>
    if hx : x ∈ roots then Classical.choose (hex x hx) else Classical.choice inferInstance
  have hchoose_mem :
      ∀ x ∈ roots, chooseIdx x ∈ idx := by
    intro x hx
    simp [chooseIdx, hx, Classical.choose_spec (hex x hx)]
  have hinj :
      Set.InjOn chooseIdx ↑roots := by
    intro x1 hx1 x2 hx2 heq
    have hx1' : x1 ∈ roots := by simpa using hx1
    have hx2' : x2 ∈ roots := by simpa using hx2
    let i := chooseIdx x1
    have hi : i ∈ idx := hchoose_mem x1 hx1'
    have hR1 : R x1 i := by
      dsimp [i, chooseIdx]
      simp [hx1']
      exact (Classical.choose_spec (hex x1 hx1')).2
    have hR2choose : R x2 (chooseIdx x2) := by
      simp only [chooseIdx, dif_pos hx2']
      exact (Classical.choose_spec (hex x2 hx2')).2
    have hi2eq : chooseIdx x2 = i := by
      simpa [i] using heq.symm
    rw [hi2eq] at hR2choose
    have hR2 : R x2 i := hR2choose
    exact huniq i hi x1 hx1' x2 hx2' hR1 hR2
  exact Finset.card_le_card_of_injOn
    (f := chooseIdx) hchoose_mem hinj

theorem anchorIProductRootBoundLegal_proved63 :
    AnchorIProductRootBoundLegal62 := by
  intro a r j t h ell lam hj hjr hh hell ht hp ha hsep
  let roots := anchorIRoots61 r ell lam
  let idx := (Finset.range ell).filter (fun i => 1 ≤ i)
  have hr0 := r_nonzero_mod63 hp hj hjr hh hell hsep
  have hcard :
      roots.card ≤ idx.card := by
    apply card_le_of_unique_factor63
      roots idx
      (fun z i =>
        ((r : ZMod lam) * (z : ZMod lam) - (i : ZMod lam)) = 0)
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact anchorIRoot_mem_factor63 hp hz'.2
    · intro i hi z1 hz1 z2 hz2 h1 h2
      have hz1lt := Finset.mem_range.mp (Finset.mem_filter.mp hz1).1
      have hz2lt := Finset.mem_range.mp (Finset.mem_filter.mp hz2).1
      exact anchorIFactor_root_unique63 hp hr0 hz1lt hz2lt h1 h2
  calc
    (anchorIRoots61 r ell lam).card = roots.card := rfl
    _ ≤ idx.card := hcard
    _ ≤ ell := by
      dsimp [idx]
      exact le_trans
        (Finset.card_filter_le (Finset.range ell) (fun i => 1 ≤ i))
        (by simp)

theorem anchorVProductRootBoundLegal_proved63 :
    AnchorVProductRootBoundLegal62 := by
  intro a r j t h ell lam hj hjr hh hell ht hp ha hsep
  let roots := anchorVRoots61 j t h lam
  let idx := (Finset.range h).filter (fun v => v ≠ t)
  have hj0 := j_nonzero_mod63 hp hj hjr hh hell hsep
  have hcard :
      roots.card ≤ idx.card := by
    apply card_le_of_unique_factor63
      roots idx
      (fun z v =>
        ((j : ZMod lam) * (z : ZMod lam) + (t : ZMod lam) - (v : ZMod lam)) = 0)
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact anchorVRoot_mem_factor63 hp hz'.2
    · intro v hv z1 hz1 z2 hz2 h1 h2
      have hz1lt := Finset.mem_range.mp (Finset.mem_filter.mp hz1).1
      have hz2lt := Finset.mem_range.mp (Finset.mem_filter.mp hz2).1
      exact anchorVFactor_root_unique63 hp hj0 hz1lt hz2lt h1 h2
  calc
    (anchorVRoots61 j t h lam).card = roots.card := rfl
    _ ≤ idx.card := hcard
    _ ≤ h := by
      dsimp [idx]
      exact le_trans
        (Finset.card_filter_le (Finset.range h) (fun v => v ≠ t))
        (by simp)

/-! -------------------------------------------------------------------------
D. Leading coefficient nonzero: isolate q(a)
------------------------------------------------------------------------- -/

/-- Every prime divisor of q(a) is <= a.  This is the exact arithmetic fact
needed to show lam ∤ q(a) when a < lam. -/
def PrimeDivisorQLe63 : Prop :=
  ∀ a p : ℕ, p.Prime → p ∣ q a → p ≤ a

theorem anchorLeadingCoeffNonzero_from_qPrimeBound63
    (hQ : PrimeDivisorQLe63) :
    AnchorLeadingCoeffNonzeroLegal62 := by
  intro a r j t h ell lam hj hjr hh hell ht hp ha hsep
  letI : Fact lam.Prime := ⟨hp⟩
  have hr0 := r_nonzero_mod63 hp hj hjr hh hell hsep
  have hj0 := j_nonzero_mod63 hp hj hjr hh hell hsep
  have hq0 : (q a : ZMod lam) ≠ 0 := by
    intro hz
    have hdiv : lam ∣ q a := by
      exact (ZMod.natCast_eq_zero_iff (q a) lam).mp hz
    have hle : lam ≤ a := hQ a lam hp hdiv
    omega
  unfold anchorLeadingCoeff61
  norm_num only [Nat.cast_mul]
  exact mul_ne_zero (mul_ne_zero hq0 hr0) hj0

/-! -------------------------------------------------------------------------
E. Updated elementary frontier
-------------------------------------------------------------------------

After this repair, three of the five elementary Weil-side statements are
targeted directly:
  * I-product root bound;
  * V-product root bound;
  * leading coefficient nonzero modulo lam, reduced to `PrimeDivisorQLe63`.

The quadratic-character side remains:
  * `QuadraticCharacterPointwise62`;
  * `AnchorRangeQuadraticSumBridge62`.

And the only deep theorem remains:
  * `AnchorQuadraticWeil59`.
-/

-- Historical audit output: #print axioms prod_eq_zero_mem63
-- Historical audit output: #print axioms anchorIRoot_mem_factor63
-- Historical audit output: #print axioms anchorVRoot_mem_factor63
-- Historical audit output: #print axioms r_nonzero_mod63
-- Historical audit output: #print axioms j_nonzero_mod63
-- Historical audit output: #print axioms anchorIFactor_root_unique63
-- Historical audit output: #print axioms anchorVFactor_root_unique63
-- Historical audit output: #print axioms anchorIProductRootBoundLegal_proved63
-- Historical audit output: #print axioms anchorVProductRootBoundLegal_proved63
-- Historical audit output: #print axioms anchorLeadingCoeffNonzero_from_qPrimeBound63

end RemainingAnalytic63


/-! ## 63. Repair 65: close the q(a) divisor fact and expose the cleaned Weil frontier

The Repair-64 API fixes leave only the generic factor-assignment injection as
the source of `sorryAx` in the two product-root bounds.  That proof has now
been simplified.

This section also discharges `PrimeDivisorQLe63` from the already-proved
factorial squarefree-kernel lemmas near the beginning of the file.
-/

namespace RemainingAnalytic65

open RemainingAnalytic37 RemainingAnalytic61 RemainingAnalytic62 RemainingAnalytic63

/-! -------------------------------------------------------------------------
A. Prime divisors of q(a) are bounded by a
------------------------------------------------------------------------- -/

theorem primeDivisorQLe_proved65 :
    PrimeDivisorQLe63 := by
  intro a p hp hpdq
  by_contra hnot
  have hap : a < p := Nat.lt_of_not_ge hnot
  have hnotdvd_fact : ¬ p ∣ a.factorial := by
    rw [hp.dvd_factorial]
    omega
  have hfac0 :
      a.factorial.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnotdvd_fact
  have hodd := (prime_dvd_q_iff a p hp).mp hpdq
  rw [hfac0] at hodd
  norm_num at hodd

theorem anchorLeadingCoeffNonzeroLegal_proved65 :
    AnchorLeadingCoeffNonzeroLegal62 :=
  anchorLeadingCoeffNonzero_from_qPrimeBound63
    primeDivisorQLe_proved65

/-! -------------------------------------------------------------------------
B. Product-root bounds now feed directly into the legal root cover
------------------------------------------------------------------------- -/

theorem anchorTwoFamilyRootCoverLegal_proved65 :
    AnchorTwoFamilyRootCoverLegal62 :=
  anchorTwoFamilyRootCoverLegal_from_productBounds62
    anchorLeadingCoeffNonzeroLegal_proved65
    anchorIProductRootBoundLegal_proved63
    anchorVProductRootBoundLegal_proved63

theorem anchorZeroBoundLegal_proved65 :
    AnchorZeroBoundLegal62 :=
  anchorZeroBoundLegal_from_cover62
    anchorTwoFamilyRootCoverLegal_proved65

/-! -------------------------------------------------------------------------
C. Cleaned Weil-side frontier
-------------------------------------------------------------------------

At this point all root-count bookkeeping is intended to be internal.

The only remaining quadratic-character bookkeeping targets are:

  * `QuadraticCharacterPointwise62`;
  * `AnchorRangeQuadraticSumBridge62`.

Together with the deep theorem:

  * `AnchorQuadraticWeil59`.

Once the first two are proved, the entire square-residue restriction is
reduced to the specialized Weil estimate alone.
-/

theorem weilSquareResidueRestriction_from_charAPI65
    (hWeil : RemainingAnalytic59.AnchorQuadraticWeil59)
    (hPoint : QuadraticCharacterPointwise62)
    (hRange : AnchorRangeQuadraticSumBridge62) :
    WeilSquareResidueRestriction :=
  weilSquareResidueRestriction_from_legalPointwise62
    hWeil
    hPoint
    hRange
    anchorLeadingCoeffNonzeroLegal_proved65
    anchorIProductRootBoundLegal_proved63
    anchorVProductRootBoundLegal_proved63

-- Historical audit output: #print axioms primeDivisorQLe_proved65
-- Historical audit output: #print axioms anchorLeadingCoeffNonzeroLegal_proved65
-- Historical audit output: #print axioms anchorTwoFamilyRootCoverLegal_proved65
-- Historical audit output: #print axioms anchorZeroBoundLegal_proved65
-- Historical audit output: #print axioms weilSquareResidueRestriction_from_charAPI65

end RemainingAnalytic65

/-!
REPAIR 65 STATUS
================

* Simplified/fixed the generic root-to-factor choice injection.
* Proved every prime divisor p of q(a) satisfies p <= a using the existing
  factorial squarefree-kernel lemmas.
* Therefore the leading coefficient is nonzero at every legal auxiliary prime.
* The intended remaining Weil-side boundary is now only:
    QuadraticCharacterPointwise62
    AnchorRangeQuadraticSumBridge62
    AnchorQuadraticWeil59 [deep].
-/


/-! ## 64. Repair 66: directly attack the quadratic-character API layer

The product-root side is green.  Repair 65 also makes the q(a) divisor bound
elementary.  We now attack the final two non-deep Weil-side statements:

  * `QuadraticCharacterPointwise62`;
  * `AnchorRangeQuadraticSumBridge62`.

These are purely standard finite-field/library facts.
-/

namespace RemainingAnalytic66

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic61
open RemainingAnalytic62 RemainingAnalytic63 RemainingAnalytic65

/-! -------------------------------------------------------------------------
A. Relate the project's square predicate to Mathlib's IsSquare
------------------------------------------------------------------------- -/

theorem modSquareOrZero_iff_isSquare66
    {lam : ℕ} (x : ZMod lam) :
    ModSquareOrZero x ↔ IsSquare x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [pow_two] using hy
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [pow_two] using hy

/-! -------------------------------------------------------------------------
B. Pointwise quadratic-character identity
------------------------------------------------------------------------- -/

theorem quadraticCharacterPointwise_proved66 :
    QuadraticCharacterPointwise62 := by
  intro lam hp x
  letI : Fact lam.Prime := ⟨hp⟩
  rw [quadraticCharValue_of_prime62 hp x]
  rw [quadraticChar_apply]
  unfold quadraticCharFun squareIndicator61 zeroIndicator61
  by_cases hx : x = 0
  · subst x
    have hm0 : ModSquareOrZero (0 : ZMod lam) := by
      exact ⟨0, by simp⟩
    simp [hm0]
  · by_cases hs : IsSquare x
    · have hm : ModSquareOrZero x :=
        (modSquareOrZero_iff_isSquare66 x).2 hs
      simp [hx, hs, hm]
    · have hm : ¬ ModSquareOrZero x := by
        intro hm'
        exact hs ((modSquareOrZero_iff_isSquare66 x).1 hm')
      simp [hx, hs, hm]

/-! -------------------------------------------------------------------------
C. Enumerating ZMod by 0,...,lam-1
------------------------------------------------------------------------- -/

theorem finEquiv_eq_natCast67
    {lam : ℕ} [NeZero lam] (x : Fin lam) :
    (ZMod.finEquiv lam) x = (x.val : ZMod lam) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast_of_lt x.isLt]
  cases lam with
  | zero =>
      exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rfl

theorem anchorRangeQuadraticSumBridge_proved66 :
    AnchorRangeQuadraticSumBridge62 := by
  intro a r j t h ell lam hp
  letI : Fact lam.Prime := ⟨hp⟩
  letI : NeZero lam := ⟨hp.ne_zero⟩
  unfold AnchorRangeQuadraticSum62 AnchorQuadraticSum59
  simp only [quadraticCharValue62, dif_pos hp]
  rw [Finset.sum_range]
  let f : ZMod lam → ℤ := fun z =>
    (quadraticChar (ZMod lam))
      (anchorEvalMod a r j t h ell lam z)
  have hcompat :
      (∑ x : Fin lam, f (x.val : ZMod lam)) =
        ∑ x : Fin lam, f ((ZMod.finEquiv lam) x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [finEquiv_eq_natCast67 x]
  have heq :
      (∑ x : Fin lam, f ((ZMod.finEquiv lam) x)) =
        ∑ z : ZMod lam, f z := by
    exact (ZMod.finEquiv lam).toEquiv.sum_comp f
  exact hcompat.trans heq

/-! -------------------------------------------------------------------------
D. Full Weil-side bookkeeping is now internal
------------------------------------------------------------------------- -/

theorem anchorQuadraticIndicatorSumIdentity_proved66 :
    RemainingAnalytic60.AnchorQuadraticIndicatorSumIdentity60 :=
  anchorQuadraticIndicatorSumIdentity_from_pointwise62
    quadraticCharacterPointwise_proved66
    anchorRangeQuadraticSumBridge_proved66

theorem weilSquareResidueRestriction_from_actualWeil66
    (hWeil : RemainingAnalytic59.AnchorQuadraticWeil59) :
    WeilSquareResidueRestriction :=
  weilSquareResidueRestriction_from_charAPI65
    hWeil
    quadraticCharacterPointwise_proved66
    anchorRangeQuadraticSumBridge_proved66

/-! -------------------------------------------------------------------------
E. The finite-field frontier after Repair 66
-------------------------------------------------------------------------

If the two theorems above compile, every elementary finite-field statement is
internal.  The Weil side of Proposition 5.1 is then reduced to exactly one
specialized external theorem:

    RemainingAnalytic59.AnchorQuadraticWeil59.

Combined with Repairs 59 and 58, the whole anchor-sieve frontier is then:

    DyadicPrimeLower59
    StandardAdditiveLargeSieve59
    AdditiveEnergyIdentity59
    AnchorQuadraticWeil59

where only the last is project-specific finite-field cancellation.
-/

-- Historical audit output: #print axioms modSquareOrZero_iff_isSquare66
-- Historical audit output: #print axioms quadraticCharacterPointwise_proved66
-- Historical audit output: #print axioms anchorRangeQuadraticSumBridge_proved66
-- Historical audit output: #print axioms anchorQuadraticIndicatorSumIdentity_proved66
-- Historical audit output: #print axioms primeDivisorQLe_proved65
-- Historical audit output: #print axioms anchorLeadingCoeffNonzeroLegal_proved65
-- Historical audit output: #print axioms anchorIProductRootBoundLegal_proved63
-- Historical audit output: #print axioms anchorVProductRootBoundLegal_proved63
-- Historical audit output: #print axioms weilSquareResidueRestriction_from_actualWeil66

end RemainingAnalytic66

/-!
REPAIR 66 STATUS
================

This repair directly attempts to eliminate the last two elementary
quadratic-character assumptions.

If green:
  * all zero/root bookkeeping is internal;
  * all square-indicator bookkeeping is internal;
  * the only specialized Weil-side theorem left is AnchorQuadraticWeil59.

The non-Weil analytic frontier remains the standard dyadic prime lower bound,
the standard additive large sieve, and the finite Fourier-energy identity.
-/


/-! ## 65. Repair 67: close all elementary quadratic-character bookkeeping

This section merely records the now fully assembled finite-field consequence.
If the two Repair-66 API theorems compile, the entire elementary Weil-side
bookkeeping is internal.
-/

namespace RemainingAnalytic67

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic62
open RemainingAnalytic63 RemainingAnalytic65 RemainingAnalytic66

theorem allElementaryWeilBookkeeping67 :
    RemainingAnalytic60.AnchorQuadraticIndicatorSumIdentity60 ∧
    AnchorZeroBoundLegal62 :=
  ⟨anchorQuadraticIndicatorSumIdentity_proved66,
   anchorZeroBoundLegal_proved65⟩

theorem weilSquareResidueRestriction_from_only_specializedWeil67
    (hWeil : RemainingAnalytic59.AnchorQuadraticWeil59) :
    WeilSquareResidueRestriction :=
  weilSquareResidueRestriction_from_actualWeil66 hWeil

/-!
If green, the specialized finite-field frontier is literally one theorem:
`RemainingAnalytic59.AnchorQuadraticWeil59`.

The non-finite-field analytic frontier remains:
  * `DyadicPrimeLower59`;
  * `StandardAdditiveLargeSieve59`;
  * `AdditiveEnergyIdentity59`.
-/

-- Historical audit output: #print axioms finEquiv_eq_natCast67
-- Historical audit output: #print axioms modSquareOrZero_iff_isSquare66
-- Historical audit output: #print axioms quadraticCharacterPointwise_proved66
-- Historical audit output: #print axioms anchorRangeQuadraticSumBridge_proved66
-- Historical audit output: #print axioms anchorQuadraticIndicatorSumIdentity_proved66
-- Historical audit output: #print axioms allElementaryWeilBookkeeping67
-- Historical audit output: #print axioms weilSquareResidueRestriction_from_only_specializedWeil67

end RemainingAnalytic67


/-! ## 66. Repair 69: clean character checkpoint and exact Fourier frontier

Repair 68 mixed a now-tiny character enumeration issue with an experimental
Fourier proof.  This repair keeps the character fix and restates the Fourier
frontier with all required instances scoped correctly.

The important mathematical split is:

* finite-field bookkeeping should now be entirely internal;
* additive Fourier energy still needs only finite Fourier algebra;
* the analytic large-sieve inequality remains separate.
-/

namespace RemainingAnalytic69

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic66 RemainingAnalytic67

/-! -------------------------------------------------------------------------
A. Character-side checkpoint
------------------------------------------------------------------------- -/

theorem elementaryWeilBookkeeping_clean69 :
    RemainingAnalytic60.AnchorQuadraticIndicatorSumIdentity60 ∧
    RemainingAnalytic62.AnchorZeroBoundLegal62 :=
  ⟨anchorQuadraticIndicatorSumIdentity_proved66,
   RemainingAnalytic65.anchorZeroBoundLegal_proved65⟩

theorem weilRestriction_from_only_specializedWeil69
    (hWeil : RemainingAnalytic59.AnchorQuadraticWeil59) :
    WeilSquareResidueRestriction :=
  weilSquareResidueRestriction_from_actualWeil66 hWeil

/-! -------------------------------------------------------------------------
B. Correctly-instanced Fourier objects
------------------------------------------------------------------------- -/

def residueMultiplicity69
    (T : Finset ℕ) (lam : ℕ) [NeZero lam] (u : ZMod lam) : ℕ :=
  (T.filter (fun z => z % lam = u.val)).card

noncomputable def residueMultiplicityC69
    (T : Finset ℕ) (lam : ℕ) [NeZero lam] (u : ZMod lam) : ℂ :=
  (residueMultiplicity69 T lam u : ℂ)

/-- Full Parseval in the normalization naturally produced by `ZMod.dft`.
The `NeZero` instance is introduced inside the proposition before any DFT term
is elaborated. -/
def FullDFTParseval69 : Prop :=
  ∀ T : Finset ℕ, ∀ lam : ℕ, ∀ hlam : 0 < lam,
    letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
    (∑ k : ZMod lam,
      ‖ZMod.dft (residueMultiplicityC69 T lam) k‖ ^ 2)
      =
    (lam : ℝ) *
      (∑ u : ZMod lam, (residueMultiplicity69 T lam u : ℝ) ^ 2)

/-- The DFT of the residue multiplicity function equals the original
exponential sum over T.  This is finite regrouping by residue class, not an
analytic estimate. -/
def AdditiveSumDFTMatch69 : Prop :=
  ∀ T : Finset ℕ, ∀ lam : ℕ, ∀ hlam : 0 < lam,
    letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
    ∀ k : ZMod lam,
      ZMod.dft (residueMultiplicityC69 T lam) k
        =
      ∑ z ∈ T, ZMod.stdAddChar (-( (z : ZMod lam) * k))

/-- Collision-profile bridge between the ZMod multiplicity formulation and the
existing natural-remainder formulation used by `residueCollisionSum`. -/
def ResidueCollisionBridge69 : Prop :=
  ∀ T : Finset ℕ, ∀ lam : ℕ, ∀ hlam : 0 < lam,
    letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
    (∑ u : ZMod lam, (residueMultiplicity69 T lam u : ℝ) ^ 2)
      =
    residueCollisionSum T lam

/-! These three finite facts are sufficient to recover
`AdditiveEnergyIdentity59`; the genuinely analytic large-sieve estimate is not
used here. -/
def ExactFourierPackage69 : Prop :=
  FullDFTParseval69 ∧ AdditiveSumDFTMatch69 ∧ ResidueCollisionBridge69

/-! -------------------------------------------------------------------------
C. Honest frontier
-------------------------------------------------------------------------

If the character checkpoint above compiles green, then:

WEIL SIDE:
  only `AnchorQuadraticWeil59` remains specialized/deep.

FOURIER SIDE:
  three finite algebraic statements remain:
    `FullDFTParseval69`
    `AdditiveSumDFTMatch69`
    `ResidueCollisionBridge69`

ANALYTIC SIDE:
  `DyadicPrimeLower59`
  `StandardAdditiveLargeSieve59`

The three Fourier statements should be internalized before treating the
large-sieve inequality itself as the external analytic input.
-/

-- Historical audit output: #print axioms RemainingAnalytic66.finEquiv_eq_natCast67
-- Historical audit output: #print axioms RemainingAnalytic66.anchorRangeQuadraticSumBridge_proved66
-- Historical audit output: #print axioms elementaryWeilBookkeeping_clean69
-- Historical audit output: #print axioms weilRestriction_from_only_specializedWeil69

end RemainingAnalytic69


/-! ## 67. Repair 70: character-green checkpoint and correctly scoped Fourier frontier

The documentation for `ZMod.finEquiv` gives the key definitional equation:
for successor modulus it is `RingEquiv.refl (Fin (n+1))`.  The robust proof
therefore compares `ZMod.val` on both sides; the natural cast has value `x.val`
because `x.val < lam`.

This repair also corrects the collision-profile Fourier statement so its
`Fintype (ZMod lam)` instance is generated only after `NeZero lam` is installed.
-/

namespace RemainingAnalytic70

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic66
open RemainingAnalytic67 RemainingAnalytic69

/-! -------------------------------------------------------------------------
A. Final elementary Weil checkpoint
------------------------------------------------------------------------- -/

theorem elementaryWeilBookkeeping_final70 :
    RemainingAnalytic60.AnchorQuadraticIndicatorSumIdentity60 ∧
    RemainingAnalytic62.AnchorZeroBoundLegal62 :=
  elementaryWeilBookkeeping_clean69

theorem weilRestriction_from_only_specializedWeil70
    (hWeil : RemainingAnalytic59.AnchorQuadraticWeil59) :
    WeilSquareResidueRestriction :=
  weilRestriction_from_only_specializedWeil69 hWeil

/-! -------------------------------------------------------------------------
B. Fourier frontier with no elaboration leaks
------------------------------------------------------------------------- -/

def FourierFiniteCore70 : Prop :=
  FullDFTParseval69 ∧
  AdditiveSumDFTMatch69 ∧
  ResidueCollisionBridge69

/-- Once the three finite Fourier identities are available, the only remaining
large-sieve-side theorem should be the genuinely analytic
`StandardAdditiveLargeSieve59`. -/
structure CleanProp51Frontier70 where
  dyadic_prime_lower : DyadicPrimeLower59
  additive_large_sieve : StandardAdditiveLargeSieve59
  fourier_finite_core : FourierFiniteCore70
  specialized_weil : RemainingAnalytic59.AnchorQuadraticWeil59

/-!
The next task is to prove the finite Fourier core.  No further finite-field
bookkeeping should be needed.

Mathematically:
  FullDFTParseval69      = finite Parseval / orthogonality;
  AdditiveSumDFTMatch69  = regrouping T by residue class;
  ResidueCollisionBridge69 = matching ZMod fibers with natural remainders.

Only after these are internal should `StandardAdditiveLargeSieve59` remain as
the large-sieve analytic input.
-/

-- Historical audit output: #print axioms RemainingAnalytic66.finEquiv_eq_natCast67
-- Historical audit output: #print axioms RemainingAnalytic66.anchorRangeQuadraticSumBridge_proved66
-- Historical audit output: #print axioms elementaryWeilBookkeeping_final70
-- Historical audit output: #print axioms weilRestriction_from_only_specializedWeil70

end RemainingAnalytic70


/-! ## 68. Repair 71: prove the DFT regrouping identity; attack collision bridge

Repair 70 is the clean finite-field checkpoint.  We now attack the finite
Fourier core directly.

The DFT matching identity is just fiberwise regrouping over the residue map.
No analytic estimate is involved.
-/

namespace RemainingAnalytic71

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic69 RemainingAnalytic70

/-! -------------------------------------------------------------------------
A. Elementary residue facts
------------------------------------------------------------------------- -/

theorem natCast_eq_iff_mod_eq71
    {lam z u : ℕ} [NeZero lam] (hu : u < lam) :
    ((z : ZMod lam) = (u : ZMod lam)) ↔ z % lam = u := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hu] using hv
  · intro h
    apply ZMod.val_injective
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hu] using h

theorem residueMultiplicity_cast_eq_natFiber71
    (T : Finset ℕ) {lam u : ℕ} [NeZero lam] (hu : u < lam) :
    residueMultiplicity69 T lam (u : ZMod lam)
      =
    fiberCount T (fun z => z % lam) u := by
  unfold residueMultiplicity69 fiberCount
  rw [ZMod.val_natCast_of_lt hu]


/-! -------------------------------------------------------------------------
B. DFT = original exponential sum
------------------------------------------------------------------------- -/

theorem additiveSumDFTMatch_proved71 :
    AdditiveSumDFTMatch69 := by
  intro T lam hlam
  letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
  intro k
  rw [ZMod.dft_apply]
  change
    (∑ u : ZMod lam,
      ZMod.stdAddChar (-(u * k)) •
        (residueMultiplicityC69 T lam u))
      =
    ∑ z ∈ T, ZMod.stdAddChar (-((z : ZMod lam) * k))
  let g : ℕ → ZMod lam := fun z => ((z % lam : ℕ) : ZMod lam)
  let f : ZMod lam → ℂ := fun u => ZMod.stdAddChar (-(u * k))
  have hmaps : ∀ z ∈ T, g z ∈ (Finset.univ : Finset (ZMod lam)) := by
    intro z hz
    simp
  have hfib :
      (∑ u ∈ (Finset.univ : Finset (ZMod lam)),
          ∑ z ∈ T with g z = u, f u)
        =
      ∑ z ∈ T, f (g z) :=
    Finset.sum_fiberwise_of_maps_to'
      (s := T)
      (t := (Finset.univ : Finset (ZMod lam)))
      (g := g)
      hmaps f
  have hfilter :
      ∀ u : ZMod lam,
        (T.filter (fun z => g z = u)).card
          =
        residueMultiplicity69 T lam u := by
    intro u
    unfold residueMultiplicity69
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro z hzT
    simp only [g]
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      simpa [ZMod.val_natCast_of_lt (Nat.mod_lt z hlam)] using hv
    · intro h
      apply ZMod.val_injective
      simpa [ZMod.val_natCast_of_lt (Nat.mod_lt z hlam)] using h
  have hlocal :
      ∀ u : ZMod lam,
        f u • residueMultiplicityC69 T lam u
          =
        ∑ z ∈ T with g z = u, f u := by
    intro u
    unfold residueMultiplicityC69
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [hfilter u]
    simp [smul_eq_mul, mul_comm]
  calc
    (∑ u : ZMod lam,
      ZMod.stdAddChar (-(u * k)) • residueMultiplicityC69 T lam u)
        =
      ∑ u : ZMod lam,
        ∑ z ∈ T with g z = u, f u := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hlocal u
    _ =
      ∑ z ∈ T, f (g z) := hfib
    _ =
      ∑ z ∈ T, ZMod.stdAddChar (-((z : ZMod lam) * k)) := by
          apply Finset.sum_congr rfl
          intro z hz
          simp only [f, g]
          congr 2
          apply ZMod.val_injective
          simp [ZMod.val_natCast, Nat.mod_mod]


/-! -------------------------------------------------------------------------
C. Natural residue support maps injectively into ZMod
------------------------------------------------------------------------- -/

theorem imageSupport_mod_lt71
    (T : Finset ℕ) {lam u : ℕ} (hlam : 0 < lam)
    (hu : u ∈ imageSupport T (fun z => z % lam)) :
    u < lam := by
  unfold imageSupport at hu
  rcases Finset.mem_image.mp hu with ⟨z, hzT, rfl⟩
  exact Nat.mod_lt _ hlam

theorem natCast_injective_on_modSupport71
    (T : Finset ℕ) {lam : ℕ} (hlam : 0 < lam) :
    Set.InjOn (fun u : ℕ => (u : ZMod lam))
      ↑(imageSupport T (fun z => z % lam)) := by
  intro u hu v hv huv
  have hu' : u < lam :=
    imageSupport_mod_lt71 T hlam (by simpa using hu)
  have hv' : v < lam :=
    imageSupport_mod_lt71 T hlam (by simpa using hv)
  have hval := congrArg ZMod.val huv
  simpa [ZMod.val_natCast_of_lt hu', ZMod.val_natCast_of_lt hv'] using hval

/-! Repair 71 occupied-ZMod support attempt: obsolete failed declaration removed in Repair 112. The later corrected proof spine does not reference it. -/

/-! -------------------------------------------------------------------------
D. Collision bridge reduced to a support-sum identity
------------------------------------------------------------------------- -/

/-! Repair 71 collision-support bridge attempt: obsolete failed declaration removed in Repair 112. The later corrected proof spine does not reference it. -/

/-!
At this point the DFT matching theorem is proved outright.

The collision bridge has been reduced to one finite support-sum identity,
`CollisionSupportCastBridge71`, whose only content is that natural residue
classes `0,...,lam-1` and the corresponding `ZMod lam` classes have the same
fiber cardinalities.

The remaining Fourier core is therefore:
  * CollisionSupportCastBridge71  [finite bookkeeping]
  * FullDFTParseval69             [finite Fourier orthogonality]
-/

-- Historical audit output: #print axioms natCast_eq_iff_mod_eq71
-- Historical audit output: #print axioms residueMultiplicity_cast_eq_natFiber71
-- Historical audit output: #print axioms additiveSumDFTMatch_proved71
-- Historical audit output: #print axioms imageSupport_mod_lt71
-- Historical audit output: #print axioms natCast_injective_on_modSupport71

end RemainingAnalytic71

/-! ## 69. Repair 74: natural-remainder multiplicity

The previous multiplicity definition filtered after coercion into `ZMod`,
which caused Lean to elaborate through an image finset and obscured
multiplicity.  We now define multiplicity canonically by the natural residue:

    m_T(u) = #{z in T : z % lam = u.val}.

This is mathematically identical and aligns exactly with the existing
`fiberCount` / `residueCollisionSum` infrastructure.
-/

namespace RemainingAnalytic74

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic69
open RemainingAnalytic70 RemainingAnalytic71

theorem exactFiber_checkpoint74 :
    ∀ (T : Finset ℕ) {lam u : ℕ} [NeZero lam], u < lam →
      residueMultiplicity69 T lam (u : ZMod lam)
        =
      fiberCount T (fun z => z % lam) u :=
  residueMultiplicity_cast_eq_natFiber71

theorem dftMatch_checkpoint74 :
    AdditiveSumDFTMatch69 :=
  additiveSumDFTMatch_proved71

/-!
If these compile, the DFT regrouping is finished without any image-fiber
ambiguity.

Next finite targets:
  * prove `CollisionSupportCastBridge71` directly from
    `residueMultiplicity_cast_eq_natFiber71`;
  * prove `FullDFTParseval69`.

After those, `AdditiveEnergyIdentity59` is internal finite algebra.
-/

-- Historical audit output: #print axioms residueMultiplicity_cast_eq_natFiber71
-- Historical audit output: #print axioms additiveSumDFTMatch_proved71
-- Historical audit output: #print axioms exactFiber_checkpoint74
-- Historical audit output: #print axioms dftMatch_checkpoint74

end RemainingAnalytic74


/-! ## 70. Repair 75: superseded

The direct support-image collision route was abandoned after elaboration
failures and is removed from the clean spine in Repair 112.  Repair 76
proves the collision bridge by the finite-equivalence route instead. -/

/-! ## 71. Repair 76: direct Fin/ZMod enumeration of collision energy

The support-image route is unnecessary.  Since multiplicity is now defined by
natural remainders, enumerate `ZMod lam` by `Fin lam` and identify each term
directly with the natural fiber count at the representative `u.val`.
-/

namespace RemainingAnalytic76

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic66
open RemainingAnalytic69 RemainingAnalytic70 RemainingAnalytic71
open RemainingAnalytic74

theorem residueMultiplicity_finEquiv76
    (T : Finset ℕ) {lam : ℕ} [NeZero lam] (u : Fin lam) :
    residueMultiplicity69 T lam ((ZMod.finEquiv lam) u)
      =
    fiberCount T (fun z => z % lam) u.val := by
  rw [RemainingAnalytic66.finEquiv_eq_natCast67 u]
  exact residueMultiplicity_cast_eq_natFiber71 T u.isLt

theorem residueCollisionBridge_proved76 :
    ResidueCollisionBridge69 := by
  intro T lam hlam
  letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
  unfold residueCollisionSum
  have hsum :=
    (ZMod.finEquiv lam).toEquiv.sum_comp
      (fun u : ZMod lam => (residueMultiplicity69 T lam u : ℝ) ^ 2)
  calc
    (∑ u : ZMod lam, (residueMultiplicity69 T lam u : ℝ) ^ 2)
        =
      ∑ u : Fin lam,
        (residueMultiplicity69 T lam ((ZMod.finEquiv lam) u) : ℝ) ^ 2 := by
          exact hsum.symm
    _ =
      ∑ u : Fin lam,
        (fiberCount T (fun z => z % lam) u.val : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [residueMultiplicity_finEquiv76 T u]
    _ =
      ∑ u ∈ Finset.range lam,
        (fiberCount T (fun z => z % lam) u : ℝ) ^ 2 := by
          exact (Finset.sum_range
            (fun u : ℕ =>
              (fiberCount T (fun z => z % lam) u : ℝ) ^ 2)).symm
    _ =
      ∑ u ∈ imageSupport T (fun z => z % lam),
        (fiberCount T (fun z => z % lam) u : ℝ) ^ 2 := by
          symm
          apply Finset.sum_subset
          · intro u hu
            rcases Finset.mem_image.mp hu with ⟨z, hzT, rfl⟩
            exact Finset.mem_range.mpr (Nat.mod_lt _ hlam)
          · intro u huRange huNot
            have hzero : fiberCount T (fun z => z % lam) u = 0 := by
              unfold fiberCount
              by_contra hcard
              have hne :
                  (T.filter (fun z => z % lam = u)).Nonempty :=
                Finset.card_ne_zero.mp hcard
              rcases hne with ⟨z, hz⟩
              rw [Finset.mem_filter] at hz
              exact huNot (Finset.mem_image.mpr ⟨z, hz.1, hz.2⟩)
            simp [hzero]

/-!
If this compiles, the entire collision side is internal and the only remaining
finite Fourier theorem is `FullDFTParseval69`.
-/

-- Historical audit output: #print axioms residueMultiplicity_finEquiv76
-- Historical audit output: #print axioms residueCollisionBridge_proved76
-- Historical audit output: #print axioms additiveSumDFTMatch_proved71

end RemainingAnalytic76


/-! ## 72. Repair 77: bridge Fin enumeration to natural range

`Finset.sum_range` is the exact theorem needed to convert the full
`Fin lam` sum to a natural sum over `range lam`.  Once both sides have
natural-number indices, the support restriction is ordinary `sum_subset`.
-/

namespace RemainingAnalytic77

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic69
open RemainingAnalytic70 RemainingAnalytic71 RemainingAnalytic74
open RemainingAnalytic76

theorem collisionBridge_checkpoint77 :
    ResidueCollisionBridge69 :=
  residueCollisionBridge_proved76

/-!
If green, both non-Parseval finite Fourier components are complete:

  * `AdditiveSumDFTMatch69`;
  * `ResidueCollisionBridge69`.

The only remaining finite Fourier theorem is then `FullDFTParseval69`.
-/

-- Historical audit output: #print axioms residueMultiplicity_finEquiv76
-- Historical audit output: #print axioms residueCollisionBridge_proved76
-- Historical audit output: #print axioms collisionBridge_checkpoint77
-- Historical audit output: #print axioms additiveSumDFTMatch_proved71

end RemainingAnalytic77


/-! ## 73. Repair 78: parser-safe range bridge

Repair 77 reached the intended final collision argument but used the binder
spelling `∑ u in Finset.range lam`, while this file/mathlib setup parses the
established notation `∑ u ∈ Finset.range lam`.

No mathematical change is made here.
-/

namespace RemainingAnalytic78

open RemainingAnalytic69 RemainingAnalytic71 RemainingAnalytic76 RemainingAnalytic77

theorem collisionBridge_checkpoint78 :
    ResidueCollisionBridge69 :=
  residueCollisionBridge_proved76

-- Historical audit output: #print axioms residueMultiplicity_finEquiv76
-- Historical audit output: #print axioms residueCollisionBridge_proved76
-- Historical audit output: #print axioms collisionBridge_checkpoint78
-- Historical audit output: #print axioms additiveSumDFTMatch_proved71

end RemainingAnalytic78


/-! ## 74. Repair 79: close the collision bridge

Repair 78 reached the final zero-fiber step.  The only failure was use of an
unavailable theorem name for proving a Finset empty.  We instead argue directly:
if the fiber card were nonzero, `Finset.card_ne_zero.mp` gives a witness,
which immediately places the residue in `imageSupport`, contradicting the
outside-support hypothesis.
-/

namespace RemainingAnalytic79

open RemainingAnalytic69 RemainingAnalytic71 RemainingAnalytic76
open RemainingAnalytic77 RemainingAnalytic78

theorem collisionBridge_checkpoint79 :
    ResidueCollisionBridge69 :=
  residueCollisionBridge_proved76

theorem finiteFourier_nonParseval_complete79 :
    AdditiveSumDFTMatch69 ∧ ResidueCollisionBridge69 :=
  ⟨additiveSumDFTMatch_proved71, residueCollisionBridge_proved76⟩

/-!
If green, the only remaining finite Fourier input is `FullDFTParseval69`.
-/

-- Historical audit output: #print axioms residueMultiplicity_finEquiv76
-- Historical audit output: #print axioms residueCollisionBridge_proved76
-- Historical audit output: #print axioms collisionBridge_checkpoint79
-- Historical audit output: #print axioms finiteFourier_nonParseval_complete79
-- Historical audit output: #print axioms additiveSumDFTMatch_proved71

end RemainingAnalytic79


/-! ## 75. Repair 80: Parseval via the exact additive-character kernel

The two bookkeeping components of the finite Fourier package are now proved.
We attack the final component, Parseval, through the standard orthogonality
kernel.

Mathlib supplies exactly the primitive-character identity we need:
`AddChar.sum_mulShift`, together with `ZMod.isPrimitive_stdAddChar`.
-/

namespace RemainingAnalytic80

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic69
open RemainingAnalytic71 RemainingAnalytic76 RemainingAnalytic79

theorem stdAddCharOrthogonality80
    {lam : ℕ} [NeZero lam] (d : ZMod lam) :
    (∑ k : ZMod lam, ZMod.stdAddChar (k * d))
      =
    if d = 0 then (lam : ℂ) else 0 := by
  have h :=
    AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar lam)
  simpa [ZMod.card] using h

theorem stdAddCharOrthogonality_sub80
    {lam : ℕ} [NeZero lam] (u v : ZMod lam) :
    (∑ k : ZMod lam, ZMod.stdAddChar (k * (v - u)))
      =
    if u = v then (lam : ℂ) else 0 := by
  rw [stdAddCharOrthogonality80]
  by_cases h : u = v
  · subst v
    simp
  · have hne : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    simp [h, hne]

/-- Orthogonality contracts the full quadratic Fourier kernel to the diagonal. -/
theorem parsevalKernelContraction80
    {lam : ℕ} [NeZero lam] (a : ZMod lam → ℝ) :
    (∑ u : ZMod lam,
      ∑ v : ZMod lam,
        ((a u * a v : ℝ) : ℂ) *
          (∑ k : ZMod lam, ZMod.stdAddChar (k * (v - u))))
      =
    (lam : ℂ) * ∑ u : ZMod lam, ((a u)^2 : ℝ) := by
  calc
    (∑ u : ZMod lam,
      ∑ v : ZMod lam,
        ((a u * a v : ℝ) : ℂ) *
          (∑ k : ZMod lam, ZMod.stdAddChar (k * (v - u))))
        =
      ∑ u : ZMod lam,
        (((a u)^2 : ℝ) : ℂ) * (lam : ℂ) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_eq_single u]
          · rw [stdAddCharOrthogonality_sub80 u u]
            simp [pow_two]
          · intro v hv hvu
            rw [stdAddCharOrthogonality_sub80 u v]
            by_cases hEq : u = v
            · exact (hvu hEq.symm).elim
            · simp [hEq]
          · intro huNot
            exact (huNot (Finset.mem_univ u)).elim
    _ =
      (lam : ℂ) * ∑ u : ZMod lam, (((a u)^2 : ℝ) : ℂ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          ring
    _ =
      (lam : ℂ) * ∑ u : ZMod lam, ((a u)^2 : ℝ) := by
          norm_num

/-!
The remaining Parseval task is now isolated to one local expansion:

    sum_k ‖dft Φ k‖^2

must be rewritten as the quadratic kernel above, for real-valued Φ.
For `residueMultiplicityC69`, every Φ(u) is a natural-number cast, so this
is exactly the easiest real-valued case.
-/

def DFTNormKernelExpansion80 : Prop :=
  ∀ T : Finset ℕ, ∀ lam : ℕ, ∀ hlam : 0 < lam,
    letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
    ((∑ k : ZMod lam,
        ‖ZMod.dft (residueMultiplicityC69 T lam) k‖ ^ 2 : ℝ) : ℂ)
      =
    ∑ u : ZMod lam,
      ∑ v : ZMod lam,
        (((residueMultiplicity69 T lam u : ℝ) *
          (residueMultiplicity69 T lam v : ℝ) : ℝ) : ℂ) *
          (∑ k : ZMod lam, ZMod.stdAddChar (k * (v - u)))

theorem fullDFTParseval_from_kernelExpansion80
    (H : DFTNormKernelExpansion80) :
    FullDFTParseval69 := by
  intro T lam hlam
  letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
  have hExp := H T lam hlam
  have hKer :=
    parsevalKernelContraction80
      (fun u : ZMod lam => (residueMultiplicity69 T lam u : ℝ))
  have hcomplex :
      (((∑ k : ZMod lam,
          ‖ZMod.dft (residueMultiplicityC69 T lam) k‖ ^ 2 : ℝ) : ℂ))
        =
      (((lam : ℝ) *
        (∑ u : ZMod lam,
          (residueMultiplicity69 T lam u : ℝ) ^ 2) : ℝ) : ℂ) := by
    rw [hExp, hKer]
    norm_num
  exact_mod_cast hcomplex

-- Historical audit output: #print axioms stdAddCharOrthogonality80
-- Historical audit output: #print axioms stdAddCharOrthogonality_sub80
-- Historical audit output: #print axioms parsevalKernelContraction80
-- Historical audit output: #print axioms fullDFTParseval_from_kernelExpansion80

end RemainingAnalytic80


/-! ## 76. Repair 81: diagonalize the Parseval kernel directly

The additive-character orthogonality lemmas from Repair 80 are green.
The previous kernel-contraction proof failed only because a nested
`sum_congr` was applied after Lean had lost the intended equality goal.

Repair 81 uses `Finset.sum_eq_single` for the inner v-sum.  Orthogonality
kills every off-diagonal term and the diagonal contributes exactly
`lam * a(u)^2`.
-/

namespace RemainingAnalytic81

open RemainingAnalytic69 RemainingAnalytic80

theorem parsevalKernel_checkpoint81
    {lam : ℕ} [NeZero lam] (a : ZMod lam → ℝ) :
    (∑ u : ZMod lam,
      ∑ v : ZMod lam,
        ((a u * a v : ℝ) : ℂ) *
          (∑ k : ZMod lam, ZMod.stdAddChar (k * (v - u))))
      =
    (lam : ℂ) * ∑ u : ZMod lam, ((a u)^2 : ℝ) :=
  parsevalKernelContraction80 a

-- Historical audit output: #print axioms stdAddCharOrthogonality80
-- Historical audit output: #print axioms stdAddCharOrthogonality_sub80
-- Historical audit output: #print axioms parsevalKernelContraction80
-- Historical audit output: #print axioms parsevalKernel_checkpoint81
-- Historical audit output: #print axioms fullDFTParseval_from_kernelExpansion80

end RemainingAnalytic81


/-! ## 77. Repair 82: explicit off-diagonal contradiction

Repair 81 reduced the kernel contraction to one branch where `simp` did not
use the orientation of the disequality hypothesis automatically.  We now split
explicitly on `u = v`; equality contradicts the branch assumption, while
inequality makes the orthogonality factor zero.
-/

namespace RemainingAnalytic82

open RemainingAnalytic69 RemainingAnalytic80 RemainingAnalytic81

theorem parsevalKernel_checkpoint82
    {lam : ℕ} [NeZero lam] (a : ZMod lam → ℝ) :
    (∑ u : ZMod lam,
      ∑ v : ZMod lam,
        ((a u * a v : ℝ) : ℂ) *
          (∑ k : ZMod lam, ZMod.stdAddChar (k * (v - u))))
      =
    (lam : ℂ) * ∑ u : ZMod lam, ((a u)^2 : ℝ) :=
  parsevalKernelContraction80 a

-- Historical audit output: #print axioms stdAddCharOrthogonality80
-- Historical audit output: #print axioms stdAddCharOrthogonality_sub80
-- Historical audit output: #print axioms parsevalKernelContraction80
-- Historical audit output: #print axioms parsevalKernel_checkpoint82
-- Historical audit output: #print axioms fullDFTParseval_from_kernelExpansion80

end RemainingAnalytic82


/-! ## 78. Repair 83: expand the DFT norm square

Repair 82 closes the orthogonality/contraction half of Parseval.  The only
remaining finite Fourier identity is the direct norm expansion.

We first isolate conjugation of the standard additive character, then expand
`normSq` as `star z * z`, distribute over the finite DFT sums, and commute
the finite sums into the quadratic kernel already handled above.
-/

namespace RemainingAnalytic83

open scoped BigOperators
open RemainingAnalytic59 RemainingAnalytic69 RemainingAnalytic71
open RemainingAnalytic80 RemainingAnalytic82

theorem star_stdAddChar83
    {lam : ℕ} [NeZero lam] (x : ZMod lam) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply]
  have hneg :
      ZMod.toCircle (-x) = (ZMod.toCircle x)⁻¹ :=
    AddChar.map_neg_eq_inv (ZMod.toCircle) x
  rw [hneg]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm

theorem star_natCast_complex83 (n : ℕ) :
    star (n : ℂ) = (n : ℂ) := by
  simp

theorem star_residueMultiplicityC83
    (T : Finset ℕ) {lam : ℕ} [NeZero lam] (u : ZMod lam) :
    star (residueMultiplicityC69 T lam u)
      = residueMultiplicityC69 T lam u := by
  unfold residueMultiplicityC69
  simp

theorem dftNormSq_expand83
    (T : Finset ℕ) {lam : ℕ} [NeZero lam] (k : ZMod lam) :
    ((‖ZMod.dft (residueMultiplicityC69 T lam) k‖ ^ 2 : ℝ) : ℂ)
      =
    ∑ u : ZMod lam,
      ∑ v : ZMod lam,
        (((residueMultiplicity69 T lam u : ℝ) *
          (residueMultiplicity69 T lam v : ℝ) : ℝ) : ℂ) *
          ZMod.stdAddChar (k * (u - v)) := by
  rw [Complex.sq_norm]
  rw [Complex.normSq_eq_conj_mul_self]
  rw [ZMod.dft_apply]
  simp only [map_sum, starRingEnd_apply, smul_eq_mul, star_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [star_residueMultiplicityC83 T u]
  rw [star_stdAddChar83]
  unfold residueMultiplicityC69
  calc
    ((residueMultiplicity69 T lam u : ℂ) *
        ZMod.stdAddChar (-(-(u * k)))) *
      (ZMod.stdAddChar (-(v * k)) *
        (residueMultiplicity69 T lam v : ℂ))
        =
      (((residueMultiplicity69 T lam u : ℂ) *
        (residueMultiplicity69 T lam v : ℂ)) *
        (ZMod.stdAddChar (-(-(u * k))) *
          ZMod.stdAddChar (-(v * k)))) := by
            ring
    _ =
      (((residueMultiplicity69 T lam u : ℂ) *
        (residueMultiplicity69 T lam v : ℂ)) *
        ZMod.stdAddChar
          (-(-(u * k)) + -(v * k))) := by
            rw [← AddChar.map_add_eq_mul]
    _ =
      (((residueMultiplicity69 T lam u : ℂ) *
        (residueMultiplicity69 T lam v : ℂ)) *
        ZMod.stdAddChar (k * (u - v))) := by
            congr 2
            ring
    _ =
      (((residueMultiplicity69 T lam u : ℝ) *
        (residueMultiplicity69 T lam v : ℝ) : ℝ) : ℂ) *
        ZMod.stdAddChar (k * (u - v)) := by
            norm_num

theorem dftNormKernelExpansion_proved83 :
    DFTNormKernelExpansion80 := by
  intro T lam hlam
  letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
  calc
    (((∑ k : ZMod lam,
        ‖ZMod.dft (residueMultiplicityC69 T lam) k‖ ^ 2 : ℝ) : ℂ))
        =
      ∑ k : ZMod lam,
        ∑ u : ZMod lam,
          ∑ v : ZMod lam,
            (((residueMultiplicity69 T lam u : ℝ) *
              (residueMultiplicity69 T lam v : ℝ) : ℝ) : ℂ) *
              ZMod.stdAddChar (k * (u - v)) := by
          norm_num
          apply Finset.sum_congr rfl
          intro k hk
          simpa using (dftNormSq_expand83 T k)
    _ =
      ∑ u : ZMod lam,
        ∑ v : ZMod lam,
          ∑ k : ZMod lam,
            (((residueMultiplicity69 T lam u : ℝ) *
              (residueMultiplicity69 T lam v : ℝ) : ℝ) : ℂ) *
              ZMod.stdAddChar (k * (u - v)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
    _ =
      ∑ u : ZMod lam,
        ∑ v : ZMod lam,
          (((residueMultiplicity69 T lam u : ℝ) *
            (residueMultiplicity69 T lam v : ℝ) : ℝ) : ℂ) *
            (∑ k : ZMod lam, ZMod.stdAddChar (k * (u - v))) := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.mul_sum]
    _ =
      ∑ u : ZMod lam,
        ∑ v : ZMod lam,
          (((residueMultiplicity69 T lam u : ℝ) *
            (residueMultiplicity69 T lam v : ℝ) : ℝ) : ℂ) *
            (∑ k : ZMod lam, ZMod.stdAddChar (k * (v - u))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro u hu
          -- After exchanging the dummy indices, only coefficient commutativity remains.
          simp only [mul_comm]

theorem fullDFTParseval_proved83 :
    FullDFTParseval69 :=
  fullDFTParseval_from_kernelExpansion80
    dftNormKernelExpansion_proved83

/-!
If all checkpoints below are green, the entire finite Fourier identity package
used to derive `AdditiveEnergyIdentity59` is kernel-checked:

  * DFT matching;
  * collision-energy matching;
  * full DFT Parseval.

The next step is then to derive `AdditiveEnergyIdentity59` by separating the
zero Fourier mode from the nonzero modes.
-/

-- Historical audit output: #print axioms star_stdAddChar83
-- Historical audit output: #print axioms star_residueMultiplicityC83
-- Historical audit output: #print axioms dftNormSq_expand83
-- Historical audit output: #print axioms dftNormKernelExpansion_proved83
-- Historical audit output: #print axioms fullDFTParseval_proved83

end RemainingAnalytic83


/-! ## 79. Repair 84: API-correct conjugation and scalar normalization

Repair 83 confirmed the full Parseval architecture but exposed three local
Lean API issues.  This repair:

* proves character conjugation through `Circle.coe_inv_eq_conj`;
* rewrites complex scalar multiplication to ordinary multiplication before
  applying `star_mul`;
* uses `simpa` for the harmless real/complex cast normalization in the outer
  finite sum.
-/

namespace RemainingAnalytic84

open RemainingAnalytic69 RemainingAnalytic80 RemainingAnalytic83

theorem parsevalExpansion_checkpoint84 :
    DFTNormKernelExpansion80 :=
  dftNormKernelExpansion_proved83

theorem fullParseval_checkpoint84 :
    FullDFTParseval69 :=
  fullDFTParseval_proved83

-- Historical audit output: #print axioms star_stdAddChar83
-- Historical audit output: #print axioms star_residueMultiplicityC83
-- Historical audit output: #print axioms dftNormSq_expand83
-- Historical audit output: #print axioms dftNormKernelExpansion_proved83
-- Historical audit output: #print axioms fullDFTParseval_proved83
-- Historical audit output: #print axioms parsevalExpansion_checkpoint84
-- Historical audit output: #print axioms fullParseval_checkpoint84

end RemainingAnalytic84


/-! ## 80. Repair 85: natural phase orientation and dummy-index swap

The DFT norm expansion from `conj(z) * z` naturally carries phase `u - v`.
The existing Parseval kernel interface uses `v - u`.  These are not
termwise equal; the correct bridge is to swap the dummy indices `u` and `v`
in the full symmetric double sum.

This repair also proves character conjugation using
`AddChar.map_neg_eq_inv` directly, avoiding brittle unfolding through the
Circle implementation.
-/

namespace RemainingAnalytic85

open RemainingAnalytic69 RemainingAnalytic80 RemainingAnalytic83 RemainingAnalytic84

theorem parsevalExpansion_checkpoint85 :
    DFTNormKernelExpansion80 :=
  dftNormKernelExpansion_proved83

theorem fullParseval_checkpoint85 :
    FullDFTParseval69 :=
  fullDFTParseval_proved83

-- Historical audit output: #print axioms star_stdAddChar83
-- Historical audit output: #print axioms star_residueMultiplicityC83
-- Historical audit output: #print axioms dftNormSq_expand83
-- Historical audit output: #print axioms dftNormKernelExpansion_proved83
-- Historical audit output: #print axioms fullDFTParseval_proved83
-- Historical audit output: #print axioms parsevalExpansion_checkpoint85
-- Historical audit output: #print axioms fullParseval_checkpoint85

end RemainingAnalytic85


/-! ## 81. Repair 86: explicit character regrouping and termwise phase normalization

Repair 85 leaves only two algebraic elaboration issues.

1. Regroup the complex coefficient factors and the two additive-character
   factors before invoking `map_add`.
2. In the dummy-index swap, normalize the character argument term-by-term
   (`k*u - k*v = u*k - v*k`) rather than asking `ring` to rewrite through
   the opaque character map.

No new mathematical input is introduced.
-/

namespace RemainingAnalytic86

open RemainingAnalytic69 RemainingAnalytic80 RemainingAnalytic83
open RemainingAnalytic84 RemainingAnalytic85

theorem parsevalExpansion_checkpoint86 :
    DFTNormKernelExpansion80 :=
  dftNormKernelExpansion_proved83

theorem fullParseval_checkpoint86 :
    FullDFTParseval69 :=
  fullDFTParseval_proved83

-- Historical audit output: #print axioms star_stdAddChar83
-- Historical audit output: #print axioms star_residueMultiplicityC83
-- Historical audit output: #print axioms dftNormSq_expand83
-- Historical audit output: #print axioms dftNormKernelExpansion_proved83
-- Historical audit output: #print axioms fullDFTParseval_proved83
-- Historical audit output: #print axioms parsevalExpansion_checkpoint86
-- Historical audit output: #print axioms fullParseval_checkpoint86

end RemainingAnalytic86


/-! ## 82. Repair 87: close Parseval algebra

Repair 86 exposed two final elaboration mistakes, not mathematical gaps.

* Additive characters use `AddChar.map_add_eq_mul`, not generic `map_add`.
* After swapping the dummy indices, coefficient commutativity and the
  character-sum argument normalization are proved separately.

If the checkpoints below are green, `FullDFTParseval69` is fully internal.
-/

namespace RemainingAnalytic87

open RemainingAnalytic69 RemainingAnalytic80 RemainingAnalytic83
open RemainingAnalytic84 RemainingAnalytic85 RemainingAnalytic86

theorem parsevalExpansion_checkpoint87 :
    DFTNormKernelExpansion80 :=
  dftNormKernelExpansion_proved83

theorem fullParseval_checkpoint87 :
    FullDFTParseval69 :=
  fullDFTParseval_proved83

-- Historical audit output: #print axioms star_stdAddChar83
-- Historical audit output: #print axioms star_residueMultiplicityC83
-- Historical audit output: #print axioms dftNormSq_expand83
-- Historical audit output: #print axioms dftNormKernelExpansion_proved83
-- Historical audit output: #print axioms fullDFTParseval_proved83
-- Historical audit output: #print axioms parsevalExpansion_checkpoint87
-- Historical audit output: #print axioms fullParseval_checkpoint87

end RemainingAnalytic87


/-! ## 83. Repair 88: close the finite Fourier energy identity

Repairs 71, 76, and 83--87 have now proved the three finite Fourier ingredients:

* DFT of the residue multiplicity profile equals the original exponential sum;
* Parseval for the full ZMod DFT;
* the ZMod multiplicity square-sum equals the natural residue collision sum.

The only remaining step in `AdditiveEnergyIdentity59` is to remove the zero
Fourier mode.  That mode is exactly `T.card`, so its squared norm is
`(T.card : ℝ)^2`.
-/

namespace RemainingAnalytic88

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic69
open RemainingAnalytic71 RemainingAnalytic76 RemainingAnalytic83
open RemainingAnalytic87

/-- A generic finite-sum identity: deleting one distinguished term is the same
as summing the `if x = z then 0 else f x` function. -/
theorem sum_if_eq_zero_else88
    {α : Type*} [Fintype α] [DecidableEq α]
    (z : α) (f : α → ℝ) :
    (∑ x : α, if x = z then 0 else f x)
      =
    ∑ x ∈ (Finset.univ.erase z), f x := by
  symm
  calc
    (∑ x ∈ (Finset.univ.erase z), f x)
        =
      ∑ x ∈ Finset.univ,
        if x ≠ z then f x else 0 := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext x
            simp
          · intro x hx
            rfl
    _ =
      ∑ x : α, if x = z then 0 else f x := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : x = z <;> simp [h]

/-- The full sum splits as the nonzero-frequency sum plus the zero mode. -/
theorem sum_if_ne_zero_add_zero_mode88
    {α : Type*} [Fintype α] [DecidableEq α]
    (z : α) (f : α → ℝ) :
    (∑ x : α, if x = z then 0 else f x) + f z
      =
    ∑ x : α, f x := by
  calc
    (∑ x : α, if x = z then 0 else f x) + f z
        =
      (∑ x ∈ (Finset.univ.erase z), f x) + f z := by
        rw [sum_if_eq_zero_else88 z f]
    _ =
      ∑ x : α, f x := by
        exact Finset.sum_erase_add
          Finset.univ f (Finset.mem_univ z)

/-- At zero frequency the DFT/exponential sum is exactly the cardinality of T. -/
theorem dft_zero_norm_sq88
    (T : Finset ℕ) {lam : ℕ} (hlam : 0 < lam) :
    letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
    ‖ZMod.dft (residueMultiplicityC69 T lam) (0 : ZMod lam)‖ ^ 2
      =
    (T.card : ℝ) ^ 2 := by
  letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
  have hmatch :=
    additiveSumDFTMatch_proved71 T lam hlam (0 : ZMod lam)
  rw [hmatch]
  simp

/-- The finite Fourier package proves the exact collision-form energy identity
used underneath the standard additive large sieve. -/
theorem additiveEnergyIdentity_proved88 :
    AdditiveEnergyIdentity59 := by
  intro T lam hlam
  letI : NeZero lam := ⟨Nat.ne_of_gt hlam⟩
  have hParseval :=
    fullDFTParseval_proved83 T lam hlam
  have hCollision :=
    residueCollisionBridge_proved76 T lam hlam
  have hZero := dft_zero_norm_sq88 T hlam
  have hSplit :=
    sum_if_ne_zero_add_zero_mode88
      (0 : ZMod lam)
      (fun k : ZMod lam =>
        ‖ZMod.dft (residueMultiplicityC69 T lam) k‖ ^ 2)
  have hMatch :
      (∑ k : ZMod lam,
        if k = 0 then 0 else
          ‖∑ z ∈ T,
            ZMod.stdAddChar (-((z : ZMod lam) * k))‖ ^ 2)
        =
      ∑ k : ZMod lam,
        if k = 0 then 0 else
          ‖ZMod.dft (residueMultiplicityC69 T lam) k‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · simp only [hk0, ↓reduceIte]
      rw [additiveSumDFTMatch_proved71 T lam hlam k]
  have hlam0 : lam ≠ 0 := Nat.ne_of_gt hlam
  simp [additiveFourierEnergy59, hlam0]
  rw [hMatch]
  unfold residueEnergy
  rw [← hCollision]
  nlinarith

theorem exactFourierPackage_proved88 :
    ExactFourierPackage69 :=
  ⟨fullDFTParseval_proved83,
    additiveSumDFTMatch_proved71,
    residueCollisionBridge_proved76⟩

/-- Consequently the large-sieve energy interface is now reduced to the
standard additive large sieve theorem alone. -/
theorem analyticLargeSieveEnergy_from_only_standard88
    (hLS : StandardAdditiveLargeSieve59) :
    AnalyticLargeSieveEnergyUpper :=
  analyticLargeSieveEnergy_from_standard59
    additiveEnergyIdentity_proved88 hLS

-- Historical audit output: #print axioms dft_zero_norm_sq88
-- Historical audit output: #print axioms additiveEnergyIdentity_proved88
-- Historical audit output: #print axioms exactFourierPackage_proved88
-- Historical audit output: #print axioms analyticLargeSieveEnergy_from_only_standard88

end RemainingAnalytic88


/-! ## 84. Repair 89: close the additive Fourier energy identity

Repair 88 left only two API/elaboration issues:

* `Finset.sum_erase_add` takes the summand function before the membership proof;
* `additiveFourierEnergy59` contains a dependent `if`, because its nonzero
  branch installs the `NeZero lam` instance.

The finite Fourier mathematics itself is already complete.
-/

namespace RemainingAnalytic89

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic69
open RemainingAnalytic71 RemainingAnalytic76 RemainingAnalytic83
open RemainingAnalytic87 RemainingAnalytic88

theorem additiveEnergyIdentity_checkpoint89 :
    AdditiveEnergyIdentity59 :=
  additiveEnergyIdentity_proved88

theorem analyticLargeSieveEnergy_from_only_standard_checkpoint89
    (hLS : StandardAdditiveLargeSieve59) :
    AnalyticLargeSieveEnergyUpper :=
  analyticLargeSieveEnergy_from_only_standard88 hLS

-- Historical audit output: #print axioms dft_zero_norm_sq88
-- Historical audit output: #print axioms additiveEnergyIdentity_proved88
-- Historical audit output: #print axioms exactFourierPackage_proved88
-- Historical audit output: #print axioms additiveEnergyIdentity_checkpoint89
-- Historical audit output: #print axioms analyticLargeSieveEnergy_from_only_standard88
-- Historical audit output: #print axioms analyticLargeSieveEnergy_from_only_standard_checkpoint89

end RemainingAnalytic89


/-! ## 85. Repair 90: avoid the ambiguous erase-sum API

Repair 89 confirmed that the only remaining obstruction is the exact argument
order of `Finset.sum_erase_add` in the browser mathlib version.  We bypass that
API completely and split `univ` into `{z}` plus `univ \ {z}` using
`Finset.sum_eq_add_sum_diff_singleton`.
-/

namespace RemainingAnalytic90

open RemainingAnalytic59 RemainingAnalytic88 RemainingAnalytic89

theorem additiveEnergyIdentity_checkpoint90 :
    AdditiveEnergyIdentity59 :=
  additiveEnergyIdentity_proved88

theorem analyticLargeSieveEnergy_from_only_standard_checkpoint90
    (hLS : StandardAdditiveLargeSieve59) :
    RemainingAnalytic37.AnalyticLargeSieveEnergyUpper :=
  analyticLargeSieveEnergy_from_only_standard88 hLS

-- Historical audit output: #print axioms additiveEnergyIdentity_proved88
-- Historical audit output: #print axioms additiveEnergyIdentity_checkpoint90
-- Historical audit output: #print axioms analyticLargeSieveEnergy_from_only_standard88
-- Historical audit output: #print axioms analyticLargeSieveEnergy_from_only_standard_checkpoint90

end RemainingAnalytic90


/-! ## 86. Repair 91: exact `sum_erase_add` signature

The browser compiler errors from Repairs 88--90 determine the current mathlib
signature unambiguously:

`Finset.sum_erase_add s f ha`

with `s` the finset, `f` the summand, and `ha : a ∈ s`.

This repair uses that exact signature and fully qualifies the downstream
large-sieve target type.
-/

namespace RemainingAnalytic91

open RemainingAnalytic37 RemainingAnalytic59
open RemainingAnalytic88 RemainingAnalytic89 RemainingAnalytic90

theorem additiveEnergyIdentity_checkpoint91 :
    AdditiveEnergyIdentity59 :=
  additiveEnergyIdentity_proved88

theorem analyticLargeSieveEnergy_from_only_standard_checkpoint91
    (hLS : StandardAdditiveLargeSieve59) :
    RemainingAnalytic37.AnalyticLargeSieveEnergyUpper :=
  analyticLargeSieveEnergy_from_only_standard88 hLS

-- Historical audit output: #print axioms additiveEnergyIdentity_proved88
-- Historical audit output: #print axioms additiveEnergyIdentity_checkpoint91
-- Historical audit output: #print axioms analyticLargeSieveEnergy_from_only_standard88
-- Historical audit output: #print axioms analyticLargeSieveEnergy_from_only_standard_checkpoint91

end RemainingAnalytic91


/-! ## 87. Repair 92: reduce the remaining energy estimate to the textbook
prime-modulus additive large sieve

Repair 91 closes all finite Fourier algebra.  The remaining energy estimate
should therefore be stated at a genuinely standard analytic boundary.

The classical large sieve says, in particular, that for any finite collection
`S` of prime moduli bounded by a real parameter `Q`, summing all nonzero
additive Fourier modes over those moduli costs at most

    C * (N + Q^2) * |T|

for `T ⊆ [1,N]`.

This formulation is independent of the anchor construction and of the
sqrt-band chosen in Proposition 5.1.
-/

namespace RemainingAnalytic92

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59
open RemainingAnalytic88 RemainingAnalytic91

/-- Textbook prime-modulus additive large sieve, isolated as the genuinely
analytic theorem.  The constant is absolute. -/
def ClassicalPrimeAdditiveLargeSieve92 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∀ Q : ℝ, 1 ≤ Q →
      ∀ S : Finset ℕ,
        (∀ q : ℕ, q ∈ S → q.Prime ∧ (q : ℝ) ≤ Q) →
        ∀ T : Finset ℕ, T ⊆ Finset.Icc 1 N →
          (∑ q ∈ S, additiveFourierEnergy59 T q)
            ≤ C * ((N : ℝ) + Q ^ 2) * (T.card : ℝ)

/-- Every auxiliary modulus lies below the classical large-sieve cutoff
`2 sqrt L`. -/
theorem auxiliaryPrime_le_sqrtCutoff92
    {L q : ℕ} (hq : q ∈ auxiliaryPrimes L) :
    q.Prime ∧ (q : ℝ) ≤ 2 * Real.sqrt (L : ℝ) := by
  exact ⟨(Finset.mem_filter.mp hq).2.1,
    (Finset.mem_filter.mp hq).2.2.2⟩

/-- For `L ≥ 1`, the cutoff `2 sqrt L` is at least one. -/
theorem one_le_two_sqrt92 {L : ℕ} (hL : 1 ≤ L) :
    (1 : ℝ) ≤ 2 * Real.sqrt (L : ℝ) := by
  have hLreal : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (L : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (L : ℝ) by positivity),
      Real.sqrt_nonneg (L : ℝ)]
  nlinarith

/-- At the sqrt scale, the classical factor `L + Q^2` is exactly `5L`. -/
theorem sqrtScale_cost92 (L : ℕ) :
    (L : ℝ) + (2 * Real.sqrt (L : ℝ)) ^ 2 = 5 * (L : ℝ) := by
  have hnonneg : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [mul_pow, Real.sq_sqrt hnonneg]
  ring

/-- The textbook large sieve immediately gives the exact specialized theorem
used by Repair 59.  No Fourier identity remains in this reduction. -/
theorem standardAdditiveLargeSieve_from_classical92
    (hCLS : ClassicalPrimeAdditiveLargeSieve92) :
    StandardAdditiveLargeSieve59 := by
  obtain ⟨C, hC, hLS⟩ := hCLS
  refine ⟨5 * C, by positivity, 1, ?_⟩
  intro L hL T hT
  have hQ : (1 : ℝ) ≤ 2 * Real.sqrt (L : ℝ) :=
    one_le_two_sqrt92 hL
  have hband :=
    hLS L (2 * Real.sqrt (L : ℝ)) hQ
      (auxiliaryPrimes L)
      (fun q hq => auxiliaryPrime_le_sqrtCutoff92 hq)
      T hT
  rw [sqrtScale_cost92] at hband
  nlinarith

/-- Hence the whole `AnalyticLargeSieveEnergyUpper` interface is now reduced
to the single textbook large-sieve theorem. -/
theorem analyticLargeSieveEnergy_from_classical92
    (hCLS : ClassicalPrimeAdditiveLargeSieve92) :
    RemainingAnalytic37.AnalyticLargeSieveEnergyUpper :=
  analyticLargeSieveEnergy_from_only_standard88
    (standardAdditiveLargeSieve_from_classical92 hCLS)

-- Historical audit output: #print axioms auxiliaryPrime_le_sqrtCutoff92
-- Historical audit output: #print axioms one_le_two_sqrt92
-- Historical audit output: #print axioms sqrtScale_cost92
-- Historical audit output: #print axioms standardAdditiveLargeSieve_from_classical92
-- Historical audit output: #print axioms analyticLargeSieveEnergy_from_classical92

end RemainingAnalytic92


/-! ## 88. Repair 93: reduce dyadic prime supply to a Chebyshev theta gap

The remaining auxiliary-prime supply only needs a lower bound of order
`n / log n` for primes in `(n,2n]`.  A standard Chebyshev formulation is
stronger and cleaner:

    sum_{n < p <= 2n} log p >= c n.

Since every such prime satisfies `log p <= log(2n)`, this immediately yields
the desired cardinality lower bound after the elementary comparison
`log(2n) <= 2 log n` for large `n`.
-/

namespace RemainingAnalytic93

open scoped BigOperators
open RemainingAnalytic59

noncomputable def dyadicTheta93 (n : ℕ) : ℝ :=
  ∑ p ∈ dyadicPrimes59 n, Real.log (p : ℝ)

/-- Standard Chebyshev theta-gap input on a dyadic interval. -/
def ChebyshevDyadicThetaGap93 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * (n : ℝ) ≤ dyadicTheta93 n

theorem dyadicPrime_log_le93
    {n p : ℕ} (hp : p ∈ dyadicPrimes59 n) :
    Real.log (p : ℝ) ≤ Real.log (2 * n : ℕ) := by
  have hpRaw : (n < p ∧ p ≤ 2 * n) ∧ p.Prime := by
    simpa [dyadicPrimes59] using hp
  have hpIcc : p ∈ Finset.Icc (n + 1) (2 * n) := by
    rw [Finset.mem_Icc]
    omega
  have hp_le : p ≤ 2 * n := (Finset.mem_Icc.mp hpIcc).2
  have hp_pos : 0 < p := by
    have : n + 1 ≤ p := (Finset.mem_Icc.mp hpIcc).1
    omega
  exact Real.log_le_log (by exact_mod_cast hp_pos) (by exact_mod_cast hp_le)

theorem dyadicTheta_le_card_mul_log93 (n : ℕ) :
    dyadicTheta93 n
      ≤ ((dyadicPrimes59 n).card : ℝ) * Real.log (2 * n : ℕ) := by
  unfold dyadicTheta93
  calc
    (∑ p ∈ dyadicPrimes59 n, Real.log (p : ℝ))
        ≤ ∑ p ∈ dyadicPrimes59 n, Real.log (2 * n : ℕ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact dyadicPrime_log_le93 hp
    _ = ((dyadicPrimes59 n).card : ℝ) * Real.log (2 * n : ℕ) := by
          simp [mul_comm]

/-- Elementary large-n logarithm comparison. -/
theorem log_two_mul_le_two_log93 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.log (2 * n : ℕ) ≤ 2 * Real.log (n : ℝ) := by
  refine ⟨2, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have htwo_le_n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2_le : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) htwo_le_n
  rw [show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnpos)]
  nlinarith

/-- A positive dyadic theta gap implies the exact `DyadicPrimeLower59`
required by the Proposition 5.1 auxiliary-prime supply. -/
theorem dyadicPrimeLower_from_thetaGap93
    (hTheta : ChebyshevDyadicThetaGap93) :
    DyadicPrimeLower59 := by
  obtain ⟨c, hc, Ntheta, htheta⟩ := hTheta
  obtain ⟨Nlog, hlog⟩ := log_two_mul_le_two_log93
  refine ⟨c / 2, by positivity, max (max Ntheta Nlog) 2, ?_⟩
  intro n hn
  have hnTheta : Ntheta ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hnLog : Nlog ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn2 : 2 ≤ n := le_trans (le_max_right (max Ntheta Nlog) 2) hn
  have hthetaLower := htheta n hnTheta
  have hthetaUpper := dyadicTheta_le_card_mul_log93 n
  have hlogUpper := hlog n hnLog
  have hlogpos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hcard_nonneg : 0 ≤ ((dyadicPrimes59 n).card : ℝ) := by positivity
  have hmul :
      ((dyadicPrimes59 n).card : ℝ) * Real.log (2 * n : ℕ)
        ≤ ((dyadicPrimes59 n).card : ℝ) * (2 * Real.log (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hlogUpper hcard_nonneg
  have hcore :
      c * (n : ℝ)
        ≤ ((dyadicPrimes59 n).card : ℝ) * (2 * Real.log (n : ℝ)) := by
    linarith
  have hdiv :
      (c / 2) * (n : ℝ) / Real.log (n : ℝ)
        ≤ ((dyadicPrimes59 n).card : ℝ) := by
    apply (div_le_iff₀ hlogpos).2
    nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Therefore the original auxiliary-prime supply reduces to the standard
Chebyshev dyadic theta gap. -/
theorem auxiliaryPrimeSupply_from_thetaGap93
    (hTheta : ChebyshevDyadicThetaGap93) :
    RemainingAnalytic37.AuxiliaryPrimeSupply :=
  auxiliaryPrimeSupply_from_dyadic59
    (dyadicPrimeLower_from_thetaGap93 hTheta)

-- Historical audit output: #print axioms dyadicPrime_log_le93
-- Historical audit output: #print axioms dyadicTheta_le_card_mul_log93
-- Historical audit output: #print axioms log_two_mul_le_two_log93
-- Historical audit output: #print axioms dyadicPrimeLower_from_thetaGap93
-- Historical audit output: #print axioms auxiliaryPrimeSupply_from_thetaGap93

end RemainingAnalytic93


/-! ## 89. Repair 94: recover dyadic interval bounds explicitly

Repair 93's only failure was elaborational: after simplification, membership
in the interval appeared as `List.Mem`, so field projection on the proof was
invalid.  We restore the explicit `Finset.Icc` membership proposition first,
then extract the upper endpoint with `Finset.mem_Icc`.
-/

namespace RemainingAnalytic94

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic93

theorem dyadicPrimeLower_from_thetaGap_checkpoint94
    (hTheta : ChebyshevDyadicThetaGap93) :
    DyadicPrimeLower59 :=
  dyadicPrimeLower_from_thetaGap93 hTheta

theorem auxiliaryPrimeSupply_from_thetaGap_checkpoint94
    (hTheta : ChebyshevDyadicThetaGap93) :
    AuxiliaryPrimeSupply :=
  auxiliaryPrimeSupply_from_thetaGap93 hTheta

-- Historical audit output: #print axioms dyadicPrime_log_le93
-- Historical audit output: #print axioms dyadicTheta_le_card_mul_log93
-- Historical audit output: #print axioms log_two_mul_le_two_log93
-- Historical audit output: #print axioms dyadicPrimeLower_from_thetaGap93
-- Historical audit output: #print axioms auxiliaryPrimeSupply_from_thetaGap93
-- Historical audit output: #print axioms dyadicPrimeLower_from_thetaGap_checkpoint94
-- Historical audit output: #print axioms auxiliaryPrimeSupply_from_thetaGap_checkpoint94

end RemainingAnalytic94


/-! ## 90. Repair 95: close the Chebyshev prime-supply reduction

Repair 94 revealed that simplification of membership in `dyadicPrimes59 n`
produces the conjunction

    ((n < p) ∧ (p ≤ 2*n)) ∧ p.Prime.

This repair destructures that conjunction explicitly and reconstructs
`Finset.Icc (n+1) (2*n)` membership with `omega`.
-/

namespace RemainingAnalytic95

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic93 RemainingAnalytic94

theorem dyadicPrimeLower_from_thetaGap_checkpoint95
    (hTheta : ChebyshevDyadicThetaGap93) :
    DyadicPrimeLower59 :=
  dyadicPrimeLower_from_thetaGap93 hTheta

theorem auxiliaryPrimeSupply_from_thetaGap_checkpoint95
    (hTheta : ChebyshevDyadicThetaGap93) :
    AuxiliaryPrimeSupply :=
  auxiliaryPrimeSupply_from_thetaGap93 hTheta

-- Historical audit output: #print axioms dyadicPrime_log_le93
-- Historical audit output: #print axioms dyadicTheta_le_card_mul_log93
-- Historical audit output: #print axioms log_two_mul_le_two_log93
-- Historical audit output: #print axioms dyadicPrimeLower_from_thetaGap93
-- Historical audit output: #print axioms auxiliaryPrimeSupply_from_thetaGap93
-- Historical audit output: #print axioms dyadicPrimeLower_from_thetaGap_checkpoint95
-- Historical audit output: #print axioms auxiliaryPrimeSupply_from_thetaGap_checkpoint95

end RemainingAnalytic95


/-! ## 91. Repair 96: reduce the specialized anchor Weil input to a
generic two-family linear-product Weil theorem

All elementary finite-field bookkeeping is already closed.  The remaining
`AnchorQuadraticWeil59` estimate depends on the anchor only through the fact
that its value is

    c * Π_i (r*z-i) * Π_v (j*z+t-v)

with a nonzero scalar `c`.

We therefore isolate a theorem that no longer mentions `a`, `q(a)`, or the
factorial problem at all.
-/

namespace RemainingAnalytic96

open scoped BigOperators
open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic61
open RemainingAnalytic62 RemainingAnalytic65

noncomputable def linearProductQuadraticSum96
    (lam : ℕ) (hp : lam.Prime) (c : ZMod lam) (r j t h ell : ℕ) : ℤ := by
  letI : Fact lam.Prime := ⟨hp⟩
  exact
    ∑ z : ZMod lam,
      quadraticCharValue62 lam
        (c *
          anchorIProduct61 r ell lam z *
          anchorVProduct61 j t h lam z)

/-- Standard finite-field boundary: quadratic-character cancellation for a
nonzero scalar times the displayed product of two families of distinct linear
forms.  The deliberately loose constant `2 * max h ell` is exactly what the
manuscript needs. -/
def ClassicalLinearProductQuadraticWeil96 : Prop :=
  ∀ r j t h ell lam : ℕ,
    0 < j → j < r → 0 < h → 0 < ell → t < h →
    (h ≠ 1 ∨ ell ≠ 1) →
    ∀ hp : lam.Prime,
    2 * r * max h ell < lam →
    ∀ c : ZMod lam, c ≠ 0 →
      |((linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)|
        ≤ 2 * (max h ell : ℝ) * Real.sqrt (lam : ℝ)

/-- At a prime modulus, the concrete anchor quadratic sum is exactly the
generic linear-product sum with scalar equal to the anchor leading
coefficient. -/
theorem anchorQuadraticSum_eq_linearProduct96
    {a r j t h ell lam : ℕ}
    (hp : lam.Prime) :
    AnchorQuadraticSum59 a r j t h ell lam =
      linearProductQuadraticSum96
        lam hp (anchorLeadingCoeff61 a r j lam) r j t h ell := by
  letI : Fact lam.Prime := ⟨hp⟩
  unfold AnchorQuadraticSum59 linearProductQuadraticSum96
  simp only [hp, dite_true]
  apply Finset.sum_congr rfl
  intro z hz
  rw [quadraticCharValue_of_prime62 hp]
  rw [anchorEvalMod_factorization61]

/-- The generic linear-product Weil theorem implies the exact anchor theorem.
The only anchor-specific fact used is the already-proved nonvanishing of the
leading scalar modulo the auxiliary prime. -/
theorem anchorQuadraticWeil_from_linearProduct96
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    AnchorQuadraticWeil59 := by
  intro a r j t h ell lam hj hjr hh hell ht hnp hp ha hsep
  have hlead :
      anchorLeadingCoeff61 a r j lam ≠ 0 :=
    anchorLeadingCoeffNonzeroLegal_proved65
      a r j t h ell lam hj hjr hh hell ht hp ha hsep
  have hgeneric :=
    hWeil r j t h ell lam hj hjr hh hell ht hnp hp hsep
      (anchorLeadingCoeff61 a r j lam) hlead
  rw [anchorQuadraticSum_eq_linearProduct96 hp]
  exact hgeneric

/-- Consequently the full faithful square-residue restriction now depends on
the generic linear-product Weil theorem alone on the character-sum side. -/
theorem weilRestriction_from_linearProduct96
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    WeilSquareResidueRestriction :=
  RemainingAnalytic70.weilRestriction_from_only_specializedWeil70
    (anchorQuadraticWeil_from_linearProduct96 hWeil)

-- Historical audit output: #print axioms anchorQuadraticSum_eq_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct96
-- Historical audit output: #print axioms weilRestriction_from_linearProduct96

end RemainingAnalytic96


/-! ## 92. Repair 97: correct the generic Weil boundary signature

Repair 96 failed before the mathematical adapter: `lam` was referenced in the
type of `c : ZMod lam` before `lam` had been introduced. This repair makes
`lam` the first explicit parameter and proves the sum identity by rewriting
the exact anchor factorization directly inside `quadraticCharValue62`.
-/

namespace RemainingAnalytic97

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic96

theorem anchorQuadraticWeil_from_linearProduct_checkpoint97
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    AnchorQuadraticWeil59 :=
  anchorQuadraticWeil_from_linearProduct96 hWeil

theorem weilRestriction_from_linearProduct_checkpoint97
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    WeilSquareResidueRestriction :=
  weilRestriction_from_linearProduct96 hWeil

-- Historical audit output: #print axioms anchorQuadraticSum_eq_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct96
-- Historical audit output: #print axioms weilRestriction_from_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct_checkpoint97
-- Historical audit output: #print axioms weilRestriction_from_linearProduct_checkpoint97

end RemainingAnalytic97


/-! ## 93. Repair 98: make primality part of the generic Weil sum

`ZMod lam` is finite only when `lam ≠ 0`.  The generic character sum is used
only for prime `lam`, so we make the prime proof an explicit argument and
install `Fact lam.Prime` inside the definition.  This avoids manufacturing a
spurious total definition at modulus zero.
-/

namespace RemainingAnalytic98

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic96 RemainingAnalytic97

theorem anchorQuadraticWeil_from_linearProduct_checkpoint98
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    AnchorQuadraticWeil59 :=
  anchorQuadraticWeil_from_linearProduct96 hWeil

theorem weilRestriction_from_linearProduct_checkpoint98
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    WeilSquareResidueRestriction :=
  weilRestriction_from_linearProduct96 hWeil

-- Historical audit output: #print axioms anchorQuadraticSum_eq_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct96
-- Historical audit output: #print axioms weilRestriction_from_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct_checkpoint98
-- Historical audit output: #print axioms weilRestriction_from_linearProduct_checkpoint98

end RemainingAnalytic98


/-! ## 94. Repair 99: bind the prime proof and normalize the character API

Repair 98 exposed two final elaboration issues in the generic Weil adapter.

1. The external theorem used `hp` in the generic sum before binding it.
2. After unfolding the anchor sum, the left side had already simplified to
   `quadraticChar`, while the generic side still used `quadraticCharValue62`.

This repair binds `hp : lam.Prime` explicitly and rewrites the generic side
through `quadraticCharValue_of_prime62` before applying the exact anchor
factorization.
-/

namespace RemainingAnalytic99

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic96
open RemainingAnalytic97 RemainingAnalytic98

theorem anchorQuadraticWeil_from_linearProduct_checkpoint99
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    AnchorQuadraticWeil59 :=
  anchorQuadraticWeil_from_linearProduct96 hWeil

theorem weilRestriction_from_linearProduct_checkpoint99
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    WeilSquareResidueRestriction :=
  weilRestriction_from_linearProduct96 hWeil

-- Historical audit output: #print axioms anchorQuadraticSum_eq_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct96
-- Historical audit output: #print axioms weilRestriction_from_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct_checkpoint99
-- Historical audit output: #print axioms weilRestriction_from_linearProduct_checkpoint99

end RemainingAnalytic99


/-! ## 95. Repair 100: exact quadratic-character API signature

Repair 99 leaves a single live elaboration error.  The theorem
`quadraticCharValue_of_prime62` has implicit modulus and therefore takes
`hp : lam.Prime` as its first explicit argument.  This repair uses the exact
signature and leaves the rest of the linear-product Weil reduction unchanged.
-/

namespace RemainingAnalytic100

open RemainingAnalytic37 RemainingAnalytic59 RemainingAnalytic96
open RemainingAnalytic97 RemainingAnalytic98 RemainingAnalytic99

theorem anchorQuadraticWeil_from_linearProduct_checkpoint100
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    AnchorQuadraticWeil59 :=
  anchorQuadraticWeil_from_linearProduct96 hWeil

theorem weilRestriction_from_linearProduct_checkpoint100
    (hWeil : ClassicalLinearProductQuadraticWeil96) :
    WeilSquareResidueRestriction :=
  weilRestriction_from_linearProduct96 hWeil

-- Historical audit output: #print axioms anchorQuadraticSum_eq_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct96
-- Historical audit output: #print axioms weilRestriction_from_linearProduct96
-- Historical audit output: #print axioms anchorQuadraticWeil_from_linearProduct_checkpoint100
-- Historical audit output: #print axioms weilRestriction_from_linearProduct_checkpoint100

end RemainingAnalytic100


/-! ## 96. Repair 101: consolidate the Proposition 5.1 analytic boundary

Repairs 92, 95, and 100 reduce the three project-specific analytic inputs to
three standard external theorems:

1. a classical prime-modulus additive large sieve;
2. a Chebyshev theta lower bound on dyadic prime intervals;
3. a quadratic-character Weil bound for a nonzero scalar times the two-family
   product of linear factors.

This section packages exactly those three theorems and proves that they imply
the existing `AnalyticCore58`.
-/

namespace RemainingAnalytic101

open RemainingAnalytic37 RemainingAnalytic58
open RemainingAnalytic92 RemainingAnalytic93 RemainingAnalytic96

structure ClassicalAnalyticCore101 where
  largeSieve : ClassicalPrimeAdditiveLargeSieve92
  dyadicTheta : ChebyshevDyadicThetaGap93
  linearProductWeil : ClassicalLinearProductQuadraticWeil96

/-- The classical large sieve gives the energy input. -/
theorem classicalCore_largeSieve101
    (h : ClassicalAnalyticCore101) :
    AnalyticLargeSieveEnergyUpper :=
  RemainingAnalytic92.analyticLargeSieveEnergy_from_classical92
    h.largeSieve

/-- The dyadic theta gap gives the auxiliary-prime supply. -/
theorem classicalCore_primeSupply101
    (h : ClassicalAnalyticCore101) :
    AuxiliaryPrimeSupply :=
  RemainingAnalytic93.auxiliaryPrimeSupply_from_thetaGap93
    h.dyadicTheta

/-- The generic linear-product Weil theorem gives the faithful anchor
square-residue restriction. -/
theorem classicalCore_weil101
    (h : ClassicalAnalyticCore101) :
    WeilSquareResidueRestriction :=
  RemainingAnalytic96.weilRestriction_from_linearProduct96
    h.linearProductWeil

/-- The entire Proposition 5.1 analytic core is therefore reduced to the
three classical theorems above. -/
theorem analyticCore58_from_classical101
    (h : ClassicalAnalyticCore101) :
    AnalyticCore58 :=
  ⟨classicalCore_weil101 h,
    classicalCore_primeSupply101 h,
    classicalCore_largeSieve101 h⟩

/-- Consequently all Proposition 5.1 consequences already proved from
`AnalyticCore58` are available from the consolidated classical core. -/
theorem uniformAnchorSieve_from_classical101
    (hGrowth : Tasks.FactorialClassGrowth)
    (h : ClassicalAnalyticCore101) :
    Tasks.UniformAnchorSieve :=
  RemainingAnalytic58.uniformAnchorSieve_from_analyticCore58
    hGrowth
    (analyticCore58_from_classical101 h)

-- Historical audit output: #print axioms classicalCore_largeSieve101
-- Historical audit output: #print axioms classicalCore_primeSupply101
-- Historical audit output: #print axioms classicalCore_weil101
-- Historical audit output: #print axioms analyticCore58_from_classical101
-- Historical audit output: #print axioms uniformAnchorSieve_from_classical101

end RemainingAnalytic101


/-! ## 97. Repair 102: correctly expose the downstream finite sieve theorem

Repair 101 successfully proved `ClassicalAnalyticCore101 -> AnalyticCore58`.
Its final convenience theorem omitted the independent factorial-growth input
required by `uniformAnchorSieve_from_analyticCore58` and also used the
unqualified target name.  This repair states the exact downstream theorem.
-/

namespace RemainingAnalytic102

open RemainingAnalytic58 RemainingAnalytic101

theorem analyticCore58_from_classical_checkpoint102
    (h : ClassicalAnalyticCore101) :
    AnalyticCore58 :=
  analyticCore58_from_classical101 h

theorem uniformAnchorSieve_from_classical_checkpoint102
    (hGrowth : Tasks.FactorialClassGrowth)
    (h : ClassicalAnalyticCore101) :
    Tasks.UniformAnchorSieve :=
  uniformAnchorSieve_from_classical101 hGrowth h

-- Historical audit output: #print axioms analyticCore58_from_classical101
-- Historical audit output: #print axioms analyticCore58_from_classical_checkpoint102
-- Historical audit output: #print axioms uniformAnchorSieve_from_classical101
-- Historical audit output: #print axioms uniformAnchorSieve_from_classical_checkpoint102

end RemainingAnalytic102


/-! ## 98. Repair 103: replace the three Proposition-5.1 fields in the
full endgame ledger by the consolidated classical analytic core

`EverythingLeft47` still lists the Weil estimate, auxiliary-prime supply, and
large-sieve energy separately.  Repairs 92--102 show that these three are all
consequences of `ClassicalAnalyticCore101`.

This section defines a sharper endgame record in which Proposition 5.1 is a
single classical analytic field.  Every other field below is genuinely
outside that Proposition-5.1 package.
-/

namespace RemainingAnalytic103

open RemainingAnalytic37 RemainingAnalytic43 RemainingAnalytic46
open RemainingAnalytic47 RemainingAnalytic101

structure EverythingLeftClassical103 where
  /- Finite / arithmetic / elementary targets. -/
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  /- Density of A. -/
  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  /- Proposition 3.5 asymptotics. -/
  cofactor_main : Remaining_CofactorMain47
  cofactor_lower : Remaining_CofactorLower47

  /- Standard PNT / q-growth. -/
  pnt : Remaining_PNTPackage47

  /- Short intervals. -/
  harman : Remaining_Harman47

  /- Lemma 4.1. -/
  dense_prime_mass : Remaining_DenseTopIntervalPrimeMass47
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  /- Entire Proposition 5.1 analytic package, reduced to three classical
     theorems in Repair 101. -/
  prop51_classical : ClassicalAnalyticCore101

/-- Exact conversion to the previous complete endgame ledger. -/
def EverythingLeftClassical103.to47
    (H : EverythingLeftClassical103) :
    EverythingLeft47 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_main := H.cofactor_main
  cofactor_lower := H.cofactor_lower
  pnt := H.pnt
  harman := H.harman
  dense_prime_mass := H.dense_prime_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  weil := classicalCore_weil101 H.prop51_classical
  auxiliary_prime_supply := classicalCore_primeSupply101 H.prop51_classical
  large_sieve_energy := classicalCore_largeSieve101 H.prop51_classical

/-- The candidate main statement from the sharpened endgame boundary. -/
theorem candidate_main_from_classical_endgame103
    (H : EverythingLeftClassical103) :
    MainStatement :=
  candidate_main_from_everything_left47 H.to47

/-- Positive lower density of `D6` from the sharpened endgame boundary. -/
theorem positive_lower_density_from_classical_endgame103
    (H : EverythingLeftClassical103) :
    PositiveLowerDensity D6 :=
  positive_lower_density_from_everything_left47 H.to47

/-- Full intermediate-output audit from the sharpened endgame boundary. -/
theorem everything_left_outputs_from_classical103
    (H : EverythingLeftClassical103) :
    EverythingLeftOutputs47 :=
  everything_left_outputs47 H.to47

-- Historical audit output: #print axioms EverythingLeftClassical103.to47
-- Historical audit output: #print axioms candidate_main_from_classical_endgame103
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame103
-- Historical audit output: #print axioms everything_left_outputs_from_classical103

end RemainingAnalytic103


/-! ## 99. Repair 105: correct the cofactor-lower audit

Repair 104 accidentally resolved `BCofactorLowerEndpointError` to the
*corrected* `RemainingAnalytic37` definition, whose conclusion is the genuine
eventual bound

    cofactorLowerSum X < ε.

That is not trivial and remains a real Proposition-3.5 analytic input.

There is, however, an obsolete earlier definition in `RemainingAnalytic21`
whose existential error term is disconnected from the cofactor sum.  We prove
only that obsolete proposition by choosing `E = 0`, while keeping the corrected
`RemainingAnalytic37.BCofactorLowerEndpointError` in the endgame boundary.
-/

namespace RemainingAnalytic105

open RemainingAnalytic47 RemainingAnalytic101 RemainingAnalytic103

/-- The obsolete Repair-21/source-level lower-endpoint interface is vacuous:
its witness `E` is not tied to any prime sum.  This theorem is an audit fact
about that old interface only. -/
theorem oldCofactorLowerEndpointError21_proved105 :
    RemainingAnalytic21.BCofactorLowerEndpointError := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro X hX
  refine ⟨0, by norm_num, ?_⟩
  exact hε

/-- Sharpened endgame boundary, retaining the corrected cofactor lower-error
statement from `RemainingAnalytic37`. -/
structure EverythingLeftClassical105 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  cofactor_main : Remaining_CofactorMain47
  cofactor_lower : Remaining_CofactorLower47

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_prime_mass : Remaining_DenseTopIntervalPrimeMass47
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical105.to103
    (H : EverythingLeftClassical105) :
    EverythingLeftClassical103 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_main := H.cofactor_main
  cofactor_lower := H.cofactor_lower
  pnt := H.pnt
  harman := H.harman
  dense_prime_mass := H.dense_prime_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame105
    (H : EverythingLeftClassical105) :
    MainStatement :=
  candidate_main_from_classical_endgame103 H.to103

theorem positive_lower_density_from_classical_endgame105
    (H : EverythingLeftClassical105) :
    PositiveLowerDensity D6 :=
  positive_lower_density_from_classical_endgame103 H.to103

theorem everything_left_outputs_from_classical105
    (H : EverythingLeftClassical105) :
    EverythingLeftOutputs47 :=
  everything_left_outputs_from_classical103 H.to103

-- Historical audit output: #print axioms oldCofactorLowerEndpointError21_proved105
-- Historical audit output: #print axioms EverythingLeftClassical105.to103
-- Historical audit output: #print axioms candidate_main_from_classical_endgame105
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame105
-- Historical audit output: #print axioms everything_left_outputs_from_classical105

end RemainingAnalytic105


/-! ## 100. Repair 106: reduce the corrected cofactor lower-endpoint error
to prime-count decay plus elementary cutoff geometry

The corrected lower-endpoint term is

  sum_{r in A, r <= X^alpha} pi(r^99) / X.

The analytic input needed here is only `pi(n)=o(n)`.  From that we first obtain
the global affine majorant `pi(n) <= eta*n + K`.  After summing, the problem
splits into two purely elementary cutoff quantities:

* the normalized 99th moment of `r <= X^alpha`, uniformly bounded;
* the normalized support size, tending to zero.

No further prime-distribution input is present in those two statements.
-/

namespace RemainingAnalytic106

open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic37

/-- Every prefix count is bounded by the length of `[1,n]`. -/
theorem prefixCount_le_self106 (S : Set ℕ) (n : ℕ) :
    prefixCount S n ≤ n := by
  classical
  unfold prefixCount
  calc
    ((Finset.Icc 1 n).filter (fun m => m ∈ S)).card
        ≤ (Finset.Icc 1 n).card := by
          apply Finset.card_le_card
          intro m hm
          exact (Finset.mem_filter.mp hm).1
    _ = n := by simp

/-- `pi(n)=o(n)` implies a uniform affine majorant.  The additive constant
absorbs the finite range below the PNT threshold. -/
theorem primeCountAffine_from_decay106
    (hPNT : PrimeCountDecay) :
    ∀ η : ℝ, 0 < η →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ n : ℕ,
          (prefixCount {p : ℕ | p.Prime} n : ℝ)
            ≤ η * (n : ℝ) + K := by
  intro η hη
  obtain ⟨N, hN⟩ := hPNT η hη
  refine ⟨(N : ℝ), by positivity, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have h := hN n hn
    have hNR : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith
  · have hcountNat :
        prefixCount {p : ℕ | p.Prime} n ≤ n :=
      prefixCount_le_self106 {p : ℕ | p.Prime} n
    have hcount :
        (prefixCount {p : ℕ | p.Prime} n : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hcountNat
    have hnN : n ≤ N := by omega
    have hnNR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have heta_nonneg : 0 ≤ η * (n : ℝ) := by positivity
    linarith

/-- Normalized 99th moment of the legal cofactor cutoff. -/
noncomputable def cofactorPowerNorm106 (X : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 X,
    if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
      ((r : ℝ) ^ (99 : ℕ)) / (X : ℝ)
    else 0

/-- Normalized cardinality of the same cutoff. -/
noncomputable def cofactorSupportNorm106 (X : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 X,
    if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
      (1 : ℝ) / (X : ℝ)
    else 0

/-- Purely elementary cutoff package.

For `alpha=1/100`, the first clause is the crude estimate
`sum_{r <= X^(1/100)} r^99 = O(X)`, while the second is
`# {r <= X^(1/100)} / X = o(1)`.
-/
def CofactorCutoffBounds106 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      cofactorPowerNorm106 X ≤ C) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      cofactorSupportNorm106 X < ε)

/-- Termwise insertion of the affine prime-count majorant. -/
theorem cofactorLower_le_affine106
    {η K : ℝ}
    (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hAff :
      ∀ n : ℕ,
        (prefixCount {p : ℕ | p.Prime} n : ℝ)
          ≤ η * (n : ℝ) + K)
    {X : ℕ} (hX : 1 ≤ X) :
    cofactorLowerSum X
      ≤ η * cofactorPowerNorm106 X
        + K * cofactorSupportNorm106 X := by
  classical
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  unfold cofactorLowerSum cofactorPowerNorm106 cofactorSupportNorm106
  calc
    (∑ r ∈ Finset.Icc 1 X,
        if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
          (prefixCount {p : ℕ | p.Prime} (r ^ 99) : ℝ) / (X : ℝ)
        else 0)
      ≤
    ∑ r ∈ Finset.Icc 1 X,
        if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
          (η * ((r : ℝ) ^ (99 : ℕ)) + K) / (X : ℝ)
        else 0 := by
          apply Finset.sum_le_sum
          intro r hr
          by_cases hc :
              r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha)
          · simp only [hc, if_true]
            apply (div_le_div_iff_of_pos_right hXpos).2
            have h := hAff (r ^ 99)
            norm_num only [Nat.cast_pow] at h
            exact h
          · simp [hc]
    _ =
      η *
        (∑ r ∈ Finset.Icc 1 X,
          if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
            ((r : ℝ) ^ (99 : ℕ)) / (X : ℝ)
          else 0)
      +
      K *
        (∑ r ∈ Finset.Icc 1 X,
          if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
            (1 : ℝ) / (X : ℝ)
          else 0) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hc :
                r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha)
            · simp [hc]
              ring
            · simp [hc]
    _ = η * cofactorPowerNorm106 X
        + K * cofactorSupportNorm106 X := rfl

/-- The corrected lower-endpoint error follows from prime-count decay and
the elementary cutoff package. -/
theorem cofactorLowerEndpointError_from_primeDecay106
    (hPNT : PrimeCountDecay)
    (hCut : CofactorCutoffBounds106) :
    BCofactorLowerEndpointError := by
  rcases hCut with ⟨C, hC, hpowPack, hsupp⟩
  rcases hpowPack with ⟨Npow, hpow⟩
  intro ε hε
  have hη : 0 < ε / (4 * C) := by positivity
  obtain ⟨K, hK, hAff⟩ :=
    primeCountAffine_from_decay106 hPNT (ε / (4 * C)) hη
  have hK1 : 0 < K + 1 := by linarith
  have hsupp_eps : 0 < ε / (4 * (K + 1)) := by positivity
  obtain ⟨Nsupp, hNsupp⟩ := hsupp (ε / (4 * (K + 1))) hsupp_eps
  refine ⟨max 1 (max Npow Nsupp), ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXPow : Npow ≤ X := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXSupp : Nsupp ≤ X := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hmain :=
    cofactorLower_le_affine106
      (η := ε / (4 * C)) (K := K)
      (le_of_lt hη) hK hAff hX1
  have hp := hpow X hXPow
  have hs := hNsupp X hXSupp
  have hηC :
      (ε / (4 * C)) * cofactorPowerNorm106 X ≤ ε / 4 := by
    have hnonneg : 0 ≤ ε / (4 * C) := le_of_lt hη
    calc
      (ε / (4 * C)) * cofactorPowerNorm106 X
          ≤ (ε / (4 * C)) * C :=
            mul_le_mul_of_nonneg_left hp hnonneg
      _ = ε / 4 := by field_simp [ne_of_gt hC]
  have hKs :
      K * cofactorSupportNorm106 X < ε / 4 := by
    have hKlt : K < K + 1 := by linarith
    have hsnonneg : 0 ≤ cofactorSupportNorm106 X := by
      unfold cofactorSupportNorm106
      positivity
    have h1 :
        K * cofactorSupportNorm106 X
          ≤ (K + 1) * cofactorSupportNorm106 X :=
      mul_le_mul_of_nonneg_right (le_of_lt hKlt) hsnonneg
    have h2 :
        (K + 1) * cofactorSupportNorm106 X < ε / 4 := by
      calc
        (K + 1) * cofactorSupportNorm106 X
            < (K + 1) * (ε / (4 * (K + 1))) := by
                exact mul_lt_mul_of_pos_left hs hK1
        _ = ε / 4 := by field_simp [ne_of_gt hK1]
    exact lt_of_le_of_lt h1 h2
  linarith

-- Historical audit output: #print axioms prefixCount_le_self106
-- Historical audit output: #print axioms primeCountAffine_from_decay106
-- Historical audit output: #print axioms cofactorLower_le_affine106
-- Historical audit output: #print axioms cofactorLowerEndpointError_from_primeDecay106

end RemainingAnalytic106


/-! ## 101. Repair 107: close the cofactor-lower assembly

Repair 106 established the PNT-to-affine-prime-count step.  The remaining
failures were purely proof assembly:

* distribute the affine summand pointwise, then use `Finset.sum_add_distrib`;
* destructure the cutoff package according to its actual nested conjunction /
  existential shape.
-/

namespace RemainingAnalytic107

open RemainingAnalytic20 RemainingAnalytic37 RemainingAnalytic106

theorem primeCountAffine_checkpoint107
    (hPNT : PrimeCountDecay) :
    ∀ η : ℝ, 0 < η →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ n : ℕ,
          (prefixCount {p : ℕ | p.Prime} n : ℝ)
            ≤ η * (n : ℝ) + K :=
  primeCountAffine_from_decay106 hPNT

theorem cofactorLowerEndpointError_checkpoint107
    (hPNT : PrimeCountDecay)
    (hCut : CofactorCutoffBounds106) :
    BCofactorLowerEndpointError :=
  cofactorLowerEndpointError_from_primeDecay106 hPNT hCut

-- Historical audit output: #print axioms prefixCount_le_self106
-- Historical audit output: #print axioms primeCountAffine_from_decay106
-- Historical audit output: #print axioms cofactorLower_le_affine106
-- Historical audit output: #print axioms cofactorLowerEndpointError_from_primeDecay106
-- Historical audit output: #print axioms cofactorLowerEndpointError_checkpoint107

end RemainingAnalytic107


/-! ## 102. Repair 108: normalize the final pointwise affine split

Repair 107 reduced the remaining failure to a purely syntactic residue:
after entering the positive cutoff branch, Lean still displayed
`if True ∧ True then ... else ...`.

A direct `simp [hc]` normalizes both conditional summands before ring
normalization.
-/

namespace RemainingAnalytic108

open RemainingAnalytic20 RemainingAnalytic37 RemainingAnalytic106 RemainingAnalytic107

theorem cofactorLower_le_affine_checkpoint108
    {η K : ℝ}
    (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hAff :
      ∀ n : ℕ,
        (prefixCount {p : ℕ | p.Prime} n : ℝ)
          ≤ η * (n : ℝ) + K)
    {X : ℕ} (hX : 1 ≤ X) :
    cofactorLowerSum X
      ≤ η * cofactorPowerNorm106 X
        + K * cofactorSupportNorm106 X :=
  cofactorLower_le_affine106 hη hK hAff hX

theorem cofactorLowerEndpointError_checkpoint108
    (hPNT : PrimeCountDecay)
    (hCut : CofactorCutoffBounds106) :
    BCofactorLowerEndpointError :=
  cofactorLowerEndpointError_from_primeDecay106 hPNT hCut

-- Historical audit output: #print axioms cofactorLower_le_affine106
-- Historical audit output: #print axioms cofactorLowerEndpointError_from_primeDecay106
-- Historical audit output: #print axioms cofactorLower_le_affine_checkpoint108
-- Historical audit output: #print axioms cofactorLowerEndpointError_checkpoint108

end RemainingAnalytic108


/-! ## 103. Repair 109: prove the elementary cofactor cutoff package

For `alpha = 1/100`, let

    B(X) = floor (X^alpha).

Every legal lower-endpoint cofactor lies in `[1,B(X)]`.  Therefore the
number of such cofactors is at most `B(X)`, and the sum of their 99th powers
is at most `B(X)^100`.  Since `B(X) <= X^(1/100)`, we have `B(X)^100 <= X`.

This proves the uniform normalized 99th-moment bound.  The normalized support
is at most `X^alpha / X = X^(-(1-alpha))`, which tends to zero.
-/

namespace RemainingAnalytic109

open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic37 RemainingAnalytic55
open RemainingAnalytic106

noncomputable def cofactorCutoff109 (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter
    (fun r => r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha))

noncomputable def cofactorCutoffB109 (X : ℕ) : ℕ :=
  Nat.floor ((X : ℝ) ^ alpha)

theorem mem_cutoff_le_floor109
    {X r : ℕ}
    (hr : r ∈ cofactorCutoff109 X) :
    r ≤ cofactorCutoffB109 X := by
  classical
  have hr' := Finset.mem_filter.mp hr
  dsimp [cofactorCutoffB109]
  exact Nat.le_floor hr'.2.2

theorem cutoff_subset_floorIcc109 (X : ℕ) :
    cofactorCutoff109 X ⊆ Finset.Icc 1 (cofactorCutoffB109 X) := by
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  exact Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hr'.1).1, mem_cutoff_le_floor109 hr⟩

theorem cutoff_card_le_floor109 (X : ℕ) :
    (cofactorCutoff109 X).card ≤ cofactorCutoffB109 X := by
  calc
    (cofactorCutoff109 X).card
        ≤ (Finset.Icc 1 (cofactorCutoffB109 X)).card :=
      Finset.card_le_card (cutoff_subset_floorIcc109 X)
    _ ≤ cofactorCutoffB109 X := by
      simp

theorem cofactorPowerNorm_eq_cutoff109
    (X : ℕ) :
    cofactorPowerNorm106 X =
      ∑ r ∈ cofactorCutoff109 X,
        ((r : ℝ) ^ (99 : ℕ)) / (X : ℝ) := by
  classical
  unfold cofactorPowerNorm106 cofactorCutoff109
  simp [Finset.sum_filter]

theorem cofactorSupportNorm_eq_cutoff109
    (X : ℕ) :
    cofactorSupportNorm106 X =
      ∑ r ∈ cofactorCutoff109 X, (1 : ℝ) / (X : ℝ) := by
  classical
  unfold cofactorSupportNorm106 cofactorCutoff109
  rw [Finset.sum_filter]

theorem cutoff_floor_rpow_le109
    (X : ℕ) :
    (cofactorCutoffB109 X : ℝ) ≤ (X : ℝ) ^ alpha := by
  dsimp [cofactorCutoffB109]
  exact Nat.floor_le (by positivity)

theorem rpow_alpha_pow_hundred109
    {X : ℕ} (hX : 1 ≤ X) :
    (((X : ℝ) ^ alpha) ^ (100 : ℕ)) = (X : ℝ) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  rw [Real.rpow_def_of_pos hXpos]
  rw [← Real.exp_nat_mul]
  have hscale :
      (100 : ℝ) * (Real.log (X : ℝ) * alpha) =
        Real.log (X : ℝ) := by
    norm_num [alpha]
    ring
  norm_num
  rw [hscale, Real.exp_log hXpos]

theorem cutoff_floor_pow_hundred_le109
    {X : ℕ} (hX : 1 ≤ X) :
    ((cofactorCutoffB109 X : ℝ) ^ (100 : ℕ)) ≤ (X : ℝ) := by
  have hB0 : (0 : ℝ) ≤ (cofactorCutoffB109 X : ℝ) := by positivity
  have hB := cutoff_floor_rpow_le109 X
  have hp :=
    pow_le_pow_left₀ hB0 hB (100 : ℕ)
  rw [rpow_alpha_pow_hundred109 hX] at hp
  exact hp

theorem cutoff_power_sum_le_floor100109
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ r ∈ cofactorCutoff109 X, (r : ℝ) ^ (99 : ℕ))
      ≤ (cofactorCutoffB109 X : ℝ) ^ (100 : ℕ) := by
  classical
  let B := cofactorCutoffB109 X
  have hcardNat := cutoff_card_le_floor109 X
  have hcard :
      ((cofactorCutoff109 X).card : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hcardNat
  have hterm :
      ∀ r ∈ cofactorCutoff109 X,
        (r : ℝ) ^ (99 : ℕ) ≤ (B : ℝ) ^ (99 : ℕ) := by
    intro r hr
    have hrBnat : r ≤ B := by
      simpa [B] using mem_cutoff_le_floor109 hr
    have hrB : (r : ℝ) ≤ (B : ℝ) := by exact_mod_cast hrBnat
    exact pow_le_pow_left₀ (by positivity) hrB (99 : ℕ)
  have hsum :
      (∑ r ∈ cofactorCutoff109 X, (r : ℝ) ^ (99 : ℕ))
        ≤ ((cofactorCutoff109 X).card : ℝ) * (B : ℝ) ^ (99 : ℕ) := by
    calc
      (∑ r ∈ cofactorCutoff109 X, (r : ℝ) ^ (99 : ℕ))
          ≤ ∑ r ∈ cofactorCutoff109 X, (B : ℝ) ^ (99 : ℕ) := by
            apply Finset.sum_le_sum
            intro r hr
            exact hterm r hr
      _ = ((cofactorCutoff109 X).card : ℝ) * (B : ℝ) ^ (99 : ℕ) := by
            simp
  calc
    (∑ r ∈ cofactorCutoff109 X, (r : ℝ) ^ (99 : ℕ))
        ≤ ((cofactorCutoff109 X).card : ℝ) * (B : ℝ) ^ (99 : ℕ) := hsum
    _ ≤ (B : ℝ) * (B : ℝ) ^ (99 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (B : ℝ) ^ (100 : ℕ) := by
      ring

theorem cofactorPowerNorm_le_one109
    {X : ℕ} (hX : 1 ≤ X) :
    cofactorPowerNorm106 X ≤ 1 := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  rw [cofactorPowerNorm_eq_cutoff109]
  have hsum := cutoff_power_sum_le_floor100109 hX
  have hpow := cutoff_floor_pow_hundred_le109 hX
  calc
    (∑ r ∈ cofactorCutoff109 X,
        (r : ℝ) ^ (99 : ℕ) / (X : ℝ))
        =
      (∑ r ∈ cofactorCutoff109 X, (r : ℝ) ^ (99 : ℕ)) / (X : ℝ) := by
        rw [Finset.sum_div]
    _ ≤ ((cofactorCutoffB109 X : ℝ) ^ (100 : ℕ)) / (X : ℝ) := by
        exact div_le_div_of_nonneg_right hsum (le_of_lt hXpos)
    _ ≤ (X : ℝ) / (X : ℝ) := by
        exact div_le_div_of_nonneg_right hpow (le_of_lt hXpos)
    _ = 1 := by field_simp [ne_of_gt hXpos]

theorem cofactorSupportNorm_le_rpow_ratio109
    {X : ℕ} (hX : 1 ≤ X) :
    cofactorSupportNorm106 X
      ≤ (X : ℝ) ^ alpha / (X : ℝ) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  rw [cofactorSupportNorm_eq_cutoff109]
  have hcardNat := cutoff_card_le_floor109 X
  have hcard :
      ((cofactorCutoff109 X).card : ℝ)
        ≤ (cofactorCutoffB109 X : ℝ) := by
    exact_mod_cast hcardNat
  have hfloor := cutoff_floor_rpow_le109 X
  calc
    (∑ r ∈ cofactorCutoff109 X, (1 : ℝ) / (X : ℝ))
        = ((cofactorCutoff109 X).card : ℝ) / (X : ℝ) := by
          simp [div_eq_mul_inv]
    _ ≤ (cofactorCutoffB109 X : ℝ) / (X : ℝ) := by
          exact div_le_div_of_nonneg_right hcard (le_of_lt hXpos)
    _ ≤ (X : ℝ) ^ alpha / (X : ℝ) := by
          exact div_le_div_of_nonneg_right hfloor (le_of_lt hXpos)

theorem rpow_ratio_eventually_small109 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        (X : ℝ) ^ alpha / (X : ℝ) < ε := by
  intro ε hε
  have hgap : 0 < 1 - alpha := by
    norm_num [alpha]
  obtain ⟨N0, hN0⟩ :=
    fixed_lt_rpow_eventually55
      (gap := 1 - alpha) (C := 1 / ε) hgap
  refine ⟨max 1 N0, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXN : N0 ≤ X := le_trans (le_max_right _ _) hX
  have hpow := hN0 X hXN
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hdecomp :
      (X : ℝ) ^ alpha * (X : ℝ) ^ (1 - alpha)
        = (X : ℝ) := by
    rw [← Real.rpow_add hXpos]
    have hsum : alpha + (1 - alpha) = (1 : ℝ) := by ring
    rw [hsum, Real.rpow_one]
  have hdenpos : 0 < (X : ℝ) ^ (1 - alpha) :=
    Real.rpow_pos_of_pos hXpos _
  have hratio :
      (X : ℝ) ^ alpha / (X : ℝ)
        = 1 / ((X : ℝ) ^ (1 - alpha)) := by
    field_simp [ne_of_gt hXpos, ne_of_gt hdenpos]
    nlinarith [hdecomp]
  rw [hratio]
  have hepsInv : 0 < 1 / ε := by positivity
  have hinv :
      1 / ((X : ℝ) ^ (1 - alpha)) < 1 / (1 / ε) := by
    exact one_div_lt_one_div_of_lt hepsInv hpow
  have heps : 1 / (1 / ε) = ε := by field_simp [ne_of_gt hε]
  simpa [heps] using hinv

theorem cofactorSupportNorm_eventually_small109 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        cofactorSupportNorm106 X < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := rpow_ratio_eventually_small109 ε hε
  refine ⟨max 1 N, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXN : N ≤ X := le_trans (le_max_right _ _) hX
  exact lt_of_le_of_lt
    (cofactorSupportNorm_le_rpow_ratio109 hX1)
    (hN X hXN)

theorem cofactorCutoffBounds_proved109 :
    CofactorCutoffBounds106 := by
  refine ⟨1, by norm_num, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    intro X hX
    exact cofactorPowerNorm_le_one109 hX
  · exact cofactorSupportNorm_eventually_small109

theorem cofactorLowerEndpointError_from_primeDecay_closed109
    (hPNT : PrimeCountDecay) :
    BCofactorLowerEndpointError :=
  cofactorLowerEndpointError_from_primeDecay106
    hPNT cofactorCutoffBounds_proved109

-- Historical audit output: #print axioms mem_cutoff_le_floor109
-- Historical audit output: #print axioms cutoff_card_le_floor109
-- Historical audit output: #print axioms rpow_alpha_pow_hundred109
-- Historical audit output: #print axioms cutoff_floor_pow_hundred_le109
-- Historical audit output: #print axioms cutoff_power_sum_le_floor100109
-- Historical audit output: #print axioms cofactorPowerNorm_le_one109
-- Historical audit output: #print axioms cofactorSupportNorm_le_rpow_ratio109
-- Historical audit output: #print axioms rpow_ratio_eventually_small109
-- Historical audit output: #print axioms cofactorSupportNorm_eventually_small109
-- Historical audit output: #print axioms cofactorCutoffBounds_proved109
-- Historical audit output: #print axioms cofactorLowerEndpointError_from_primeDecay_closed109

end RemainingAnalytic109


/-! ## 104. Repair 110: normalize the elementary cutoff proof

Repair 109 left four normalization-only failures:
* rewrite the support indicator sum with `Finset.sum_filter` directly;
* normalize the natural-number cast in the `100`-fold exponential identity;
* expose division as multiplication by an inverse in the constant finite sum;
* close the exponent decomposition with `Real.rpow_one`.
-/

namespace RemainingAnalytic110

open RemainingAnalytic20 RemainingAnalytic37 RemainingAnalytic106 RemainingAnalytic109

theorem cofactorCutoffBounds_checkpoint110 :
    CofactorCutoffBounds106 :=
  cofactorCutoffBounds_proved109

theorem cofactorLowerEndpointError_from_primeDecay_checkpoint110
    (hPNT : PrimeCountDecay) :
    BCofactorLowerEndpointError :=
  cofactorLowerEndpointError_from_primeDecay_closed109 hPNT

-- Historical audit output: #print axioms rpow_alpha_pow_hundred109
-- Historical audit output: #print axioms cofactorPowerNorm_le_one109
-- Historical audit output: #print axioms cofactorSupportNorm_le_rpow_ratio109
-- Historical audit output: #print axioms rpow_ratio_eventually_small109
-- Historical audit output: #print axioms cofactorCutoffBounds_proved109
-- Historical audit output: #print axioms cofactorLowerEndpointError_from_primeDecay_closed109
-- Historical audit output: #print axioms cofactorCutoffBounds_checkpoint110
-- Historical audit output: #print axioms cofactorLowerEndpointError_from_primeDecay_checkpoint110

end RemainingAnalytic110


/-! ## 105. Repair 111: remove the corrected cofactor-lower field from the endgame boundary

Repair 110 proves the genuine corrected lower-endpoint estimate from
`PrimeCountDecay` alone.  Since the existing `PNTPackage` already contains
that prime-count decay input, the separate `cofactor_lower` field is now
redundant for the endgame.

This section defines the sharpened endgame record with that field removed and
reconstructs the previous record automatically.
-/

namespace RemainingAnalytic111

open RemainingAnalytic20 RemainingAnalytic37 RemainingAnalytic47
open RemainingAnalytic101 RemainingAnalytic103 RemainingAnalytic109

/-- Endgame boundary after eliminating the corrected cofactor-lower estimate
as an independent input. -/
structure EverythingLeftClassical111 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  cofactor_main : Remaining_CofactorMain47

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_prime_mass : Remaining_DenseTopIntervalPrimeMass47
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

/-- Recover the corrected cofactor-lower estimate from the PNT package. -/
theorem cofactorLower_from_pntPackage111
    (hPNT : Remaining_PNTPackage47) :
    Remaining_CofactorLower47 :=
  cofactorLowerEndpointError_from_primeDecay_closed109 hPNT.prime_count_decay

/-- Exact conversion to the previous Repair-103 endgame ledger. -/
def EverythingLeftClassical111.to103
    (H : EverythingLeftClassical111) :
    EverythingLeftClassical103 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_main := H.cofactor_main
  cofactor_lower := cofactorLower_from_pntPackage111 H.pnt
  pnt := H.pnt
  harman := H.harman
  dense_prime_mass := H.dense_prime_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame111
    (H : EverythingLeftClassical111) :
    MainStatement :=
  candidate_main_from_classical_endgame103 H.to103

theorem positive_lower_density_from_classical_endgame111
    (H : EverythingLeftClassical111) :
    PositiveLowerDensity D6 :=
  positive_lower_density_from_classical_endgame103 H.to103

theorem everything_left_outputs_from_classical111
    (H : EverythingLeftClassical111) :
    EverythingLeftOutputs47 :=
  everything_left_outputs_from_classical103 H.to103

-- Historical audit output: #print axioms cofactorLower_from_pntPackage111
-- Historical audit output: #print axioms EverythingLeftClassical111.to103
-- Historical audit output: #print axioms candidate_main_from_classical_endgame111
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame111
-- Historical audit output: #print axioms everything_left_outputs_from_classical111

end RemainingAnalytic111


/-! ## 106. Repair 112: clean-spine checkpoint

This repair removes only superseded declarations that generated persistent
historical red errors:

* the failed Repair-61 finite-field attempts later replaced by Repairs 62--70;
* the failed Repair-71/75 support-image collision route later replaced by
  Repair 76 and the Parseval chain through Repair 91.

No surviving theorem from Repairs 62--111 referenced the removed declarations.
The current endgame checkpoint below therefore tests the cleaned proof spine
directly.
-/

namespace RemainingAnalytic112

open RemainingAnalytic111

theorem candidate_main_cleanSpine112
    (H : EverythingLeftClassical111) :
    MainStatement :=
  candidate_main_from_classical_endgame111 H

theorem positive_lower_density_cleanSpine112
    (H : EverythingLeftClassical111) :
    PositiveLowerDensity D6 :=
  positive_lower_density_from_classical_endgame111 H

-- Historical audit output: #print axioms candidate_main_cleanSpine112
-- Historical audit output: #print axioms positive_lower_density_cleanSpine112

end RemainingAnalytic112


/-! ## 107. Repair 113: fully clean historical spine

The last two hard red elaboration errors came from obsolete Repair-61
interfaces that mentioned `quadraticChar (ZMod lam)` before Lean could install
the prime-field instance from a hypothesis.  Repair 62 already replaced those
interfaces with a total prime-conditional wrapper, and no surviving theorem
referenced the old names.

This checkpoint tests the same current endgame after removing those final
obsolete declarations.
-/

namespace RemainingAnalytic113

open RemainingAnalytic111 RemainingAnalytic112

theorem candidate_main_fullyClean113
    (H : EverythingLeftClassical111) :
    MainStatement :=
  candidate_main_cleanSpine112 H

theorem positive_lower_density_fullyClean113
    (H : EverythingLeftClassical111) :
    PositiveLowerDensity D6 :=
  positive_lower_density_cleanSpine112 H

-- Historical audit output: #print axioms candidate_main_fullyClean113
-- Historical audit output: #print axioms positive_lower_density_fullyClean113

end RemainingAnalytic113


/-! ## 108. Repair 114: close the final accidental comment boundary

Repair 113 removed the last obsolete hard-error declarations, but the textual
surgery duplicated a doc-comment opener immediately before
`anchorSquareCount_eq_indicatorSum61`.  This repair fixes that syntax only.
-/

namespace RemainingAnalytic114

open RemainingAnalytic111 RemainingAnalytic113

theorem candidate_main_fullyClean114
    (H : EverythingLeftClassical111) :
    MainStatement :=
  candidate_main_fullyClean113 H

theorem positive_lower_density_fullyClean114
    (H : EverythingLeftClassical111) :
    PositiveLowerDensity D6 :=
  positive_lower_density_fullyClean113 H

-- Historical audit output: #print axioms candidate_main_fullyClean114
-- Historical audit output: #print axioms positive_lower_density_fullyClean114

end RemainingAnalytic114


/-! ## 109. Repair 115: batch analytic reductions

This repair makes three substantive boundary reductions at once.

1. The dense branch no longer assumes an already-packaged squarefree product
   `R`.  It assumes only logarithmic prime mass in the actual top interval,
   and constructs `R` internally as the product of those primes.

2. The cofactor main term is split into its two classical analytic pieces:
   a uniform PNT replacement of `π(X/r)/X` by the reciprocal-log kernel, and
   the Abel/partial-summation limit of that kernel against a set of density δ.

3. The sharpened endgame record uses these new inputs directly.  Together with
   Repair 111, neither `cofactor_lower` nor the manuscript-shaped
   `cofactor_main` nor the product-packaged dense-prime field is primitive.
-/

namespace RemainingAnalytic115

open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic24 RemainingAnalytic37
open RemainingAnalytic43 RemainingAnalytic47 RemainingAnalytic101
open RemainingAnalytic109 RemainingAnalytic111

/-! -------------------------------------------------------------------------
A. Dense top interval: reduce product packaging to logarithmic prime mass
------------------------------------------------------------------------- -/

/-- The actual prime set used in the dense branch. -/
def denseTopPrimes115 (b c : ℕ) : Finset ℕ :=
  (Finset.Icc 1 c).filter
    (fun p => p.Prime ∧ max b (c / 2) < p)

/-- Standard quantitative-PNT form of the dense input: the logarithmic mass
of primes in the top interval is at least one quarter of the interval length.

All construction of the squarefree witness is finite algebra and is done
below. -/
def DenseTopLogPrimeMass115 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ X₀ : ℕ,
    ∀ X a b c : ℕ, X₀ ≤ X → a < b → b < c → c ≤ X →
      (X : ℝ) ^ γ ≤ ((c - b : ℕ) : ℝ) →
      (a : ℝ) ≤ 10 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) →
      (b : ℝ) ≤
        100 * ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ 2 →
      ((c - b : ℕ) : ℝ) / 4 ≤
        ∑ p ∈ denseTopPrimes115 b c, Real.log (p : ℝ)

theorem denseTopPrimes_prime115
    {b c p : ℕ} (hp : p ∈ denseTopPrimes115 b c) :
    p.Prime := by
  exact (Finset.mem_filter.mp hp).2.1

theorem denseTopPrimes_range115
    {b c p : ℕ} (hp : p ∈ denseTopPrimes115 b c) :
    max b (c / 2) < p ∧ p ≤ c := by
  have h := Finset.mem_filter.mp hp
  exact ⟨h.2.2, (Finset.mem_Icc.mp h.1).2⟩

theorem denseTopPrimeProduct_pos115
    (b c : ℕ) :
    0 < ∏ p ∈ denseTopPrimes115 b c, p := by
  apply Finset.prod_pos
  intro p hp
  exact (denseTopPrimes_prime115 hp).pos

theorem denseTopPrimeProduct_squarefree115
    (b c : ℕ) :
    Squarefree (∏ p ∈ denseTopPrimes115 b c, p) := by
  exact squarefree_finset_prod_primes
    (fun p hp => denseTopPrimes_prime115 hp)

theorem log_denseTopPrimeProduct115
    (b c : ℕ) :
    Real.log (((∏ p ∈ denseTopPrimes115 b c, p : ℕ) : ℝ))
      =
    ∑ p ∈ denseTopPrimes115 b c, Real.log (p : ℝ) := by
  have hcast :
      (((∏ p ∈ denseTopPrimes115 b c, p : ℕ) : ℝ))
        =
      ∏ p ∈ denseTopPrimes115 b c, (p : ℝ) := by
    norm_num
  rw [hcast]
  rw [Real.log_prod]
  intro p hp
  exact_mod_cast
    (Nat.ne_of_gt (denseTopPrimes_prime115 hp).pos)

theorem prime_mem_denseTop_of_dvd_product115
    {b c p : ℕ}
    (hp : p.Prime)
    (hdiv : p ∣ ∏ r ∈ denseTopPrimes115 b c, r) :
    p ∈ denseTopPrimes115 b c := by
  exact prime_mem_of_dvd_finset_prod_primes
    hp
    (fun r hr => denseTopPrimes_prime115 hr)
    hdiv

/-- The standard log-mass statement implies exactly the old dense product
boundary.  In particular, squarefree-product extraction is no longer
external mathematics. -/
theorem denseTopIntervalPrimeMass_from_logMass115
    (H : DenseTopLogPrimeMass115) :
    DenseTopIntervalPrimeMass := by
  intro γ hγ0 hγ1
  obtain ⟨X₀, hX₀⟩ := H γ hγ0 hγ1
  refine ⟨X₀, ?_⟩
  intro X a b c hX hab hbc hcX hgap ha hb
  have hmass := hX₀ X a b c hX hab hbc hcX hgap ha hb
  let R : ℕ := ∏ p ∈ denseTopPrimes115 b c, p
  have hRpos : 0 < R := by
    simpa [R] using denseTopPrimeProduct_pos115 b c
  have hRsf : Squarefree R := by
    simpa [R] using denseTopPrimeProduct_squarefree115 b c
  refine ⟨R, hRpos, hRsf, ?_, ?_⟩
  · have hlogR := log_denseTopPrimeProduct115 b c
    simpa [R] using hmass.trans_eq hlogR.symm
  · intro p hp hpR
    have hpS : p ∈ denseTopPrimes115 b c := by
      apply prime_mem_denseTop_of_dvd_product115 hp
      simpa [R] using hpR
    exact denseTopPrimes_range115 hpS

/-! -------------------------------------------------------------------------
B. Cofactor main term: separate uniform PNT from density partial summation
------------------------------------------------------------------------- -/

/-- Reciprocal-log kernel obtained by replacing
`π(X/r)/(X)` by `1/(r log(X/r))`. -/
noncomputable def cofactorKernel115 (X : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 X,
    if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
      1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))
    else 0

/-- Uniform PNT input in precisely the range needed by Proposition 3.5.

This is the prime-distribution half of the cofactor main term.  It says that
after summing over the permitted cofactors, replacing the prime count by the
standard reciprocal-log kernel costs `o(1)`. -/
def UniformCofactorPNTKernel115 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    |RemainingAnalytic37.cofactorUpperSum X - cofactorKernel115 X| < ε

/-- Abel/partial-summation statement for a set of natural density δ.

This is the density-theoretic half of Proposition 3.5 and contains no prime
counting function. -/
def DensityCofactorKernelLimit115 : Prop :=
  ∀ δ : ℝ, HasDensity A δ →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      |cofactorKernel115 X - densityConstant δ| < ε

/-- Triangle-inequality assembly of the two classical pieces. -/
theorem cofactorMain_from_kernelPieces115
    (hPNT : UniformCofactorPNTKernel115)
    (hDensity : DensityCofactorKernelLimit115) :
    BCofactorMainTerm := by
  intro δ hA ε hε
  have he2 : 0 < ε / 2 := by linarith
  obtain ⟨NP, hNP⟩ := hPNT (ε / 2) he2
  obtain ⟨ND, hND⟩ := hDensity δ hA (ε / 2) he2
  refine ⟨max NP ND, ?_⟩
  intro X hX
  have hXP : NP ≤ X := le_trans (le_max_left _ _) hX
  have hXD : ND ≤ X := le_trans (le_max_right _ _) hX
  have hp := hNP X hXP
  have hd := hND X hXD
  calc
    |RemainingAnalytic37.cofactorUpperSum X - densityConstant δ|
        =
      |(RemainingAnalytic37.cofactorUpperSum X - cofactorKernel115 X)
        + (cofactorKernel115 X - densityConstant δ)| := by
          congr 1
          ring
    _ ≤
      |RemainingAnalytic37.cofactorUpperSum X - cofactorKernel115 X|
        +
      |cofactorKernel115 X - densityConstant δ| := by
          simpa only [Real.norm_eq_abs] using
            (norm_add_le
              (RemainingAnalytic37.cofactorUpperSum X - cofactorKernel115 X)
              (cofactorKernel115 X - densityConstant δ))
    _ < ε := by linarith

/-! -------------------------------------------------------------------------
C. Sharpen the full endgame record
------------------------------------------------------------------------- -/

/-- Endgame after:
* consolidating Proposition 5.1 to the three classical inputs of Repair 101;
* eliminating `cofactor_lower` from PNT (Repairs 106--111);
* replacing the packaged dense product by logarithmic prime mass;
* splitting the cofactor main term into uniform PNT + density partial summation.
-/
structure EverythingLeftClassical115 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  cofactor_pnt_kernel : UniformCofactorPNTKernel115
  cofactor_density_kernel : DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_log_prime_mass : DenseTopLogPrimeMass115
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical115.to111
    (H : EverythingLeftClassical115) :
    EverythingLeftClassical111 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_main :=
    cofactorMain_from_kernelPieces115
      H.cofactor_pnt_kernel H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_prime_mass :=
    denseTopIntervalPrimeMass_from_logMass115 H.dense_log_prime_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame115
    (H : EverythingLeftClassical115) :
    MainStatement :=
  candidate_main_from_classical_endgame111 H.to111

theorem positive_lower_density_from_classical_endgame115
    (H : EverythingLeftClassical115) :
    PositiveLowerDensity D6 :=
  positive_lower_density_from_classical_endgame111 H.to111

theorem everything_left_outputs_from_classical115
    (H : EverythingLeftClassical115) :
    EverythingLeftOutputs47 :=
  everything_left_outputs_from_classical111 H.to111

-- Historical audit output: #print axioms denseTopPrimeProduct_squarefree115
-- Historical audit output: #print axioms log_denseTopPrimeProduct115
-- Historical audit output: #print axioms denseTopIntervalPrimeMass_from_logMass115
-- Historical audit output: #print axioms cofactorMain_from_kernelPieces115
-- Historical audit output: #print axioms EverythingLeftClassical115.to111
-- Historical audit output: #print axioms candidate_main_from_classical_endgame115
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame115
-- Historical audit output: #print axioms everything_left_outputs_from_classical115


/-! ## 116. Cofactor PNT: expose the exact finite error sum

Repair 116 makes the prime-number-theorem half of Proposition 3.5 more
transparent.  Instead of taking the already-summed difference between the
cofactor prime count and the reciprocal-log kernel as the primitive input,
we define the exact error contributed by each cofactor and prove that the
aggregate difference is literally the finite sum of those errors.

This does not prove the remaining uniform PNT estimate itself.  It moves the
formalization boundary from a bespoke difference of two large sums to the
standard-looking assertion that the corresponding finite PNT error sum tends
to zero uniformly on the legal cofactor range.
-/

namespace RemainingAnalytic116

open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic37 RemainingAnalytic115

/-- The individual normalized PNT error at cofactor `r`.  It is set to zero
outside the legal cofactor support, exactly matching both sums in Repair 115. -/
noncomputable def cofactorPNTErrorTerm116 (X r : ℕ) : ℝ :=
  if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
    (prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
      1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))
  else 0

/-- Exact algebraic decomposition of the aggregate kernel error into the sum
of the individual cofactor errors. -/
theorem cofactorUpper_sub_kernel_eq_errorSum116 (X : ℕ) :
    RemainingAnalytic37.cofactorUpperSum X -
        RemainingAnalytic115.cofactorKernel115 X
      =
    ∑ r ∈ Finset.Icc 1 X, cofactorPNTErrorTerm116 X r := by
  unfold RemainingAnalytic37.cofactorUpperSum
  unfold RemainingAnalytic115.cofactorKernel115
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hc : r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha)
  · simp [cofactorPNTErrorTerm116, hc]
  · simp [cofactorPNTErrorTerm116, hc]

/-- Source-level uniform PNT input after Repair 116: the finite sum of the
actual cofactor-by-cofactor errors is `o(1)`. -/
def CofactorPNTErrorSum116 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    |∑ r ∈ Finset.Icc 1 X, cofactorPNTErrorTerm116 X r| < ε

/-- The explicit finite-error-sum statement implies Repair 115's packaged
uniform cofactor PNT kernel estimate. -/
theorem uniformCofactorPNTKernel_from_errorSum116
    (H : CofactorPNTErrorSum116) :
    RemainingAnalytic115.UniformCofactorPNTKernel115 := by
  intro ε hε
  obtain ⟨N, hN⟩ := H ε hε
  refine ⟨N, ?_⟩
  intro X hX
  rw [cofactorUpper_sub_kernel_eq_errorSum116]
  exact hN X hX

/-- A useful zero-support lemma for future termwise PNT estimates. -/
theorem cofactorPNTErrorTerm_eq_zero_of_not_legal116
    {X r : ℕ}
    (h : ¬ (r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha))) :
    cofactorPNTErrorTerm116 X r = 0 := by
  simp [cofactorPNTErrorTerm116, h]

/-- On the legal support, the error term has exactly the expected PNT form. -/
theorem cofactorPNTErrorTerm_eq_of_legal116
    {X r : ℕ}
    (h : r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha)) :
    cofactorPNTErrorTerm116 X r =
      (prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
        1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))) := by
  simp [cofactorPNTErrorTerm116, h]

/-- Repair-116 endgame: the old `UniformCofactorPNTKernel115` field is replaced
by the exact finite error-sum statement.  All other Repair-115 reductions are
retained unchanged. -/
structure EverythingLeftClassical116 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  cofactor_pnt_error_sum : CofactorPNTErrorSum116
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_log_prime_mass : RemainingAnalytic115.DenseTopLogPrimeMass115
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical116.to115
    (H : EverythingLeftClassical116) :
    RemainingAnalytic115.EverythingLeftClassical115 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_pnt_kernel :=
    uniformCofactorPNTKernel_from_errorSum116 H.cofactor_pnt_error_sum
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_log_prime_mass := H.dense_log_prime_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame116
    (H : EverythingLeftClassical116) :
    MainStatement :=
  RemainingAnalytic115.candidate_main_from_classical_endgame115 H.to115

theorem positive_lower_density_from_classical_endgame116
    (H : EverythingLeftClassical116) :
    PositiveLowerDensity D6 :=
  RemainingAnalytic115.positive_lower_density_from_classical_endgame115 H.to115

theorem everything_left_outputs_from_classical116
    (H : EverythingLeftClassical116) :
    EverythingLeftOutputs47 :=
  RemainingAnalytic115.everything_left_outputs_from_classical115 H.to115

-- Historical audit output: #print axioms cofactorUpper_sub_kernel_eq_errorSum116
-- Historical audit output: #print axioms uniformCofactorPNTKernel_from_errorSum116
-- Historical audit output: #print axioms candidate_main_from_classical_endgame116
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame116
-- Historical audit output: #print axioms everything_left_outputs_from_classical116

end RemainingAnalytic116


/-! ## 117. Cofactor PNT: relative pointwise error plus kernel L1 control

Repair 117 removes one more bespoke analytic interface.  Repair 116 asked
for the signed finite sum of the normalized PNT errors to be `o(1)`.  Here we
show that it is enough to have the two standard ingredients one would
actually prove:

* a uniform relative pointwise PNT estimate on the legal cofactor range; and
* an eventual uniform L1 bound for the reciprocal-log kernel.

The Lean work below performs all finite summation, triangle-inequality, and
constant bookkeeping.  No cancellation in the signed PNT error sum is used.
-/

namespace RemainingAnalytic117

open scoped BigOperators
open RemainingAnalytic116

/-- The individual reciprocal-log kernel weight.  Outside the legal cofactor
support it is zero, matching `cofactorKernel115`. -/
noncomputable def cofactorKernelTerm117 (X r : ℕ) : ℝ :=
  if r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha) then
    1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))
  else 0

/-- The Repair-115 kernel is exactly the sum of the pointwise kernel terms. -/
theorem cofactorKernel_eq_sum_terms117 (X : ℕ) :
    RemainingAnalytic115.cofactorKernel115 X =
      ∑ r ∈ Finset.Icc 1 X, cofactorKernelTerm117 X r := by
  unfold RemainingAnalytic115.cofactorKernel115
  apply Finset.sum_congr rfl
  intro r hr
  rfl

/-- Uniform relative PNT error on every cofactor in the finite summation.
This is the natural pointwise input obtained from a uniform PNT on
`X / r`, with `r ≤ X^alpha`. -/
def UniformRelativeCofactorPNT117 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    ∀ r ∈ Finset.Icc 1 X,
      |RemainingAnalytic116.cofactorPNTErrorTerm116 X r| ≤
        ρ * |cofactorKernelTerm117 X r|

/-- The reciprocal-log kernel has bounded total absolute mass on the legal
cofactor range.  This is the non-cancellation form of the elementary kernel
bound needed to sum a relative PNT error. -/
def CofactorKernelL1Bound117 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    ∑ r ∈ Finset.Icc 1 X, |cofactorKernelTerm117 X r| ≤ C

/-- Generic finite triangle inequality, written locally so this repair does
not depend on a particular Mathlib lemma name for `abs` of a finite sum. -/
theorem abs_finset_sum_le_sum_abs117
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    |∑ x ∈ s, f x| ≤ ∑ x ∈ s, |f x| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have htri : |f a + ∑ x ∈ s, f x| ≤ |f a| + |∑ x ∈ s, f x| := by
        simpa only [Real.norm_eq_abs] using
          (norm_add_le (f a) (∑ x ∈ s, f x))
      exact htri.trans (add_le_add (le_refl |f a|) ih)

/-- Relative pointwise PNT plus bounded kernel L1 mass gives an absolute
summed PNT error tending to zero. -/
theorem cofactorAbsoluteErrorSum_from_relative_l1_117
    (hRel : UniformRelativeCofactorPNT117)
    (hL1 : CofactorKernelL1Bound117) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (∑ r ∈ Finset.Icc 1 X,
        |RemainingAnalytic116.cofactorPNTErrorTerm116 X r|) < ε := by
  intro ε hε
  obtain ⟨C, hC, NK, hK⟩ := hL1
  let ρ : ℝ := ε / (2 * C)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  obtain ⟨NP, hP⟩ := hRel ρ hρ
  refine ⟨max NP NK, ?_⟩
  intro X hX
  have hXP : NP ≤ X := le_trans (le_max_left NP NK) hX
  have hXK : NK ≤ X := le_trans (le_max_right NP NK) hX
  have hsum :
      (∑ r ∈ Finset.Icc 1 X,
        |RemainingAnalytic116.cofactorPNTErrorTerm116 X r|)
        ≤
      ∑ r ∈ Finset.Icc 1 X, ρ * |cofactorKernelTerm117 X r| := by
    apply Finset.sum_le_sum
    intro r hr
    exact hP X hXP r hr
  have hsum' :
      (∑ r ∈ Finset.Icc 1 X,
        |RemainingAnalytic116.cofactorPNTErrorTerm116 X r|)
        ≤
      ρ * (∑ r ∈ Finset.Icc 1 X, |cofactorKernelTerm117 X r|) := by
    simpa [Finset.mul_sum] using hsum
  have hKC := hK X hXK
  have hbound :
      ρ * (∑ r ∈ Finset.Icc 1 X, |cofactorKernelTerm117 X r|) ≤ ρ * C := by
    exact mul_le_mul_of_nonneg_left hKC (le_of_lt hρ)
  have hρC : ρ * C = ε / 2 := by
    dsimp [ρ]
    field_simp [ne_of_gt hC]
  have hhalf : ε / 2 < ε := by linarith
  exact lt_of_le_of_lt (hsum'.trans hbound) (by simpa [hρC] using hhalf)

/-- Hence the relative pointwise PNT and kernel L1 bound imply the exact
Repair-116 signed error-sum input. -/
theorem cofactorPNTErrorSum_from_relative_l1_117
    (hRel : UniformRelativeCofactorPNT117)
    (hL1 : CofactorKernelL1Bound117) :
    RemainingAnalytic116.CofactorPNTErrorSum116 := by
  intro ε hε
  obtain ⟨N, hN⟩ :=
    cofactorAbsoluteErrorSum_from_relative_l1_117 hRel hL1 ε hε
  refine ⟨N, ?_⟩
  intro X hX
  have habs := abs_finset_sum_le_sum_abs117
    (Finset.Icc 1 X)
    (fun r => RemainingAnalytic116.cofactorPNTErrorTerm116 X r)
  exact lt_of_le_of_lt habs (hN X hX)

/-- Repair-117 endgame.  The single signed-error-sum field from Repair 116 is
replaced by a pointwise uniform relative PNT statement and an L1 kernel bound.
All finite summation needed to recover Repair 116 is now proved in Lean. -/
structure EverythingLeftClassical117 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  cofactor_relative_pnt : UniformRelativeCofactorPNT117
  cofactor_kernel_l1 : CofactorKernelL1Bound117
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_log_prime_mass : RemainingAnalytic115.DenseTopLogPrimeMass115
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical117.to116
    (H : EverythingLeftClassical117) :
    RemainingAnalytic116.EverythingLeftClassical116 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_pnt_error_sum :=
    cofactorPNTErrorSum_from_relative_l1_117
      H.cofactor_relative_pnt H.cofactor_kernel_l1
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_log_prime_mass := H.dense_log_prime_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame117
    (H : EverythingLeftClassical117) :
    MainStatement :=
  RemainingAnalytic116.candidate_main_from_classical_endgame116 H.to116

theorem positive_lower_density_from_classical_endgame117
    (H : EverythingLeftClassical117) :
    PositiveLowerDensity D6 :=
  RemainingAnalytic116.positive_lower_density_from_classical_endgame116 H.to116

theorem everything_left_outputs_from_classical117
    (H : EverythingLeftClassical117) :
    EverythingLeftOutputs47 :=
  RemainingAnalytic116.everything_left_outputs_from_classical116 H.to116

-- Historical audit output: #print axioms cofactorKernel_eq_sum_terms117
-- Historical audit output: #print axioms abs_finset_sum_le_sum_abs117
-- Historical audit output: #print axioms cofactorAbsoluteErrorSum_from_relative_l1_117
-- Historical audit output: #print axioms cofactorPNTErrorSum_from_relative_l1_117
-- Historical audit output: #print axioms candidate_main_from_classical_endgame117
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame117
-- Historical audit output: #print axioms everything_left_outputs_from_classical117

end RemainingAnalytic117


/-! ## 118. Remove the redundant cofactor-kernel L1 assumption

Repair 117 used two inputs to sum the pointwise PNT error: a relative PNT
bound and an eventual L1 bound for the reciprocal-log kernel.  The latter is
not genuinely independent.  For X > 1 every legal kernel term is nonnegative
(because r <= X^alpha < X), and the already retained density-kernel limit
therefore bounds the total absolute kernel mass.

Thus Repair 118 derives `CofactorKernelL1Bound117` from the A-density
approximation plus `DensityCofactorKernelLimit115`, and removes
`cofactor_kernel_l1` from the final endgame record.
-/

namespace RemainingAnalytic118

open scoped BigOperators
open RemainingAnalytic117

/-- The chosen exponent alpha is strictly below one. -/
theorem alpha_lt_one118 : alpha < (1 : ℝ) := by
  norm_num [alpha]

/-- For a real base above one, the alpha power is strictly smaller than the
base itself. -/
theorem rpow_alpha_lt_self118 {x : ℝ} (hx : 1 < x) :
    x ^ alpha < x := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hpow : x ^ alpha < x ^ (1 : ℝ) := by
    rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hxpos]
    apply Real.exp_lt_exp.mpr
    have hlog : 0 < Real.log x := Real.log_pos hx
    nlinarith [alpha_lt_one118]
  simpa using hpow

/-- Every legal reciprocal-log kernel term is nonnegative once X >= 2. -/
theorem cofactorKernelTerm_nonneg118
    {X r : ℕ} (hX : 2 ≤ X) :
    0 ≤ cofactorKernelTerm117 X r := by
  unfold cofactorKernelTerm117
  split_ifs with hlegal
  · rcases hlegal with ⟨hrA, hrpow⟩
    have hXgt : (1 : ℝ) < X := by
      exact_mod_cast (show 1 < X by omega)
    have hpowlt : (X : ℝ) ^ alpha < (X : ℝ) :=
      rpow_alpha_lt_self118 hXgt
    have hrX : (r : ℝ) < (X : ℝ) := lt_of_le_of_lt hrpow hpowlt
    have hr1 : 1 ≤ r := hrA.1
    have hrposN : 0 < r := by omega
    have hrposR : (0 : ℝ) < r := by exact_mod_cast hrposN
    have hratio : (1 : ℝ) < (X : ℝ) / (r : ℝ) := by
      apply (lt_div_iff₀ hrposR).2
      simpa using hrX
    have hlogpos : 0 < Real.log ((X : ℝ) / (r : ℝ)) :=
      Real.log_pos hratio
    positivity
  · simp

/-- Hence absolute values disappear term-by-term in the eventual range. -/
theorem abs_cofactorKernelTerm_eq118
    {X r : ℕ} (hX : 2 ≤ X) :
    |cofactorKernelTerm117 X r| = cofactorKernelTerm117 X r := by
  exact abs_of_nonneg (cofactorKernelTerm_nonneg118 hX)

/-- The kernel L1 mass is exactly the kernel itself for X >= 2. -/
theorem sum_abs_cofactorKernelTerm_eq_kernel118
    {X : ℕ} (hX : 2 ≤ X) :
    (∑ r ∈ Finset.Icc 1 X, |cofactorKernelTerm117 X r|) =
      RemainingAnalytic115.cofactorKernel115 X := by
  calc
    (∑ r ∈ Finset.Icc 1 X, |cofactorKernelTerm117 X r|)
        = ∑ r ∈ Finset.Icc 1 X, cofactorKernelTerm117 X r := by
            apply Finset.sum_congr rfl
            intro r hr
            exact abs_cofactorKernelTerm_eq118 hX
    _ = RemainingAnalytic115.cofactorKernel115 X :=
      (cofactorKernel_eq_sum_terms117 X).symm

/-- The A-density approximation plus convergence of the cofactor kernel
already implies the Repair-117 L1 bound; no separate analytic hypothesis is
needed. -/
theorem cofactorKernelL1Bound_from_density118
    (hLim : Remaining_AFiniteDensityLimit47)
    (hTail : Remaining_AUniformTail47)
    (hDensity : RemainingAnalytic115.DensityCofactorKernelLimit115) :
    CofactorKernelL1Bound117 := by
  have hApprox : RemainingAnalytic20.ADensityApproximation :=
    A_approximation_of_limit_tail hLim hTail
  have hAdensity : HasDensity A hApprox.delta :=
    A_density_of_approximation hApprox
  obtain ⟨N, hN⟩ := hDensity hApprox.delta hAdensity 1 (by norm_num)
  let C : ℝ := |densityConstant hApprox.delta| + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, max N 2, ?_⟩
  intro X hX
  have hXN : N ≤ X := le_trans (le_max_left N 2) hX
  have hX2 : 2 ≤ X := le_trans (le_max_right N 2) hX
  have hclose := hN X hXN
  have hupper :
      RemainingAnalytic115.cofactorKernel115 X <
        densityConstant hApprox.delta + 1 := by
    have := (abs_lt.mp hclose).2
    linarith
  have hdle : densityConstant hApprox.delta ≤ |densityConstant hApprox.delta| :=
    le_abs_self _
  have hKC : RemainingAnalytic115.cofactorKernel115 X ≤ C := by
    dsimp [C]
    exact le_of_lt (lt_of_lt_of_le hupper (by linarith))
  rw [sum_abs_cofactorKernelTerm_eq_kernel118 hX2]
  exact hKC

/-- Repair-118 endgame: `cofactor_kernel_l1` has disappeared.  It is derived
from fields that were already required for the A-density and cofactor-density
parts of Proposition 3.5. -/
structure EverythingLeftClassical118 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  cofactor_relative_pnt : UniformRelativeCofactorPNT117
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_log_prime_mass : RemainingAnalytic115.DenseTopLogPrimeMass115
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical118.to117
    (H : EverythingLeftClassical118) :
    EverythingLeftClassical117 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_relative_pnt := H.cofactor_relative_pnt
  cofactor_kernel_l1 :=
    cofactorKernelL1Bound_from_density118
      H.A_density_limit H.A_uniform_tail H.cofactor_density_kernel
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_log_prime_mass := H.dense_log_prime_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame118
    (H : EverythingLeftClassical118) : MainStatement :=
  candidate_main_from_classical_endgame117 H.to117

theorem positive_lower_density_from_classical_endgame118
    (H : EverythingLeftClassical118) : PositiveLowerDensity D6 :=
  positive_lower_density_from_classical_endgame117 H.to117

theorem everything_left_outputs_from_classical118
    (H : EverythingLeftClassical118) : EverythingLeftOutputs47 :=
  everything_left_outputs_from_classical117 H.to117

-- Historical audit output: #print axioms alpha_lt_one118
-- Historical audit output: #print axioms rpow_alpha_lt_self118
-- Historical audit output: #print axioms cofactorKernelTerm_nonneg118
-- Historical audit output: #print axioms sum_abs_cofactorKernelTerm_eq_kernel118
-- Historical audit output: #print axioms cofactorKernelL1Bound_from_density118
-- Historical audit output: #print axioms candidate_main_from_classical_endgame118
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame118

-- Historical audit output: #print axioms everything_left_outputs_from_classical118

end RemainingAnalytic118


/-! ## 119. Dense branch: strip away the irrelevant bottom-index variables

Repair 115's dense logarithmic prime-mass input still quantified over the
bottom factorial index `a` and its auxiliary bound, even though the prime sum
itself depends only on `X,b,c`.  Repair 119 removes that redundancy.  The new
input is the standard Chebyshev-theta lower bound on the actual top interval
`(max(b,c/2),c]`; all references to `a` are reconstructed automatically when
the old manuscript-facing interface is needed.
-/

namespace RemainingAnalytic119

open scoped BigOperators
open RemainingAnalytic117 RemainingAnalytic118

/-- Chebyshev-theta mass on the exact top interval used by the dense branch.
Compared with `DenseTopLogPrimeMass115`, this contains only variables that
actually occur in the prime sum. -/
def DenseTopThetaMass119 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ X₀ : ℕ,
    ∀ X b c : ℕ, X₀ ≤ X → b < c → c ≤ X →
      (X : ℝ) ^ γ ≤ ((c - b : ℕ) : ℝ) →
      (b : ℝ) ≤
        100 * ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ 2 →
      ((c - b : ℕ) : ℝ) / 4 ≤
        ∑ p ∈ RemainingAnalytic115.denseTopPrimes115 b c,
          Real.log (p : ℝ)

/-- The stripped-down theta statement implies the previous dense analytic
input.  The bottom index `a` and its bound are logically irrelevant here. -/
theorem denseTopLogPrimeMass_from_theta119
    (H : DenseTopThetaMass119) :
    RemainingAnalytic115.DenseTopLogPrimeMass115 := by
  intro γ hγ0 hγ1
  obtain ⟨X₀, hX₀⟩ := H γ hγ0 hγ1
  refine ⟨X₀, ?_⟩
  intro X a b c hX hab hbc hcX hgap ha hb
  exact hX₀ X b c hX hbc hcX hgap hb

/-- Repair-119 endgame: the dense branch now asks only for the actual
Chebyshev-theta estimate, with no irrelevant bottom-index quantifiers. -/
structure EverythingLeftClassical119 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  cofactor_relative_pnt : RemainingAnalytic117.UniformRelativeCofactorPNT117
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_theta_mass : DenseTopThetaMass119
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical119.to118
    (H : EverythingLeftClassical119) :
    RemainingAnalytic118.EverythingLeftClassical118 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_relative_pnt := H.cofactor_relative_pnt
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_log_prime_mass := denseTopLogPrimeMass_from_theta119 H.dense_theta_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame119
    (H : EverythingLeftClassical119) : MainStatement :=
  RemainingAnalytic118.candidate_main_from_classical_endgame118 H.to118

theorem positive_lower_density_from_classical_endgame119
    (H : EverythingLeftClassical119) : PositiveLowerDensity D6 :=
  RemainingAnalytic118.positive_lower_density_from_classical_endgame118 H.to118

theorem everything_left_outputs_from_classical119
    (H : EverythingLeftClassical119) : EverythingLeftOutputs47 :=
  RemainingAnalytic118.everything_left_outputs_from_classical118 H.to118

-- Historical audit output: #print axioms denseTopLogPrimeMass_from_theta119
-- Historical audit output: #print axioms candidate_main_from_classical_endgame119
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame119
-- Historical audit output: #print axioms everything_left_outputs_from_classical119


end RemainingAnalytic119


/-! ## 120. Cofactor PNT: expose the legal-range pointwise theorem

Repair 117 still states the PNT input in terms of the already-packaged
`cofactorPNTErrorTerm116` and `cofactorKernelTerm117`, both of which contain
support `if`s.  Repair 120 removes that formalization artifact.

The new input is exactly the normalized prime-count estimate on a *legal*
cofactor `r`:
  | pi(X/r)/X - 1/(r log(X/r)) |
    <= rho /(r log(X/r)).
Outside the legal support the Repair-117 error term and kernel term are both
zero, so the old interface is recovered internally.
-/

namespace RemainingAnalytic120

open scoped BigOperators
open RemainingAnalytic117 RemainingAnalytic118 RemainingAnalytic119

/-- Pointwise uniform PNT on the actual legal cofactor range, with no support
`if`s and no absolute value around the positive reciprocal-log kernel. -/
def LegalPointwiseCofactorPNT120 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ N : ℕ, ∀ X : ℕ, max N 2 ≤ X →
    ∀ r ∈ Finset.Icc 1 X,
      r ∈ A →
      ((r : ℝ) ≤ (X : ℝ) ^ alpha) →
      |(prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
          1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))|
        ≤
      ρ * (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))))

/-- On legal support, the Repair-117 kernel term is exactly the reciprocal-log
main term. -/
theorem cofactorKernelTerm_eq_main120
    {X r : ℕ}
    (hrA : r ∈ A)
    (hrpow : (r : ℝ) ≤ (X : ℝ) ^ alpha) :
    cofactorKernelTerm117 X r =
      1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))) := by
  simp [cofactorKernelTerm117, hrA, hrpow]

/-- On legal support, the Repair-116 error term is exactly the normalized
prime-count remainder. -/
theorem cofactorPNTErrorTerm_eq_main120
    {X r : ℕ}
    (hrA : r ∈ A)
    (hrpow : (r : ℝ) ≤ (X : ℝ) ^ alpha) :
    RemainingAnalytic116.cofactorPNTErrorTerm116 X r =
      (prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
        1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))) := by
  simp [RemainingAnalytic116.cofactorPNTErrorTerm116, hrA, hrpow]

/-- The legal-range pointwise PNT implies Repair 117's packaged relative PNT
input.  All support bookkeeping is discharged here once and for all. -/
theorem uniformRelativeCofactorPNT_from_legal120
    (H : LegalPointwiseCofactorPNT120) :
    UniformRelativeCofactorPNT117 := by
  intro ρ hρ
  obtain ⟨N, hN⟩ := H ρ hρ
  refine ⟨max N 2, ?_⟩
  intro X hX r hr
  by_cases hc : r ∈ A ∧ ((r : ℝ) ≤ (X : ℝ) ^ alpha)
  · rcases hc with ⟨hrA, hrpow⟩
    have hraw := hN X hX r hr hrA hrpow
    have hX2 : 2 ≤ X := le_trans (le_max_right N 2) hX
    have hk_nonneg :
        0 ≤ cofactorKernelTerm117 X r :=
      RemainingAnalytic118.cofactorKernelTerm_nonneg118 hX2
    have hk_eq :
        cofactorKernelTerm117 X r =
          1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))) :=
      cofactorKernelTerm_eq_main120 hrA hrpow
    have hmain_nonneg :
        0 ≤ 1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))) := by
      simpa [hk_eq] using hk_nonneg
    rw [cofactorPNTErrorTerm_eq_main120 hrA hrpow, hk_eq,
      abs_of_nonneg hmain_nonneg]
    exact hraw
  · have herr :
        RemainingAnalytic116.cofactorPNTErrorTerm116 X r = 0 := by
      simp [RemainingAnalytic116.cofactorPNTErrorTerm116, hc]
    have hk :
        cofactorKernelTerm117 X r = 0 := by
      simp [cofactorKernelTerm117, hc]
    rw [herr, hk]
    simp

/-- Repair-120 endgame: the cofactor PNT field now states only the genuine
legal-range prime-count estimate.  The support-condition packaging in Repairs
116--117 is no longer part of the external analytic boundary. -/
structure EverythingLeftClassical120 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  cofactor_pointwise_pnt : LegalPointwiseCofactorPNT120
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_theta_mass : RemainingAnalytic119.DenseTopThetaMass119
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical120.to119
    (H : EverythingLeftClassical120) :
    RemainingAnalytic119.EverythingLeftClassical119 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_relative_pnt :=
    uniformRelativeCofactorPNT_from_legal120 H.cofactor_pointwise_pnt
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_theta_mass := H.dense_theta_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame120
    (H : EverythingLeftClassical120) : MainStatement :=
  RemainingAnalytic119.candidate_main_from_classical_endgame119 H.to119

theorem positive_lower_density_from_classical_endgame120
    (H : EverythingLeftClassical120) : PositiveLowerDensity D6 :=
  RemainingAnalytic119.positive_lower_density_from_classical_endgame119 H.to119

theorem everything_left_outputs_from_classical120
    (H : EverythingLeftClassical120) : EverythingLeftOutputs47 :=
  RemainingAnalytic119.everything_left_outputs_from_classical119 H.to119

-- Historical audit output: #print axioms cofactorKernelTerm_eq_main120
-- Historical audit output: #print axioms cofactorPNTErrorTerm_eq_main120
-- Historical audit output: #print axioms uniformRelativeCofactorPNT_from_legal120
-- Historical audit output: #print axioms candidate_main_from_classical_endgame120
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame120
-- Historical audit output: #print axioms everything_left_outputs_from_classical120


end RemainingAnalytic120


/-! ## 121. Cofactor PNT: remove A and the power cutoff from the external theorem

Repair 120 exposed the actual normalized prime-count estimate, but its
statement still mentioned membership in `A` and the special cofactor cutoff
`r <= X^alpha`. Neither belongs to the prime number theorem.

Repair 121 replaces that input by a scale-uniform theorem that knows only
that `r` is positive and that `X/r` is sufficiently large, encoded by
`Y * r <= X`. The fact that every legal cofactor eventually satisfies this
scale condition is elementary power domination because `alpha < 1`.
-/

namespace RemainingAnalytic121

open scoped BigOperators
open RemainingAnalytic117 RemainingAnalytic118 RemainingAnalytic119
open RemainingAnalytic120

/-- A set-independent, scale-uniform prime-count asymptotic.

For every relative error `ρ`, there is a lower scale `Y` such that whenever
`X/r >= Y` (encoded integrally as `Y*r <= X`), the normalized prime count at
`X/r` has the required relative error. This statement contains no reference
to `A` and no reference to the special exponent `alpha`. -/
def ScaleUniformPrimeCount121 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ Y : ℕ, ∀ X r : ℕ,
    1 ≤ r → Y * r ≤ X →
      |(prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
          1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))|
        ≤
      ρ * (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))))

/-- Since `alpha = 1/100 < 1`, every fixed scale `Y` is eventually smaller
than `X^(1-alpha)`. Hence a legal cofactor `r <= X^alpha` satisfies
`Y*r <= X` for all sufficiently large `X`. -/
theorem eventually_scale_condition121
    (Y : ℕ) :
    ∃ N : ℕ, ∀ X r : ℕ, N ≤ X →
      r ∈ Finset.Icc 1 X →
      (r : ℝ) ≤ (X : ℝ) ^ alpha →
      Y * r ≤ X := by
  have hgap : 0 < (1 : ℝ) - alpha := by
    norm_num [alpha]
  obtain ⟨N0, hN0⟩ :=
    RemainingAnalytic55.fixed_lt_rpow_eventually55
      (gap := (1 : ℝ) - alpha) (C := (Y : ℝ)) hgap
  refine ⟨max 1 N0, ?_⟩
  intro X r hX hr hrpow
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXN : N0 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hYpow :
      (Y : ℝ) < (X : ℝ) ^ ((1 : ℝ) - alpha) :=
    hN0 X hXN
  have hpowpos : 0 < (X : ℝ) ^ alpha :=
    Real.rpow_pos_of_pos hXpos _
  have hmul1 :
      (Y : ℝ) * (r : ℝ) ≤
        (Y : ℝ) * (X : ℝ) ^ alpha :=
    mul_le_mul_of_nonneg_left hrpow (by positivity)
  have hmul2 :
      (Y : ℝ) * (X : ℝ) ^ alpha <
        (X : ℝ) ^ ((1 : ℝ) - alpha) * (X : ℝ) ^ alpha :=
    mul_lt_mul_of_pos_right hYpow hpowpos
  have hdecomp :
      (X : ℝ) ^ ((1 : ℝ) - alpha) * (X : ℝ) ^ alpha =
        (X : ℝ) := by
    rw [← Real.rpow_add hXpos]
    have hsum : ((1 : ℝ) - alpha) + alpha = (1 : ℝ) := by
      ring
    rw [hsum, Real.rpow_one]
  have hreal : (Y : ℝ) * (r : ℝ) < (X : ℝ) := by
    calc
      (Y : ℝ) * (r : ℝ)
          ≤ (Y : ℝ) * (X : ℝ) ^ alpha := hmul1
      _ < (X : ℝ) ^ ((1 : ℝ) - alpha) * (X : ℝ) ^ alpha := hmul2
      _ = (X : ℝ) := hdecomp
  have hnat : Y * r < X := by
    exact_mod_cast hreal
  omega

/-- The scale-uniform PNT theorem implies Repair 120's legal-cofactor theorem.
All dependence on `A` and on the cutoff `r <= X^alpha` is now internal. -/
theorem legalPointwiseCofactorPNT_from_scale121
    (H : ScaleUniformPrimeCount121) :
    LegalPointwiseCofactorPNT120 := by
  intro ρ hρ
  obtain ⟨Y, hY⟩ := H ρ hρ
  obtain ⟨Nscale, hscale⟩ := eventually_scale_condition121 Y
  refine ⟨max Nscale 2, ?_⟩
  intro X hX r hr hrA hrpow
  have hXN : Nscale ≤ X := by
    exact le_trans (le_max_left Nscale 2)
      (le_trans (le_max_left (max Nscale 2) 2) hX)
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hYr : Y * r ≤ X :=
    hscale X r hXN hr hrpow
  exact hY X r hr1 hYr

/-- Repair-121 endgame: the PNT boundary is now independent of the arithmetic
set `A` and independent of the manuscript-specific cofactor exponent. -/
structure EverythingLeftClassical121 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  scale_uniform_pnt : ScaleUniformPrimeCount121
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_theta_mass : RemainingAnalytic119.DenseTopThetaMass119
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical121.to120
    (H : EverythingLeftClassical121) :
    RemainingAnalytic120.EverythingLeftClassical120 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  cofactor_pointwise_pnt :=
    legalPointwiseCofactorPNT_from_scale121 H.scale_uniform_pnt
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_theta_mass := H.dense_theta_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame121
    (H : EverythingLeftClassical121) : MainStatement :=
  RemainingAnalytic120.candidate_main_from_classical_endgame120 H.to120

theorem positive_lower_density_from_classical_endgame121
    (H : EverythingLeftClassical121) : PositiveLowerDensity D6 :=
  RemainingAnalytic120.positive_lower_density_from_classical_endgame120 H.to120

theorem everything_left_outputs_from_classical121
    (H : EverythingLeftClassical121) : EverythingLeftOutputs47 :=
  RemainingAnalytic120.everything_left_outputs_from_classical120 H.to120

-- Historical audit output: #print axioms eventually_scale_condition121
-- Historical audit output: #print axioms legalPointwiseCofactorPNT_from_scale121
-- Historical audit output: #print axioms candidate_main_from_classical_endgame121
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame121
-- Historical audit output: #print axioms everything_left_outputs_from_classical121


end RemainingAnalytic121


/-! ## 122. Split the scale-uniform PNT into standard PNT + floor/log normalization

Repair 121 removes the arithmetic set `A` from the PNT boundary. The next
step is to separate genuine prime-number-theorem content from the elementary
fact that `X / r` is a floor approximation to `X/r`.

The two inputs below are intentionally different in character:

* `OneVariablePrimeCountPNT122` is the usual one-variable relative PNT.
* `FloorLogNormalizationTransfer122` contains no new prime-distribution
  information: it says that, once the one-variable estimate is known at
  `n = X/r`, the floor and logarithm normalizations transfer it to the exact
  cofactor expression used by the manuscript.

This makes the remaining formalization target much sharper: the second item
should ultimately be eliminated by elementary real/Nat inequalities.
-/

namespace RemainingAnalytic122

open scoped BigOperators
open RemainingAnalytic121

/-- Standard one-variable relative PNT, stated for the `prefixCount`
normalization used throughout this file. -/
def OneVariablePrimeCountPNT122 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    |(prefixCount {p : ℕ | p.Prime} n : ℝ) / (n : ℝ) -
        1 / Real.log (n : ℝ)|
      ≤
    ρ * (1 / Real.log (n : ℝ))

/-- Pure normalization transfer from `n = X/r` to the exact cofactor scale.

No prime-distribution theorem is hidden here: the prime-count expression
appears only through the assumed one-variable estimate `hlocal`. The
remaining work is floor control and comparison of `log (X/r : Nat)` with
`log ((X:ℝ)/(r:ℝ))`. -/
def FloorLogNormalizationTransfer122 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ Y : ℕ, ∀ X r : ℕ,
    1 ≤ r → Y * r ≤ X →
    let n := X / r
    (|(prefixCount {p : ℕ | p.Prime} n : ℝ) / (n : ℝ) -
        1 / Real.log (n : ℝ)|
      ≤
      (ρ / 2) * (1 / Real.log (n : ℝ))) →
    |(prefixCount {p : ℕ | p.Prime} n : ℝ) / (X : ℝ) -
        1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))|
      ≤
    ρ * (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))))

/-- Standard PNT plus the elementary floor/log transfer imply the
scale-uniform prime-count input of Repair 121. -/
theorem scaleUniformPrimeCount_from_split122
    (HPNT : OneVariablePrimeCountPNT122)
    (Hnorm : FloorLogNormalizationTransfer122) :
    ScaleUniformPrimeCount121 := by
  intro ρ hρ
  have hρ2 : 0 < ρ / 2 := by linarith
  obtain ⟨N, hN2, hPNT⟩ := HPNT (ρ / 2) hρ2
  obtain ⟨Y0, hnorm⟩ := Hnorm ρ hρ
  refine ⟨max N Y0, ?_⟩
  intro X r hr hscale
  have hrpos : 0 < r := by omega
  have hNr : N * r ≤ X := by
    exact le_trans
      (Nat.mul_le_mul_right r (le_max_left N Y0))
      hscale
  have hnr : N ≤ X / r := by
    exact (Nat.le_div_iff_mul_le hrpos).2 hNr
  have hlocal := hPNT (X / r) hnr
  have hY0r : Y0 * r ≤ X := by
    exact le_trans
      (Nat.mul_le_mul_right r (le_max_right N Y0))
      hscale
  exact hnorm X r hr hY0r hlocal

/-- Repair-122 endgame: the cofactor prime-count input is split into a
standard one-variable PNT and an explicitly elementary normalization target. -/
structure EverythingLeftClassical122 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  one_variable_pnt : OneVariablePrimeCountPNT122
  floor_log_normalization : FloorLogNormalizationTransfer122
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_theta_mass : RemainingAnalytic119.DenseTopThetaMass119
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical122.to121
    (H : EverythingLeftClassical122) :
    RemainingAnalytic121.EverythingLeftClassical121 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  scale_uniform_pnt :=
    scaleUniformPrimeCount_from_split122
      H.one_variable_pnt H.floor_log_normalization
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_theta_mass := H.dense_theta_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame122
    (H : EverythingLeftClassical122) : MainStatement :=
  RemainingAnalytic121.candidate_main_from_classical_endgame121 H.to121

theorem positive_lower_density_from_classical_endgame122
    (H : EverythingLeftClassical122) : PositiveLowerDensity D6 :=
  RemainingAnalytic121.positive_lower_density_from_classical_endgame121 H.to121

theorem everything_left_outputs_from_classical122
    (H : EverythingLeftClassical122) : EverythingLeftOutputs47 :=
  RemainingAnalytic121.everything_left_outputs_from_classical121 H.to121

-- Historical audit output: #print axioms legalPointwiseCofactorPNT_from_scale121
-- Historical audit output: #print axioms scaleUniformPrimeCount_from_split122
-- Historical audit output: #print axioms candidate_main_from_classical_endgame122
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame122
-- Historical audit output: #print axioms everything_left_outputs_from_classical122


end RemainingAnalytic122


/-! ## 123. Put the PNT input in standard unnormalized form; harden floor control

Repair 122 split the cofactor estimate into one-variable PNT plus an elementary
floor/log transfer.  This section pushes both sides:

1. the one-variable PNT is replaced by the more standard statement
      |pi(n) - n/log n| <= rho * n/log n;
   the normalized version is proved from it;
2. several exact Nat-division lemmas are recorded for the future elimination
   of `FloorLogNormalizationTransfer122`.

The remaining normalization hypothesis is therefore isolated from the genuine
prime-distribution theorem.
-/

namespace RemainingAnalytic123

open scoped BigOperators
open RemainingAnalytic121 RemainingAnalytic122

/-- Standard relative-error PNT around `n / log n`, before dividing by `n`. -/
def PrimeCountRelativePNT123 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    |(prefixCount {p : ℕ | p.Prime} n : ℝ) -
        (n : ℝ) / Real.log (n : ℝ)|
      ≤
    ρ * ((n : ℝ) / Real.log (n : ℝ))

/-- Exact lower floor inequality, retained in Nat form. -/
theorem natDiv_mul_le123 (X r : ℕ) :
    (X / r) * r ≤ X := by
  exact Nat.div_mul_le_self X r

/-- Exact upper floor inequality for a positive divisor. -/
theorem X_lt_succ_natDiv_mul123
    {X r : ℕ} (hr : 1 ≤ r) :
    X < (X / r + 1) * r := by
  have hrpos : 0 < r := by omega
  have hmod : X % r < r := Nat.mod_lt X hrpos
  have hdecomp : r * (X / r) + X % r = X := Nat.div_add_mod X r
  calc
    X = r * (X / r) + X % r := hdecomp.symm
    _ < r * (X / r) + r := Nat.add_lt_add_left hmod _
    _ = (X / r + 1) * r := by ring

/-- A scale condition `Y*r <= X` is exactly what is needed to force
`Y <= floor(X/r)`. -/
theorem scale_le_natDiv123
    {X r Y : ℕ} (hr : 1 ≤ r) (hscale : Y * r ≤ X) :
    Y ≤ X / r := by
  have hrpos : 0 < r := by omega
  exact (Nat.le_div_iff_mul_le hrpos).2 hscale

/-- In particular, the scale condition with `Y >= 2` puts the natural quotient
in the positive-log regime. -/
theorem two_le_natDiv_of_scale123
    {X r Y : ℕ} (hr : 1 ≤ r) (hY : 2 ≤ Y) (hscale : Y * r ≤ X) :
    2 ≤ X / r := by
  exact le_trans hY (scale_le_natDiv123 hr hscale)

/-- The standard unnormalized relative PNT implies the normalized
one-variable PNT used in Repair 122. -/
theorem oneVariablePrimeCountPNT_from_relative123
    (H : PrimeCountRelativePNT123) :
    OneVariablePrimeCountPNT122 := by
  intro ρ hρ
  obtain ⟨N, hN2, hN⟩ := H ρ hρ
  refine ⟨N, hN2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans hN2 hn
  have hnposNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hraw := hN n hn
  have hid :
      (prefixCount {p : ℕ | p.Prime} n : ℝ) / (n : ℝ) -
          1 / Real.log (n : ℝ)
        =
      ((prefixCount {p : ℕ | p.Prime} n : ℝ) -
          (n : ℝ) / Real.log (n : ℝ)) / (n : ℝ) := by
    field_simp [hn0]
  rw [hid, abs_div, abs_of_pos hnpos]
  have hdiv :=
    div_le_div_of_nonneg_right hraw (le_of_lt hnpos)
  calc
    |(prefixCount {p : ℕ | p.Prime} n : ℝ) -
        (n : ℝ) / Real.log (n : ℝ)| / (n : ℝ)
        ≤
      (ρ * ((n : ℝ) / Real.log (n : ℝ))) / (n : ℝ) := hdiv
    _ = ρ * (1 / Real.log (n : ℝ)) := by
      field_simp [hn0]

/-- Repair-123 endgame: the PNT field is now the usual relative error around
`n/log n`; all manuscript-specific normalization remains isolated in the
explicitly elementary floor/log transfer. -/
structure EverythingLeftClassical123 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47

  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47

  prime_count_relative_pnt : PrimeCountRelativePNT123
  floor_log_normalization : FloorLogNormalizationTransfer122
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115

  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47

  dense_theta_mass : RemainingAnalytic119.DenseTopThetaMass119
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47

  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical123.to122
    (H : EverythingLeftClassical123) :
    RemainingAnalytic122.EverythingLeftClassical122 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  one_variable_pnt :=
    oneVariablePrimeCountPNT_from_relative123 H.prime_count_relative_pnt
  floor_log_normalization := H.floor_log_normalization
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_theta_mass := H.dense_theta_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame123
    (H : EverythingLeftClassical123) : MainStatement :=
  RemainingAnalytic122.candidate_main_from_classical_endgame122 H.to122

theorem positive_lower_density_from_classical_endgame123
    (H : EverythingLeftClassical123) : PositiveLowerDensity D6 :=
  RemainingAnalytic122.positive_lower_density_from_classical_endgame122 H.to122

theorem everything_left_outputs_from_classical123
    (H : EverythingLeftClassical123) : EverythingLeftOutputs47 :=
  RemainingAnalytic122.everything_left_outputs_from_classical122 H.to122

-- Historical audit output: #print axioms natDiv_mul_le123
-- Historical audit output: #print axioms X_lt_succ_natDiv_mul123
-- Historical audit output: #print axioms scale_le_natDiv123
-- Historical audit output: #print axioms two_le_natDiv_of_scale123
-- Historical audit output: #print axioms oneVariablePrimeCountPNT_from_relative123
-- Historical audit output: #print axioms candidate_main_from_classical_endgame123
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame123
-- Historical audit output: #print axioms everything_left_outputs_from_classical123


end RemainingAnalytic123


/-! ## 124. Quantitative floor-control lemmas for the normalization transfer

Repair 123 isolated the remaining elementary normalization problem.  Repair 124
builds the real-variable floor estimates needed to remove that hypothesis.

For `n = X / r` and `r > 0` we prove:
  * `n <= X/r < n+1` over the reals;
  * if `Y*r <= X` and `Y >= 2`, then `n >= 2`, hence `log n > 0`;
  * the relative floor discrepancy between `n*r/X` and `1` is bounded by
    `1/n`.

These are the exact deterministic ingredients needed for the next logarithm
comparison step.
-/

namespace RemainingAnalytic124

open scoped BigOperators
open RemainingAnalytic121 RemainingAnalytic122 RemainingAnalytic123

theorem natDiv_real_lower124
    {X r : ℕ} (hr : 1 ≤ r) :
    ((X / r : ℕ) : ℝ) ≤ (X : ℝ) / (r : ℝ) := by
  exact RemainingAnalytic52.natDivCastLeRealDiv_proved52 X r hr

theorem natDiv_real_upper124
    {X r : ℕ} (hr : 1 ≤ r) :
    (X : ℝ) / (r : ℝ) < ((X / r : ℕ) : ℝ) + 1 := by
  have hrposNat : 0 < r := by omega
  have hnat := X_lt_succ_natDiv_mul123 (X := X) (r := r) hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrposNat
  have hreal :
      (X : ℝ) < ((((X / r : ℕ) + 1 : ℕ) : ℝ) * (r : ℝ)) := by
    exact_mod_cast hnat
  have := (div_lt_iff₀ hrpos).2 hreal
  norm_num at this ⊢
  simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using this

theorem natDiv_log_pos124
    {X r Y : ℕ}
    (hr : 1 ≤ r) (hY : 2 ≤ Y) (hscale : Y * r ≤ X) :
    0 < Real.log ((X / r : ℕ) : ℝ) := by
  have hn2 : 2 ≤ X / r :=
    two_le_natDiv_of_scale123 hr hY hscale
  have h1 : (1 : ℝ) < ((X / r : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < X / r by omega)
  exact Real.log_pos h1

theorem natDiv_pos_real124
    {X r Y : ℕ}
    (hr : 1 ≤ r) (hY : 1 ≤ Y) (hscale : Y * r ≤ X) :
    (0 : ℝ) < ((X / r : ℕ) : ℝ) := by
  have hn1 : 1 ≤ X / r :=
    le_trans hY (scale_le_natDiv123 hr hscale)
  exact_mod_cast (show 0 < X / r by omega)

/-- The floor quotient misses the exact real quotient by less than one unit. -/
theorem natDiv_floor_gap_lt_one124
    {X r : ℕ} (hr : 1 ≤ r) :
    0 ≤ (X : ℝ) / (r : ℝ) - ((X / r : ℕ) : ℝ) ∧
    (X : ℝ) / (r : ℝ) - ((X / r : ℕ) : ℝ) < 1 := by
  constructor
  · linarith [natDiv_real_lower124 (X := X) (r := r) hr]
  · linarith [natDiv_real_upper124 (X := X) (r := r) hr]

/-- Quantitative relative floor error:
`1 - n*r/X <= 1/n`, where `n = floor(X/r)`. -/
theorem floor_relative_error_le_inv_natDiv124
    {X r Y : ℕ}
    (hr : 1 ≤ r) (hY : 1 ≤ Y) (hscale : Y * r ≤ X) :
    0 ≤
      1 - ((((X / r : ℕ) : ℝ) * (r : ℝ)) / (X : ℝ)) ∧
    1 - ((((X / r : ℕ) : ℝ) * (r : ℝ)) / (X : ℝ))
      ≤ 1 / ((X / r : ℕ) : ℝ) := by
  have hrposNat : 0 < r := by omega
  have hYr_ge_r : r ≤ Y * r := by
    have hmul := Nat.mul_le_mul_right r hY
    simpa [one_mul] using hmul
  have hrX : r ≤ X := le_trans hYr_ge_r hscale
  have hXposNat : 0 < X := lt_of_lt_of_le hrposNat hrX
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrposNat
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXposNat
  have hnpos : (0 : ℝ) < ((X / r : ℕ) : ℝ) :=
    natDiv_pos_real124 hr hY hscale
  have hmulNat := natDiv_mul_le123 X r
  have hmul :
      (((X / r : ℕ) : ℝ) * (r : ℝ)) ≤ (X : ℝ) := by
    exact_mod_cast hmulNat
  constructor
  · have hfrac :
        ((((X / r : ℕ) : ℝ) * (r : ℝ)) / (X : ℝ)) ≤ 1 := by
      exact (div_le_one hXpos).2 hmul
    linarith
  · have hupper := natDiv_real_upper124 (X := X) (r := r) hr
    have hxn :
        (X : ℝ) < ((((X / r : ℕ) : ℝ) + 1) * (r : ℝ)) := by
      exact (div_lt_iff₀ hrpos).1 hupper
    have hkey :
        (X : ℝ) - (((X / r : ℕ) : ℝ) * (r : ℝ)) < (r : ℝ) := by
      linarith
    have hXge :
        ((X / r : ℕ) : ℝ) * (r : ℝ) ≤ (X : ℝ) := hmul
    have hden :
        ((X / r : ℕ) : ℝ) * (r : ℝ) > 0 := mul_pos hnpos hrpos
    have hx_ge_nr :
        1 / (X : ℝ) ≤
          1 / (((X / r : ℕ) : ℝ) * (r : ℝ)) := by
      exact one_div_le_one_div_of_le hden hXge
    have hdiff :
        1 - ((((X / r : ℕ) : ℝ) * (r : ℝ)) / (X : ℝ))
          =
        ((X : ℝ) - (((X / r : ℕ) : ℝ) * (r : ℝ))) / (X : ℝ) := by
      field_simp [ne_of_gt hXpos]
    rw [hdiff]
    have hnonneg :
        0 ≤ (X : ℝ) - (((X / r : ℕ) : ℝ) * (r : ℝ)) := by
      linarith
    have hstep :
        ((X : ℝ) - (((X / r : ℕ) : ℝ) * (r : ℝ))) / (X : ℝ)
          <
        (r : ℝ) / (X : ℝ) := by
      exact (div_lt_div_iff_of_pos_right hXpos).2 hkey
    have hrx :
        (r : ℝ) / (X : ℝ) ≤
          1 / ((X / r : ℕ) : ℝ) := by
      have hrewrite :
          (r : ℝ) / (X : ℝ) =
            (r : ℝ) * (1 / (X : ℝ)) := by ring
      rw [hrewrite]
      calc
        (r : ℝ) * (1 / (X : ℝ))
            ≤ (r : ℝ) *
                (1 / (((X / r : ℕ) : ℝ) * (r : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hx_ge_nr (le_of_lt hrpos)
        _ = 1 / ((X / r : ℕ) : ℝ) := by
              field_simp [ne_of_gt hnpos, ne_of_gt hrpos]
    exact le_of_lt (lt_of_lt_of_le hstep hrx)

/-- Repair-124 retains the same endgame assumptions as Repair 123; its purpose
is to move the normalization transfer toward a proof rather than a hypothesis. -/
abbrev EverythingLeftClassical124 := EverythingLeftClassical123

theorem candidate_main_from_classical_endgame124
    (H : EverythingLeftClassical124) : MainStatement :=
  candidate_main_from_classical_endgame123 H

theorem positive_lower_density_from_classical_endgame124
    (H : EverythingLeftClassical124) : PositiveLowerDensity D6 :=
  positive_lower_density_from_classical_endgame123 H

-- Historical audit output: #print axioms oneVariablePrimeCountPNT_from_relative123
-- Historical audit output: #print axioms natDiv_real_lower124
-- Historical audit output: #print axioms natDiv_real_upper124
-- Historical audit output: #print axioms natDiv_log_pos124
-- Historical audit output: #print axioms natDiv_floor_gap_lt_one124
-- Historical audit output: #print axioms floor_relative_error_le_inv_natDiv124
-- Historical audit output: #print axioms candidate_main_from_classical_endgame124
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame124


end RemainingAnalytic124


/-! ## 125. Decompose the last floor/log normalization into two deterministic targets

The remaining `FloorLogNormalizationTransfer122` mixes two effects:
1. rescaling the PNT error from denominator `n = X/r` to denominator `X`;
2. changing the main term from `n/(X log n)` to
   `1/(r log((X:ℝ)/(r:ℝ)))`.

Repair 125 separates these.  The bridge below is pure triangle inequality,
so subsequent work can prove the two deterministic pieces independently.
-/

namespace RemainingAnalytic125

open scoped BigOperators
open RemainingAnalytic121 RemainingAnalytic122 RemainingAnalytic123
open RemainingAnalytic124

/-- Transfer only the stochastic/PNT error part from `n`-normalization to
`X`-normalization. -/
def PrimeErrorRescaling125 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ Y : ℕ, ∀ X r : ℕ,
    1 ≤ r → Y * r ≤ X →
    let n := X / r
    (|(prefixCount {p : ℕ | p.Prime} n : ℝ) / (n : ℝ) -
        1 / Real.log (n : ℝ)|
      ≤
      (ρ / 2) * (1 / Real.log (n : ℝ))) →
    |(prefixCount {p : ℕ | p.Prime} n : ℝ) / (X : ℝ) -
        (n : ℝ) / ((X : ℝ) * Real.log (n : ℝ))|
      ≤
    (ρ / 2) *
      (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))))

/-- Transfer only the deterministic main term across the floor/log
normalization. -/
def MainTermFloorLogTransfer125 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ Y : ℕ, ∀ X r : ℕ,
    1 ≤ r → Y * r ≤ X →
    let n := X / r
    |(n : ℝ) / ((X : ℝ) * Real.log (n : ℝ)) -
        1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))|
      ≤
    (ρ / 2) *
      (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))))

/-- The two deterministic normalization pieces imply the Repair-122
floor/log normalization theorem. -/
theorem floorLogNormalization_from_two125
    (Herr : PrimeErrorRescaling125)
    (Hmain : MainTermFloorLogTransfer125) :
    FloorLogNormalizationTransfer122 := by
  intro ρ hρ
  obtain ⟨Yerr, hYerr⟩ := Herr ρ hρ
  obtain ⟨Ymain, hYmain⟩ := Hmain ρ hρ
  refine ⟨max Yerr Ymain, ?_⟩
  intro X r hr hscale
  dsimp
  intro hlocal
  have hErrScale : Yerr * r ≤ X := by
    exact le_trans
      (Nat.mul_le_mul_right r (le_max_left Yerr Ymain))
      hscale
  have hMainScale : Ymain * r ≤ X := by
    exact le_trans
      (Nat.mul_le_mul_right r (le_max_right Yerr Ymain))
      hscale
  have herr := hYerr X r hr hErrScale hlocal
  have hmain := hYmain X r hr hMainScale
  have htri :
      |(prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
          1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))|
        ≤
      |(prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
          ((X / r : ℕ) : ℝ) /
            ((X : ℝ) * Real.log ((X / r : ℕ) : ℝ))| +
      |((X / r : ℕ) : ℝ) /
            ((X : ℝ) * Real.log ((X / r : ℕ) : ℝ)) -
          1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))| := by
    simpa only [sub_eq_add_neg] using
      (abs_sub_le
        ((prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ))
        (((X / r : ℕ) : ℝ) /
          ((X : ℝ) * Real.log ((X / r : ℕ) : ℝ)))
        (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))))
  calc
    |(prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
        1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))|
      ≤
    |(prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) / (X : ℝ) -
        ((X / r : ℕ) : ℝ) /
          ((X : ℝ) * Real.log ((X / r : ℕ) : ℝ))| +
    |((X / r : ℕ) : ℝ) /
          ((X : ℝ) * Real.log ((X / r : ℕ) : ℝ)) -
        1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))| := htri
    _ ≤
      (ρ / 2) *
          (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))) +
      (ρ / 2) *
          (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))) := by
            exact add_le_add herr hmain
    _ =
      ρ * (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))) := by
            ring

/-- New endgame interface with the normalization transfer decomposed into
two smaller deterministic pieces. -/
structure EverythingLeftClassical125 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47
  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47
  prime_count_relative_pnt : PrimeCountRelativePNT123
  prime_error_rescaling : PrimeErrorRescaling125
  main_term_floor_log : MainTermFloorLogTransfer125
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115
  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47
  dense_theta_mass : RemainingAnalytic119.DenseTopThetaMass119
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47
  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical125.to123
    (H : EverythingLeftClassical125) :
    RemainingAnalytic123.EverythingLeftClassical123 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  prime_count_relative_pnt := H.prime_count_relative_pnt
  floor_log_normalization :=
    floorLogNormalization_from_two125
      H.prime_error_rescaling H.main_term_floor_log
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_theta_mass := H.dense_theta_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame125
    (H : EverythingLeftClassical125) : MainStatement :=
  RemainingAnalytic123.candidate_main_from_classical_endgame123 H.to123

theorem positive_lower_density_from_classical_endgame125
    (H : EverythingLeftClassical125) : PositiveLowerDensity D6 :=
  RemainingAnalytic123.positive_lower_density_from_classical_endgame123 H.to123

-- Historical audit output: #print axioms natDiv_real_lower124
-- Historical audit output: #print axioms floor_relative_error_le_inv_natDiv124
-- Historical audit output: #print axioms floorLogNormalization_from_two125
-- Historical audit output: #print axioms candidate_main_from_classical_endgame125
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame125


end RemainingAnalytic125


/-! ## 126. Reduce prime-error rescaling to a deterministic kernel comparison

Repair 125 now has the correct error budget.  This section proves the exact
algebraic rescaling identity and shows that `PrimeErrorRescaling125` follows
from a single floor/log kernel comparison.

The remaining comparison is deterministic:
  (n / X) * (1 / log n)
    <= 1 / (r * log (X/r)),
where `n = floor(X/r)`, once the scale is large enough.

Equivalently, after substituting `q = X/r`, this is the monotonicity of
`log x / x` on the large range, plus the floor relation `n <= q < n+1`.
-/

namespace RemainingAnalytic126

open scoped BigOperators
open RemainingAnalytic121 RemainingAnalytic122 RemainingAnalytic123
open RemainingAnalytic124 RemainingAnalytic125

/-- Exact algebraic identity behind the prime-error rescaling. -/
theorem primeError_rescale_identity126
    {X n : ℕ}
    (hX : 0 < X) (hn : 2 ≤ n) :
    (prefixCount {p : ℕ | p.Prime} n : ℝ) / (X : ℝ) -
        (n : ℝ) / ((X : ℝ) * Real.log (n : ℝ))
      =
    ((n : ℝ) / (X : ℝ)) *
      ((prefixCount {p : ℕ | p.Prime} n : ℝ) / (n : ℝ) -
        1 / Real.log (n : ℝ)) := by
  have hX0 : (X : ℝ) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt hlogpos
  field_simp [hX0, hn0, hlog0] <;> ring

/-- Deterministic kernel comparison sufficient to rescale the one-variable
relative PNT error to the cofactor normalization. -/
def FloorKernelComparison126 : Prop :=
  ∃ Y : ℕ, 3 ≤ Y ∧ ∀ X r : ℕ,
    1 ≤ r → Y * r ≤ X →
    let n := X / r
    ((n : ℝ) / (X : ℝ)) * (1 / Real.log (n : ℝ))
      ≤
    1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))

/-- The exact identity plus the deterministic kernel comparison prove the
entire `PrimeErrorRescaling125` hypothesis. -/
theorem primeErrorRescaling_from_kernel126
    (Hkernel : FloorKernelComparison126) :
    PrimeErrorRescaling125 := by
  intro ρ hρ
  obtain ⟨Y, hY3, hkernel⟩ := Hkernel
  refine ⟨Y, ?_⟩
  intro X r hr hscale
  dsimp
  intro hlocal
  have hn3 : 3 ≤ X / r :=
    le_trans hY3 (scale_le_natDiv123 hr hscale)
  have hn2 : 2 ≤ X / r := le_trans (by omega) hn3
  have hrpos : 0 < r := by omega
  have hYrpos : 0 < Y * r := Nat.mul_pos (by omega) hrpos
  have hXpos : 0 < X := lt_of_lt_of_le hYrpos hscale
  have hnX_nonneg :
      0 ≤ (((X / r : ℕ) : ℝ) / (X : ℝ)) := by
    positivity
  have hid := primeError_rescale_identity126
    (X := X) (n := X / r) hXpos hn2
  rw [hid, abs_mul]
  have hnabs :
      |((X / r : ℕ) : ℝ) / (X : ℝ)| =
        ((X / r : ℕ) : ℝ) / (X : ℝ) := by
    exact abs_of_nonneg hnX_nonneg
  rw [hnabs]
  have hmul :=
    mul_le_mul_of_nonneg_left hlocal hnX_nonneg
  have hk := hkernel X r hr hscale
  have hρhalf_nonneg : 0 ≤ ρ / 2 := by linarith
  calc
    (((X / r : ℕ) : ℝ) / (X : ℝ)) *
        |(prefixCount {p : ℕ | p.Prime} (X / r) : ℝ) /
            ((X / r : ℕ) : ℝ) -
          1 / Real.log ((X / r : ℕ) : ℝ)|
      ≤
    (((X / r : ℕ) : ℝ) / (X : ℝ)) *
        ((ρ / 2) * (1 / Real.log ((X / r : ℕ) : ℝ))) := hmul
    _ =
      (ρ / 2) *
        ((((X / r : ℕ) : ℝ) / (X : ℝ)) *
          (1 / Real.log ((X / r : ℕ) : ℝ))) := by ring
    _ ≤
      (ρ / 2) *
        (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left hk hρhalf_nonneg

/-- Endgame after eliminating `PrimeErrorRescaling125` as an independent
external hypothesis. -/
structure EverythingLeftClassical126 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  legal_auxiliary_thresholds : Remaining_LegalAuxiliaryThresholds47
  four_code_cardinality : Remaining_FourCodeCardinality47
  five_code_cardinality : Remaining_FiveCodeCardinality47
  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47
  prime_count_relative_pnt : PrimeCountRelativePNT123
  floor_kernel_comparison : FloorKernelComparison126
  main_term_floor_log : MainTermFloorLogTransfer125
  cofactor_density_kernel : RemainingAnalytic115.DensityCofactorKernelLimit115
  pnt : Remaining_PNTPackage47
  harman : Remaining_Harman47
  dense_theta_mass : RemainingAnalytic119.DenseTopThetaMass119
  sparse_weighted_transfer : Remaining_SparseWeightedTransfer47
  prop51_classical : ClassicalAnalyticCore101

def EverythingLeftClassical126.to125
    (H : EverythingLeftClassical126) :
    RemainingAnalytic125.EverythingLeftClassical125 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := H.legal_auxiliary_thresholds
  four_code_cardinality := H.four_code_cardinality
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  prime_count_relative_pnt := H.prime_count_relative_pnt
  prime_error_rescaling :=
    primeErrorRescaling_from_kernel126 H.floor_kernel_comparison
  main_term_floor_log := H.main_term_floor_log
  cofactor_density_kernel := H.cofactor_density_kernel
  pnt := H.pnt
  harman := H.harman
  dense_theta_mass := H.dense_theta_mass
  sparse_weighted_transfer := H.sparse_weighted_transfer
  prop51_classical := H.prop51_classical

theorem candidate_main_from_classical_endgame126
    (H : EverythingLeftClassical126) : MainStatement :=
  RemainingAnalytic125.candidate_main_from_classical_endgame125 H.to125

theorem positive_lower_density_from_classical_endgame126
    (H : EverythingLeftClassical126) : PositiveLowerDensity D6 :=
  RemainingAnalytic125.positive_lower_density_from_classical_endgame125 H.to125

-- Historical audit output: #print axioms floorLogNormalization_from_two125
-- Historical audit output: #print axioms primeError_rescale_identity126
-- Historical audit output: #print axioms primeErrorRescaling_from_kernel126
-- Historical audit output: #print axioms candidate_main_from_classical_endgame126
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame126

end RemainingAnalytic126


/-! ## 127. Analytic expansion: actual estimates and explicit remaining inputs

This section adds proofs, not axioms.  Its endgame remains conditional.
No instance of the final analytic input record is asserted to exist.
The new scripts have not been compiled in the preparation environment.

A. Eliminate both floor/log normalization assumptions.
B. Prove a quantitative finite Abel lemma and a density-to-kernel theorem.
C. Derive the dense theta input from one-variable log-squared theta accuracy.
D. Construct sparse packets from canonical counts and from a mass/loss budget.
E. Isolate the canonical Harman exceptional set and prove a second-moment criterion.
F. Reuse dense theta mass for Proposition 5.1's dyadic prime supply.
-/

namespace RemainingAnalytic127

open scoped BigOperators
open RemainingAnalytic117 RemainingAnalytic118 RemainingAnalytic119
open RemainingAnalytic120 RemainingAnalytic121 RemainingAnalytic122
open RemainingAnalytic123 RemainingAnalytic124 RemainingAnalytic125
open RemainingAnalytic126

/-- An elementary threshold for any fixed lower bound on the logarithm. -/
theorem eventually_log_ge127 (C : ℝ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → C ≤ Real.log (X : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp C)
  refine ⟨N, ?_⟩
  intro X hX
  have hNX : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have heX : Real.exp C < (X : ℝ) := lt_of_lt_of_le hN hNX
  have hlog := Real.log_lt_log (Real.exp_pos C) heX
  rw [Real.log_exp] at hlog
  exact le_of_lt hlog

/-- The two inequalities that control the floor-normalized main term.
The upper bound uses Mathlib's antitonicity of `log x / x` on `[exp 1, infinity)`.
The lower bound uses only monotonicity of `log`.
-/
theorem floor_main_term_bounds127 {X r : ℕ}
    (hr : 1 ≤ r) (hn2 : 2 ≤ X / r)
    (hne : Real.exp 1 ≤ ((X / r : ℕ) : ℝ)) :
    (((X / r : ℕ) : ℝ) /
        ((X : ℝ) * Real.log ((X / r : ℕ) : ℝ))) ≤
      1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))) ∧
    ((((X / r : ℕ) : ℝ) * (r : ℝ)) / (X : ℝ)) *
        (1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)))) ≤
      ((X / r : ℕ) : ℝ) /
        ((X : ℝ) * Real.log ((X / r : ℕ) : ℝ)) := by
  have hrp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hn1 : (1 : ℝ) < ((X / r : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < X / r by omega)
  have hnp : (0 : ℝ) < ((X / r : ℕ) : ℝ) := by linarith
  have hXp : (0 : ℝ) < (X : ℝ) := by
    have hle := Nat.div_le_self X r
    exact_mod_cast (show 0 < X by omega)
  have hnq := natDiv_real_lower124 (X := X) (r := r) hr
  have hqp : (0 : ℝ) < (X : ℝ) / (r : ℝ) := div_pos hXp hrp
  have hln : 0 < Real.log ((X / r : ℕ) : ℝ) := Real.log_pos hn1
  have hlq : 0 < Real.log ((X : ℝ) / (r : ℝ)) :=
    Real.log_pos (lt_of_lt_of_le hn1 hnq)
  have hlogs : Real.log ((X / r : ℕ) : ℝ) ≤
      Real.log ((X : ℝ) / (r : ℝ)) := Real.log_le_log hnp hnq
  have hmono := Real.log_div_self_antitoneOn
    (show ((X / r : ℕ) : ℝ) ∈ Set.Ici (Real.exp 1) from hne)
    (show (X : ℝ) / (r : ℝ) ∈ Set.Ici (Real.exp 1) from le_trans hne hnq)
    hnq
  have hcross := (div_le_div_iff₀ hqp hnp).1 hmono
  have hcrossR := mul_le_mul_of_nonneg_right hcross (le_of_lt hrp)
  have hqr : ((X : ℝ) / (r : ℝ)) * (r : ℝ) = (X : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt hrp)
  constructor
  · apply (div_le_div_iff₀ (mul_pos hXp hln) (mul_pos hrp hlq)).2
    have hqlog := congrArg (fun z : ℝ => Real.log ((X / r : ℕ) : ℝ) * z) hqr
    nlinarith only [hcrossR, hqlog]
  · have hinv := one_div_le_one_div_of_le hln hlogs
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ ((X / r : ℕ) : ℝ) / (X : ℝ) by positivity)
    convert hmul using 1 <;>
      field_simp [ne_of_gt hrp, ne_of_gt hXp, ne_of_gt hln, ne_of_gt hlq] <;> ring

/-- The former independent floor-kernel hypothesis is discharged. -/
theorem floorKernelComparison_proved127 : FloorKernelComparison126 := by
  obtain ⟨Y, hY⟩ := exists_nat_gt (max (Real.exp 1) (3 : ℝ))
  have hY3 : 3 ≤ Y := by
    have : (3 : ℝ) < (Y : ℝ) := lt_of_le_of_lt (le_max_right _ _) hY
    exact_mod_cast (le_of_lt this)
  have hYe : Real.exp 1 ≤ (Y : ℝ) :=
    le_trans (le_max_left _ _) (le_of_lt hY)
  refine ⟨Y, hY3, ?_⟩
  intro X r hr hscale
  dsimp
  have hYn := scale_le_natDiv123 hr hscale
  have hn2 : 2 ≤ X / r := by omega
  have hne : Real.exp 1 ≤ ((X / r : ℕ) : ℝ) :=
    le_trans hYe (by exact_mod_cast hYn)
  calc
    (((X / r : ℕ) : ℝ) / (X : ℝ)) *
        (1 / Real.log ((X / r : ℕ) : ℝ)) =
      ((X / r : ℕ) : ℝ) /
        ((X : ℝ) * Real.log ((X / r : ℕ) : ℝ)) := by
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
          ring
    _ ≤ _ := (floor_main_term_bounds127 hr hn2 hne).1

/-- Uniform relative error of the deterministic floor/log main term.
No prime-count estimate is used in this theorem. -/
theorem mainTermFloorLogTransfer_proved127 : MainTermFloorLogTransfer125 := by
  intro ρ hρ
  obtain ⟨Y, hY⟩ := exists_nat_gt
    (max (Real.exp 1) (max (3 : ℝ) (2 / ρ)))
  have hYe : Real.exp 1 ≤ (Y : ℝ) :=
    le_trans (le_max_left _ _) (le_of_lt hY)
  have hYthree : (3 : ℝ) ≤ (Y : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_lt hY)
  have hY3 : 3 ≤ Y := by exact_mod_cast hYthree
  have hYρ : 2 / ρ ≤ (Y : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_lt hY)
  refine ⟨Y, ?_⟩
  intro X r hr hscale
  dsimp
  have hYn := scale_le_natDiv123 hr hscale
  have hn2 : 2 ≤ X / r := by omega
  have hnp : (0 : ℝ) < ((X / r : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < X / r by omega)
  have hne : Real.exp 1 ≤ ((X / r : ℕ) : ℝ) :=
    le_trans hYe (by exact_mod_cast hYn)
  have hsmall : 1 / ((X / r : ℕ) : ℝ) ≤ ρ / 2 := by
    have hq : 2 / ρ ≤ ((X / r : ℕ) : ℝ) :=
      le_trans hYρ (by exact_mod_cast hYn)
    have hprod := (div_le_iff₀ hρ).1 hq
    apply (div_le_iff₀ hnp).2
    nlinarith
  have hb := floor_main_term_bounds127 hr hn2 hne
  have hfloor := floor_relative_error_le_inv_natDiv124
    (X := X) (r := r) (Y := Y) hr (by omega) hscale
  have hrp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hn1 : (1 : ℝ) < ((X / r : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < X / r by omega)
  have hlogp : 0 < Real.log ((X : ℝ) / (r : ℝ)) :=
    Real.log_pos (lt_of_lt_of_le hn1 (natDiv_real_lower124 hr))
  have hk : 0 ≤ 1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))) := by
    positivity
  rw [abs_of_nonpos (sub_nonpos.mpr hb.1)]
  have hbound := mul_le_mul_of_nonneg_right (le_trans hfloor.2 hsmall) hk
  nlinarith [hb.2]

/-- Both deterministic normalization hypotheses have now been discharged. -/
theorem floorLogNormalization_proved127 : FloorLogNormalizationTransfer122 :=
  floorLogNormalization_from_two125
    (primeErrorRescaling_from_kernel126 floorKernelComparison_proved127)
    mainTermFloorLogTransfer_proved127

/-- The cofactor PNT now follows from the one-variable relative PNT alone. -/
theorem scaleUniformPrimeCount_from_relative127
    (H : PrimeCountRelativePNT123) : ScaleUniformPrimeCount121 :=
  scaleUniformPrimeCount_from_split122
    (oneVariablePrimeCountPNT_from_relative123 H)
    floorLogNormalization_proved127

/-! ### B. Quantitative summation by parts and density transfer -/

noncomputable def prefixSum127 (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, f i

/-- Exact finite Abel summation, including its endpoint term. -/
theorem finite_abel127 (f w : ℕ → ℝ) (M : ℕ) :
    (∑ i ∈ Finset.range M, f i * w i) =
      prefixSum127 f M * w M +
        ∑ i ∈ Finset.range M,
          prefixSum127 f (i + 1) * (w i - w (i + 1)) := by
  induction M with
  | zero => simp [prefixSum127]
  | succ M ih =>
      have hp : prefixSum127 f (M + 1) = prefixSum127 f M + f M := by
        simp [prefixSum127, Finset.sum_range_succ]
      simp only [Finset.sum_range_succ, Nat.succ_eq_add_one]
      rw [ih, hp]
      ring

/-- Exact evaluation of the affine envelope in the Abel bound. -/
theorem abel_affine_envelope127 (w : ℕ → ℝ) (M : ℕ) (ε C : ℝ) :
    (ε * (M : ℝ) + C) * w M +
        (∑ i ∈ Finset.range M,
          (ε * ((i + 1 : ℕ) : ℝ) + C) * (w i - w (i + 1))) =
      ε * (∑ i ∈ Finset.range M, w i) + C * w 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
      simp only [Finset.sum_range_succ, Nat.succ_eq_add_one]
      push_cast at ih ⊢
      nlinarith only [ih]

/-- A quantitative weighted-discrepancy bound.  In applications `f` is the
centered indicator of a density set. -/
theorem abel_discrepancy_bound127
    (f w : ℕ → ℝ) (M : ℕ) (ε C : ℝ)
    (hprefix : ∀ n : ℕ, n ≤ M → |prefixSum127 f n| ≤ ε * (n : ℝ) + C)
    (hwM : 0 ≤ w M)
    (hdec : ∀ i : ℕ, i < M → w (i + 1) ≤ w i) :
    |∑ i ∈ Finset.range M, f i * w i| ≤
      ε * (∑ i ∈ Finset.range M, w i) + C * w 0 := by
  rw [finite_abel127]
  have htri :
      |prefixSum127 f M * w M +
          ∑ i ∈ Finset.range M, prefixSum127 f (i + 1) * (w i - w (i + 1))| ≤
        |prefixSum127 f M * w M| +
          |∑ i ∈ Finset.range M, prefixSum127 f (i + 1) * (w i - w (i + 1))| := by
    simpa only [Real.norm_eq_abs] using
      (norm_add_le (prefixSum127 f M * w M)
        (∑ i ∈ Finset.range M, prefixSum127 f (i + 1) * (w i - w (i + 1))))
  have hsum :
      |∑ i ∈ Finset.range M, prefixSum127 f (i + 1) * (w i - w (i + 1))| ≤
        ∑ i ∈ Finset.range M,
          (ε * ((i + 1 : ℕ) : ℝ) + C) * (w i - w (i + 1)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range M,
          |prefixSum127 f (i + 1) * (w i - w (i + 1))| := by
            exact abs_finset_sum_le_sum_abs117 _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hiM := Finset.mem_range.mp hi
        have hd : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr (hdec i hiM)
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hprefix (i + 1) (by omega)) hd
  have hend : |prefixSum127 f M * w M| ≤ (ε * (M : ℝ) + C) * w M := by
    rw [abs_mul, abs_of_nonneg hwM]
    exact mul_le_mul_of_nonneg_right (hprefix M le_rfl) hwM
  exact le_trans htri
    (le_trans (add_le_add hend hsum) (le_of_eq (abel_affine_envelope127 w M ε C)))

/-- Explicit reindexing between `range N` and the positive prefix `[1,N]`. -/
theorem sum_range_succ_eq_Icc127 (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, f (i + 1)) = ∑ r ∈ Finset.Icc 1 N, f r := by
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    have hiN := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj hij
    omega
  · intro r hr
    have hrN := Finset.mem_Icc.mp hr
    refine ⟨r - 1, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro i hi
    rfl

/-- Count as an explicit real indicator sum. -/
theorem prefixCount_eq_indicator_sum127 (S : Set ℕ) (N : ℕ) :
    (prefixCount S N : ℝ) =
      ∑ r ∈ Finset.Icc 1 N, (if r ∈ S then (1 : ℝ) else 0) := by
  classical
  unfold prefixCount
  rw [← Finset.sum_filter]
  simp

noncomputable def centeredIndicator127 (S : Set ℕ) (δ : ℝ) (i : ℕ) : ℝ :=
  (if i + 1 ∈ S then 1 else 0) - δ

theorem centered_prefix127 (S : Set ℕ) (δ : ℝ) (N : ℕ) :
    prefixSum127 (centeredIndicator127 S δ) N =
      (prefixCount S N : ℝ) - δ * (N : ℝ) := by
  classical
  unfold prefixSum127 centeredIndicator127
  have hrange :
      (∑ i ∈ Finset.range N, (if i + 1 ∈ S then (1 : ℝ) else 0)) =
        ∑ r ∈ Finset.Icc 1 N, (if r ∈ S then (1 : ℝ) else 0) := by
    exact sum_range_succ_eq_Icc127
      (fun r => if r ∈ S then (1 : ℝ) else 0) N
  have hcount :
      (∑ r ∈ Finset.Icc 1 N, (if r ∈ S then (1 : ℝ) else 0)) =
        (prefixCount S N : ℝ) :=
    (prefixCount_eq_indicator_sum127 S N).symm
  rw [Finset.sum_sub_distrib]
  rw [hrange, hcount]
  simp [nsmul_eq_mul, mul_comm]

/-- A density hypothesis gives a global affine discrepancy envelope.  The
constant covers the finite initial segment; no uniformity is assumed there. -/
theorem density_discrepancy_envelope127 (S : Set ℕ) (δ : ℝ)
    (hD : HasDensity S δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |(prefixCount S n : ℝ) - δ * (n : ℝ)| ≤ ε * (n : ℝ) + C := by
  obtain ⟨N, hN⟩ := hD ε hε
  let C : ℝ := (1 + |δ|) * (N : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst n
    simpa [prefixCount] using hC
  have hnp : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hn0)
  by_cases hNn : N ≤ n
  · have he := hN n hNn
    have hid : (prefixCount S n : ℝ) - δ * (n : ℝ) =
        (proportion S n - δ) * (n : ℝ) := by
      unfold proportion
      field_simp [ne_of_gt hnp] <;> ring
    rw [hid, abs_mul, abs_of_pos hnp]
    have hb := mul_le_mul_of_nonneg_right (le_of_lt he) (le_of_lt hnp)
    linarith
  · have hnN : (n : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show n ≤ N by omega)
    have hcount : (prefixCount S n : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast RemainingAnalytic106.prefixCount_le_self106 S n
    have hcount0 : (0 : ℝ) ≤ (prefixCount S n : ℝ) := by positivity
    have hδup := mul_le_mul_of_nonneg_right (le_abs_self δ) (le_of_lt hnp)
    have hδlo := mul_le_mul_of_nonneg_right (neg_abs_le δ) (le_of_lt hnp)
    have hbound : |(prefixCount S n : ℝ) - δ * (n : ℝ)| ≤
        (1 + |δ|) * (n : ℝ) := by
      apply abs_le.mpr
      constructor <;> nlinarith
    have hfinite : (1 + |δ|) * (n : ℝ) ≤ C := by
      exact mul_le_mul_of_nonneg_left hnN (by positivity)
    have he0 : 0 ≤ ε * (n : ℝ) := by positivity
    linarith

/-- A regular, bounded, vanishing-head row kernel kills centered density
indicators.  This is the density-theoretic part, proved independently of primes. -/
theorem centered_kernel_tends_zero127
    (S : Set ℕ) (δ : ℝ) (hD : HasDensity S δ)
    (w : ℕ → ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hregular : ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (∀ i : ℕ, 0 ≤ w X i) ∧ Antitone (w X) ∧
      (∑ i ∈ Finset.range X, w X i) ≤ B)
    (hhead : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X → w X 0 < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      |∑ i ∈ Finset.range X, centeredIndicator127 S δ i * w X i| < ε := by
  intro ε hε
  let η : ℝ := ε / (2 * (B + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, hEnv⟩ := density_discrepancy_envelope127 S δ hD η hη
  obtain ⟨NR, hNR⟩ := hregular
  obtain ⟨NH, hNH⟩ := hhead (ε / (2 * (C + 1))) (by positivity)
  refine ⟨max NR NH, ?_⟩
  intro X hX
  obtain ⟨hnon, hanti, hmass⟩ := hNR X (le_trans (le_max_left _ _) hX)
  have hh := hNH X (le_trans (le_max_right _ _) hX)
  have hbound := abel_discrepancy_bound127
    (centeredIndicator127 S δ) (w X) X η C
    (by intro n hn; rw [centered_prefix127]; exact hEnv n)
    (hnon X) (by intro i hi; exact hanti (Nat.le_succ i))
  have hηB : η * (B + 1) = ε / 2 := by
    dsimp [η]
    field_simp [ne_of_gt (show 0 < B + 1 by linarith)] <;> ring
  have hheadScaled := mul_lt_mul_of_pos_left hh (show 0 < C + 1 by linarith)
  have hheadId : (C + 1) * (ε / (2 * (C + 1))) = ε / 2 := by
    field_simp [ne_of_gt (show 0 < C + 1 by linarith)] <;> ring
  rw [hheadId] at hheadScaled
  have hmassScaled := mul_le_mul_of_nonneg_left hmass (le_of_lt hη)
  have hhead0 := hnon 0
  nlinarith

/-- Full density transfer for row kernels.  Only the scalar total-mass limit,
row monotonicity, positivity and a vanishing head are needed. -/
theorem density_kernel_transfer127
    (S : Set ℕ) (δ L : ℝ) (hD : HasDensity S δ)
    (w : ℕ → ℕ → ℝ)
    (hregular : ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (∀ i : ℕ, 0 ≤ w X i) ∧ Antitone (w X))
    (hhead : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X → w X 0 < ε)
    (hmass : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      |(∑ i ∈ Finset.range X, w X i) - L| < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      |(∑ i ∈ Finset.range X, (if i + 1 ∈ S then (1 : ℝ) else 0) * w X i) -
        δ * L| < ε := by
  classical
  obtain ⟨NR, hNR⟩ := hregular
  obtain ⟨NB, hNB⟩ := hmass 1 (by norm_num)
  have hregB : ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (∀ i : ℕ, 0 ≤ w X i) ∧ Antitone (w X) ∧
      (∑ i ∈ Finset.range X, w X i) ≤ |L| + 1 := by
    refine ⟨max NR NB, ?_⟩
    intro X hX
    obtain ⟨hnon, hanti⟩ := hNR X (le_trans (le_max_left _ _) hX)
    have hb := (abs_lt.mp (hNB X (le_trans (le_max_right _ _) hX))).2
    exact ⟨hnon, hanti, by linarith [le_abs_self L]⟩
  have hcenter := centered_kernel_tends_zero127 S δ hD w (|L| + 1)
    (by positivity) hregB hhead
  intro ε hε
  obtain ⟨NC, hNC⟩ := hcenter (ε / 2) (by positivity)
  obtain ⟨NM, hNM⟩ := hmass (ε / (2 * (|δ| + 1))) (by positivity)
  refine ⟨max NC NM, ?_⟩
  intro X hX
  have hc := hNC X (le_trans (le_max_left _ _) hX)
  have hm := hNM X (le_trans (le_max_right _ _) hX)
  have hid :
      (∑ i ∈ Finset.range X, (if i + 1 ∈ S then (1 : ℝ) else 0) * w X i) - δ * L =
        (∑ i ∈ Finset.range X, centeredIndicator127 S δ i * w X i) +
          δ * ((∑ i ∈ Finset.range X, w X i) - L) := by
    simp only [centeredIndicator127, sub_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    ring
  rw [hid]
  have htri :
      |(∑ i ∈ Finset.range X, centeredIndicator127 S δ i * w X i) +
          δ * ((∑ i ∈ Finset.range X, w X i) - L)| ≤
        |∑ i ∈ Finset.range X, centeredIndicator127 S δ i * w X i| +
          |δ| * |(∑ i ∈ Finset.range X, w X i) - L| := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      (norm_add_le (∑ i ∈ Finset.range X, centeredIndicator127 S δ i * w X i)
        (δ * ((∑ i ∈ Finset.range X, w X i) - L)))
  have hmScaled := mul_lt_mul_of_pos_left hm (show 0 < |δ| + 1 by positivity)
  have hmId : (|δ| + 1) * (ε / (2 * (|δ| + 1))) = ε / 2 := by
    field_simp [ne_of_gt (show 0 < |δ| + 1 by positivity)] <;> ring
  rw [hmId] at hmScaled
  nlinarith [abs_nonneg ((∑ i ∈ Finset.range X, w X i) - L)]


/-- The positive-cofactor kernel, indexed from zero and set to zero beyond
its cutoff.  It contains no arithmetic-set predicate. -/
noncomputable def cofactorRow127 (X i : ℕ) : ℝ :=
  if i < X ∧ ((i + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ alpha then
    1 / (((i + 1 : ℕ) : ℝ) * Real.log ((X : ℝ) / ((i + 1 : ℕ) : ℝ)))
  else 0

theorem cofactorRow_nonneg127 {X : ℕ} (hX : 2 ≤ X) (i : ℕ) :
    0 ≤ cofactorRow127 X i := by
  unfold cofactorRow127
  split_ifs with hi
  · have hrp : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have hrX : ((i + 1 : ℕ) : ℝ) < (X : ℝ) :=
      lt_of_le_of_lt hi.2
        (rpow_alpha_lt_self118 (by exact_mod_cast (show 1 < X by omega)))
    have hq : (1 : ℝ) < (X : ℝ) / ((i + 1 : ℕ) : ℝ) := by
      apply (lt_div_iff₀ hrp).2
      simpa using hrX
    have hl := Real.log_pos hq
    positivity
  · exact le_rfl

/-- Monotonicity of the reciprocal-log kernel on the large-quotient range. -/
theorem reciprocalLog_antitone127 {x r s : ℝ}
    (hx : 0 < x) (hr : 0 < r) (hrs : r ≤ s)
    (hqs : 1 < x / s) (hqe : Real.exp 1 ≤ x / s) :
    1 / (s * Real.log (x / s)) ≤ 1 / (r * Real.log (x / r)) := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hqorder : x / s ≤ x / r := div_le_div_of_nonneg_left hx.le hr hrs
  have hqr : 1 < x / r := lt_of_lt_of_le hqs hqorder
  have hmono := Real.log_div_self_antitoneOn hqe (le_trans hqe hqorder) hqorder
  have hscaled := mul_le_mul_of_nonneg_left hmono hx.le
  have hden : r * Real.log (x / r) ≤ s * Real.log (x / s) := by
    convert hscaled using 1 <;>
      field_simp [ne_of_gt hx, ne_of_gt hr, ne_of_gt hs] <;> ring
  exact one_div_le_one_div_of_le (mul_pos hr (Real.log_pos hqr)) hden

theorem cofactorRow_regular127 :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (∀ i : ℕ, 0 ≤ cofactorRow127 X i) ∧ Antitone (cofactorRow127 X) := by
  obtain ⟨Y, hY⟩ := exists_nat_gt (max (Real.exp 1) (3 : ℝ))
  have hYe : Real.exp 1 ≤ (Y : ℝ) :=
    le_trans (le_max_left _ _) hY.le
  have hY3 : (3 : ℝ) ≤ (Y : ℝ) :=
    le_trans (le_max_right _ _) hY.le
  obtain ⟨NS, hNS⟩ := eventually_scale_condition121 Y
  refine ⟨max NS 2, ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXNS : NS ≤ X := le_trans (le_max_left _ _) hX
  refine ⟨cofactorRow_nonneg127 hX2, ?_⟩
  intro i j hij
  by_cases hj : j < X ∧ ((j + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ alpha
  · have hijR : ((i + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show i + 1 ≤ j + 1 by omega)
    have hi : i < X ∧ ((i + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ alpha :=
      ⟨by omega, le_trans hijR hj.2⟩
    have hjI : j + 1 ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hscale := hNS X (j + 1) hXNS hjI hj.2
    have hscaleR : (Y : ℝ) * ((j + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast hscale
    have hjp : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hYq := (le_div_iff₀ hjp).2 hscaleR
    simp only [cofactorRow127, if_pos hj, if_pos hi]
    exact reciprocalLog_antitone127
      (by exact_mod_cast (show 0 < X by omega)) (by positivity) hijR
      (by linarith) (le_trans hYe hYq)
  · have hz : cofactorRow127 X j = 0 := by simp only [cofactorRow127, if_neg hj]
    rw [hz]
    exact cofactorRow_nonneg127 hX2 i

theorem cofactorRow_head_vanishes127 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      cofactorRow127 X 0 < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_log_ge127 (1 / ε + 1)
  refine ⟨N, ?_⟩
  intro X hX
  have hlog := hN X hX
  have hlogp : 0 < Real.log (X : ℝ) := by
    have : 0 < 1 / ε := one_div_pos.mpr hε
    linarith
  unfold cofactorRow127
  split_ifs
  · norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, div_one]
    apply (div_lt_iff₀ hlogp).2
    have hs := mul_le_mul_of_nonneg_left hlog hε.le
    have hid : ε * (1 / ε + 1) = 1 + ε := by
      field_simp [ne_of_gt hε] <;> ring
    rw [hid] at hs
    linarith
  · exact hε

/-- The arithmetic cofactor kernel is the weighted indicator row exactly. -/
theorem cofactorKernel_eq_row127 (X : ℕ) :
    cofactorKernel115 X =
      ∑ i ∈ Finset.range X,
        (if i + 1 ∈ A then (1 : ℝ) else 0) * cofactorRow127 X i := by
  classical
  have hreindex := sum_range_succ_eq_Icc127
    (fun r : ℕ => if r ∈ A ∧ (r : ℝ) ≤ (X : ℝ) ^ alpha then
      1 / ((r : ℝ) * Real.log ((X : ℝ) / (r : ℝ))) else 0) X
  unfold cofactorKernel115
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro i hi
  have hiX := Finset.mem_range.mp hi
  by_cases hA : i + 1 ∈ A <;>
    by_cases hp : ((i + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ alpha <;>
      simp [cofactorRow127, hiX, hA, hp]

/-- Residual scalar calculus input, not asserted here.  All dependence on A,
its density, prime counting and Abel summation has been removed from it. -/
def BareCofactorMassLimit127 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    |(∑ i ∈ Finset.range X, cofactorRow127 X i) - Real.log ((100 : ℝ) / 99)| < ε

/-- The entire density-to-kernel step follows from the scalar mass limit;
the density transfer itself is no longer an external hypothesis. -/
theorem densityCofactorKernel_from_bareMass127
    (H : BareCofactorMassLimit127) : DensityCofactorKernelLimit115 := by
  intro δ hD ε hε
  obtain ⟨N, hN⟩ := density_kernel_transfer127 A δ (Real.log ((100 : ℝ) / 99))
    hD cofactorRow127 cofactorRow_regular127 cofactorRow_head_vanishes127 H ε hε
  refine ⟨N, ?_⟩
  intro X hX
  rw [cofactorKernel_eq_row127]
  exact hN X hX


/-! ### C. Dense theta: exact interval identity and quantitative endpoint control -/

noncomputable def primeLog127 (p : ℕ) : ℝ :=
  if p.Prime then Real.log (p : ℝ) else 0

noncomputable def thetaPrefix127 (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 n, primeLog127 p

/-- Exact prefix decomposition; no assertion about prime distribution. -/
theorem thetaPrefix_split127 {d c : ℕ} (hdc : d ≤ c) :
    thetaPrefix127 c = thetaPrefix127 d +
      ∑ p ∈ (Finset.Icc 1 c).filter (fun p => p.Prime ∧ d < p),
        Real.log (p : ℝ) := by
  classical
  have hlow : (Finset.Icc 1 c).filter (fun p => p ≤ d) = Finset.Icc 1 d := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hlowSum : (∑ p ∈ Finset.Icc 1 c, if p ≤ d then primeLog127 p else 0) =
      thetaPrefix127 d := by
    rw [← Finset.sum_filter, hlow]
    rfl
  rw [← hlowSum, Finset.sum_filter, ← Finset.sum_add_distrib]
  unfold thetaPrefix127
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpd : p ≤ d
  · simp [primeLog127, hpd, not_lt_of_ge hpd]
  · simp [primeLog127, hpd, lt_of_not_ge hpd]

/-- The exact top-prime mass is a difference of two Chebyshev prefixes. -/
theorem denseTopMass_eq_thetaDifference127 {b c : ℕ} (hbc : b ≤ c) :
    (∑ p ∈ denseTopPrimes115 b c, Real.log (p : ℝ)) =
      thetaPrefix127 c - thetaPrefix127 (max b (c / 2)) := by
  have hcut : max b (c / 2) ≤ c := max_le hbc (Nat.div_le_self c 2)
  have hsplit := thetaPrefix_split127 hcut
  change thetaPrefix127 c = thetaPrefix127 (max b (c / 2)) +
    (∑ p ∈ denseTopPrimes115 b c, Real.log (p : ℝ)) at hsplit
  linarith

/-- The top interval has at least half the length of the original interval. -/
theorem denseTop_width127 {b c : ℕ} (hbc : b ≤ c) :
    ((c - b : ℕ) : ℝ) ≤
      2 * ((c : ℝ) - (max b (c / 2) : ℕ)) := by
  have hn : c - b + 2 * max b (c / 2) ≤ 2 * c := by omega
  have hr : ((c - b : ℕ) : ℝ) + 2 * ((max b (c / 2) : ℕ) : ℝ) ≤ 2 * (c : ℝ) := by
    exact_mod_cast hn
  linarith

/-- A quantitative, finite endpoint lemma for the dense branch. -/
theorem denseTopMass_from_endpoint_errors127 {b c : ℕ} (hbc : b ≤ c)
    (hc : |thetaPrefix127 c - (c : ℝ)| ≤ ((c - b : ℕ) : ℝ) / 8)
    (hd : |thetaPrefix127 (max b (c / 2)) - ((max b (c / 2) : ℕ) : ℝ)| ≤
      ((c - b : ℕ) : ℝ) / 8) :
    ((c - b : ℕ) : ℝ) / 4 ≤
      ∑ p ∈ denseTopPrimes115 b c, Real.log (p : ℝ) := by
  rw [denseTopMass_eq_thetaDifference127 hbc]
  have hc' := (abs_le.mp hc).1
  have hd' := (abs_le.mp hd).2
  linarith [denseTop_width127 hbc]

/-- One-variable quantitative theta input.  This is stronger than qualitative
PNT.  It is NOT proved or postulated as an axiom in this file. -/
def ThetaLogSqRemainder127 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |thetaPrefix127 n - (n : ℝ)| * (Real.log (n : ℝ)) ^ 2 ≤ ε * (n : ℝ)

/-- The uniform endpoint-error calculation, with every constant explicit. -/
theorem theta_error_budget127 {E l L h z γ : ℝ}
    (hE : 0 ≤ E) (hγ : 0 < γ) (hL : 0 < L)
    (hl : γ * L / 2 ≤ l)
    (hz : z ≤ 101 * h * L ^ 2)
    (herror : E * l ^ 2 ≤ (γ ^ 2 / 3232) * z) :
    E ≤ h / 8 := by
  have hprodpos : 0 < γ * L := mul_pos hγ hL
  have hl0 : 0 ≤ l := by linarith
  have hsquare : (γ * L / 2) ^ 2 ≤ l ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hsquare hE
  have h2 := mul_le_mul_of_nonneg_left hz (show 0 ≤ γ ^ 2 / 3232 by positivity)
  have hcombined : E * (γ ^ 2 * L ^ 2) ≤ (h / 8) * (γ ^ 2 * L ^ 2) := by
    nlinarith only [h1, herror, h2]
  have hdenpos : 0 < γ ^ 2 * L ^ 2 := by positivity
  exact le_of_mul_le_mul_right hcombined hdenpos

/-- Quantitative one-variable theta accuracy supplies the full dense input.
The cutoff `max b (c/2)` and the logarithmic dense/sparse boundary are handled
inside this proof, rather than assumed as another short-interval theorem. -/
theorem denseTopThetaMass_from_thetaRemainder127
    (H : ThetaLogSqRemainder127) : DenseTopThetaMass119 := by
  intro γ hγ0 hγ1
  obtain ⟨NT, hNT⟩ := H (γ ^ 2 / 3232) (by positivity)
  obtain ⟨NP, hNP⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := γ) (C := (4 : ℝ) * ((NT : ℝ) + 4)) hγ0
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 (max 1 (2 * Real.log 4 / γ))
  refine ⟨max 2 (max NP NL), ?_⟩
  intro X b c hX hbc hcX hgap hb
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXP : NP ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXL : NL ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  let h : ℝ := ((c - b : ℕ) : ℝ)
  let L : ℝ := Real.log (X : ℝ)
  let d : ℕ := max b (c / 2)
  have hdc : d ≤ c := max_le (Nat.le_of_lt hbc) (Nat.div_le_self c 2)
  have hgapc : h ≤ (c : ℝ) := by
    dsimp [h]
    exact_mod_cast (Nat.sub_le c b)
  have hlarge : 4 * ((NT : ℝ) + 4) < (c : ℝ) :=
    lt_of_lt_of_le (hNP X hXP) (le_trans hgap hgapc)
  have hlargeNat : 4 * (NT + 4) < c := by exact_mod_cast hlarge
  have hdNT : NT ≤ d := by dsimp [d]; omega
  have hcNT : NT ≤ c := by omega
  have hdp : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show 0 < d by dsimp [d]; omega)
  have hcp : (0 : ℝ) < (c : ℝ) := by linarith
  have hc4d : (c : ℝ) ≤ 4 * (d : ℝ) := by
    exact_mod_cast (show c ≤ 4 * d by dsimp [d]; omega)
  have hLraw := hNL X hXL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hLraw
  have hLpos : 0 < L := by linarith
  have hLγ : 2 * Real.log 4 / γ ≤ L := le_trans (le_max_right _ _) hLraw
  have hlog4 : 2 * Real.log 4 ≤ L * γ := (div_le_iff₀ hγ0).1 hLγ
  have hpowc : (X : ℝ) ^ γ ≤ (c : ℝ) := le_trans hgap hgapc
  have hlogc : γ * L ≤ Real.log (c : ℝ) := by
    have hm := Real.log_le_log (Real.rpow_pos_of_pos hXp γ) hpowc
    rw [Real.log_rpow hXp] at hm
    simpa [L, mul_comm] using hm
  have hlogd : γ * L / 2 ≤ Real.log (d : ℝ) := by
    have hm := Real.log_le_log hcp hc4d
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hdp)] at hm
    nlinarith only [hm, hlogc, hlog4]
  have hlogcHalf : γ * L / 2 ≤ Real.log (c : ℝ) := by
    have hp : 0 ≤ γ * L := mul_nonneg hγ0.le hLpos.le
    linarith
  have hsplit : (c : ℝ) = (b : ℝ) + h := by
    dsimp [h]
    rw [Nat.cast_sub (Nat.le_of_lt hbc)]
    ring
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hhL := mul_le_mul_of_nonneg_left hLsq hh0
  have hcBound : (c : ℝ) ≤ 101 * h * L ^ 2 := by
    change (b : ℝ) ≤ 100 * h * L ^ 2 at hb
    nlinarith only [hb, hsplit, hhL]
  have hdBound : (d : ℝ) ≤ 101 * h * L ^ 2 :=
    le_trans (by exact_mod_cast hdc) hcBound
  have hEc : |thetaPrefix127 c - (c : ℝ)| ≤ h / 8 :=
    theta_error_budget127 (abs_nonneg _) hγ0 hLpos hlogcHalf hcBound (hNT c hcNT)
  have hEd : |thetaPrefix127 d - (d : ℝ)| ≤ h / 8 :=
    theta_error_budget127 (abs_nonneg _) hγ0 hLpos hlogd hdBound (hNT d hdNT)
  exact denseTopMass_from_endpoint_errors127 hbc.le hEc hEd


/-! ### D. Sparse transfer: canonical prime counts and explicit square-loss budgets -/

/-- Exactly the valuation-one primes that a sparse packet may retain. -/
def sparseGoodPrimes127 (a b c P : ℕ) : Finset ℕ :=
  (Finset.Icc P (2 * P)).filter (fun p =>
    p.Prime ∧ a < p ∧ p ∣ falling (c - b) c ∧ ¬ p ^ 2 ∣ falling (c - b) c)

/-- A canonical counting estimate constructs a complete unit-weight packet. -/
noncomputable def sparsePacket_of_count127 {a b c P : ℕ}
    (hcount : ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
      ((sparseGoodPrimes127 a b c P).card : ℝ)) :
    SparseWeightPacket a b c P := by
  classical
  refine {
    weight := fun p => if p ∈ sparseGoodPrimes127 a b c P then 1 else 0
    support := ?_
    unit_weight := ?_
    valuation_one := ?_
    weighted_count_lower := ?_
  }
  · intro p hp
    have hm : p ∈ sparseGoodPrimes127 a b c P := by
      by_contra hnot
      simp [hnot] at hp
    obtain ⟨hI, hdata⟩ := Finset.mem_filter.mp hm
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hI
    exact ⟨hdata.1, hlo, hhi⟩
  · intro p
    split_ifs <;> norm_num
  · intro p hp
    have hm : p ∈ sparseGoodPrimes127 a b c P := by
      by_contra hnot
      simp [hnot] at hp
    exact (Finset.mem_filter.mp hm).2.2
  · have hset : (Finset.Icc P (2 * P)).filter
        (fun p => p ∈ sparseGoodPrimes127 a b c P) = sparseGoodPrimes127 a b c P := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · exact fun hp => hp.2
      · intro hp
        exact ⟨(Finset.mem_filter.mp hp).1, hp⟩
    rw [← Finset.sum_filter, hset]
    simpa using hcount

/-- Conversely, fractional weights cannot beat the canonical good-prime count. -/
theorem sparsePacket_implies_count127 {a b c P : ℕ}
    (W : SparseWeightPacket a b c P) :
    ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
      ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  have hsubset : W.selected ⊆ sparseGoodPrimes127 a b c P := by
    intro p hp
    have hI := (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨hI, selected_prime_data W hp⟩
  have hc : (W.selected.card : ℝ) ≤ ((sparseGoodPrimes127 a b c P).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  exact le_trans W.weighted_count_lower
    (le_trans (weighted_sum_le_selected_card W) hc)

/-- A precise equivalence, not a claim that the required prime count is proved. -/
theorem sparsePacket_iff_count127 (a b c P : ℕ) :
    Nonempty (SparseWeightPacket a b c P) ↔
      ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
        ((sparseGoodPrimes127 a b c P).card : ℝ) := by
  constructor
  · rintro ⟨W⟩
    exact sparsePacket_implies_count127 W
  · intro hcount
    exact ⟨sparsePacket_of_count127 hcount⟩

/-- Analytic sparse boundary with no existential weight function.  It is
logically equivalent to the old packet boundary, not an extra theorem. -/
def SparseGoodPrimeCount127 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ X₀ : ℕ,
    ∀ X a b c : ℕ,
      X₀ ≤ X → a < b → b < c → c ≤ X →
      (X : ℝ) ^ γ ≤ ((c - b : ℕ) : ℝ) →
      (a : ℝ) ≤ 10 * ((c - b : ℕ) : ℝ) * Real.log (X : ℝ) →
      100 * ((c - b : ℕ) : ℝ) * (Real.log (X : ℝ)) ^ 2 < (b : ℝ) →
      ∃ P : ℕ, 2 ≤ P ∧
        ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ)) ≤
          ((sparseGoodPrimes127 a b c P).card : ℝ)

theorem sparseWeightedTransfer_from_count127
    (H : SparseGoodPrimeCount127) : Remaining_SparseWeightedTransfer47 := by
  intro γ hγ0 hγ1
  obtain ⟨N, hN⟩ := H γ hγ0 hγ1
  refine ⟨N, ?_⟩
  intro X a b c hX hab hbc hcX hgap ha hb
  obtain ⟨P, hP, hcount⟩ := hN X a b c hX hab hbc hcX hgap ha hb
  exact ⟨P, sparsePacket_of_count127 hcount, hP⟩

theorem sparseGoodPrimeCount_from_weighted127
    (H : Remaining_SparseWeightedTransfer47) : SparseGoodPrimeCount127 := by
  intro γ hγ0 hγ1
  obtain ⟨N, hN⟩ := H γ hγ0 hγ1
  refine ⟨N, ?_⟩
  intro X a b c hX hab hbc hcX hgap ha hb
  obtain ⟨P, W, hP⟩ := hN X a b c hX hab hbc hcX hgap ha hb
  exact ⟨P, hP, sparsePacket_implies_count127 W⟩

/-- Exact decomposition into retained mass and square-divisor loss. -/
theorem sparse_keep_loss_identity127 (w : ℕ → ℝ) (a b c P : ℕ) :
    (∑ p ∈ Finset.Icc P (2 * P),
      if p ^ 2 ∣ falling (c - b) c then 0 else w p) +
    (∑ p ∈ Finset.Icc P (2 * P),
      if p ^ 2 ∣ falling (c - b) c then w p else 0) =
    ∑ p ∈ Finset.Icc P (2 * P), w p := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- A concrete way to produce the sparse packet: start with weighted prime
DIVISORS, prove a gross mass bound and a square-divisor loss bound, and delete
the square-divisor part.  Neither analytic mass bound is assumed proved. -/
noncomputable def sparsePacket_of_mass_loss127 {a b c P : ℕ}
    (w : ℕ → ℝ)
    (hw : ∀ p : ℕ, 0 ≤ w p ∧ w p ≤ 1)
    (hsupport : ∀ p : ℕ, 0 < w p →
      p.Prime ∧ P ≤ p ∧ p ≤ 2 * P ∧ a < p ∧ p ∣ falling (c - b) c)
    (hgross : 2 * (((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ))) ≤
      ∑ p ∈ Finset.Icc P (2 * P), w p)
    (hloss : (∑ p ∈ Finset.Icc P (2 * P),
      if p ^ 2 ∣ falling (c - b) c then w p else 0) ≤
      ((c - b : ℕ) : ℝ) / (640 * Real.log (2 * P : ℝ))) :
    SparseWeightPacket a b c P := by
  classical
  refine {
    weight := fun p => if p ^ 2 ∣ falling (c - b) c then 0 else w p
    support := ?_
    unit_weight := ?_
    valuation_one := ?_
    weighted_count_lower := ?_
  }
  · intro p hp
    by_cases hsq : p ^ 2 ∣ falling (c - b) c
    · simp [hsq] at hp
    · have hwpos : 0 < w p := by simpa [hsq] using hp
      have hd := hsupport p hwpos
      exact ⟨hd.1, hd.2.1, hd.2.2.1⟩
  · intro p
    split_ifs
    · norm_num
    · exact hw p
  · intro p hp
    by_cases hsq : p ^ 2 ∣ falling (c - b) c
    · simp [hsq] at hp
    · have hwpos : 0 < w p := by simpa [hsq] using hp
      have hd := hsupport p hwpos
      exact ⟨hd.2.2.2.1, hd.2.2.2.2, hsq⟩
  · have hid := sparse_keep_loss_identity127 w a b c P
    linarith

/-! ### E. Harman: canonical exceptional set and a sufficient second-moment estimate -/

def shortIntervalPrimes127 (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 m).filter (fun p =>
    p.Prime ∧ ((m - p : ℕ) : ℝ) ≤ (m : ℝ) ^ theta)

def badShortIntervals127 : Set ℕ := {m | shortIntervalPrimes127 m = ∅}

theorem shortInterval_nonempty_iff127 (m : ℕ) :
    (shortIntervalPrimes127 m).Nonempty ↔
      ∃ p : ℕ, p.Prime ∧ p ≤ m ∧ ((m - p : ℕ) : ℝ) ≤ (m : ℝ) ^ theta := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨hI, hd⟩ := Finset.mem_filter.mp hp
    exact ⟨p, hd.1, (Finset.mem_Icc.mp hI).2, hd.2⟩
  · rintro ⟨p, hp, hpm, hgap⟩
    exact ⟨p, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpm⟩, hp, hgap⟩⟩

/-- The density-zero statement about the canonical bad intervals is enough;
there is no need to guess an exceptional set separately. -/
theorem harman_from_bad_density127
    (H : DensityZero badShortIntervals127) : Remaining_Harman47 := by
  refine ⟨badShortIntervals127, H, 0, ?_⟩
  intro m hm hgood
  have hne : shortIntervalPrimes127 m ≠ ∅ := hgood
  exact (shortInterval_nonempty_iff127 m).1 (Finset.nonempty_iff_ne_empty.mpr hne)

/-- The canonical bad-set formulation is also necessary. -/
theorem bad_density_from_harman127
    (H : Remaining_Harman47) : DensityZero badShortIntervals127 := by
  obtain ⟨E, hE, N, hN⟩ := H
  apply densityZero_mono (T := E ∪ Initial N) ?_
    (densityZero_union hE (densityZero_initial N))
  intro m hm
  by_cases hmN : N ≤ m
  · left
    by_contra hmE
    have hprime := (shortInterval_nonempty_iff127 m).2 (hN m hmN hmE)
    have hempty : shortIntervalPrimes127 m = ∅ := hm
    simpa [hempty] using hprime
  · right
    exact Nat.lt_of_not_ge hmN

theorem harman_iff_bad_density127 :
    Remaining_Harman47 ↔ DensityZero badShortIntervals127 :=
  ⟨bad_density_from_harman127, harman_from_bad_density127⟩

/-- A normalized squared prime-count discrepancy.  On an empty interval it
is exactly one, including at the finitely many degenerate small endpoints. -/
noncomputable def shortIntervalSquareError127 (m : ℕ) : ℝ :=
  (((shortIntervalPrimes127 m).card : ℝ) /
    ((m : ℝ) ^ theta / Real.log (m : ℝ)) - 1) ^ 2

/-- A sufficient analytic mean-square hypothesis.  It is deliberately left
unproved; it is not asserted to follow from qualitative PNT. -/
def HarmanNormalizedSecondMoment127 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    (∑ m ∈ Finset.Icc 1 X, shortIntervalSquareError127 m) < ε * (X : ℝ)

theorem bad_count_le_secondMoment127 (X : ℕ) :
    (prefixCount badShortIntervals127 X : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 X, shortIntervalSquareError127 m := by
  rw [prefixCount_eq_indicator_sum127]
  apply Finset.sum_le_sum
  intro m hm
  by_cases hbad : m ∈ badShortIntervals127
  · have he : shortIntervalPrimes127 m = ∅ := hbad
    simp [hbad, shortIntervalSquareError127, he]
  · simp only [if_neg hbad]
    exact sq_nonneg _

theorem harman_from_secondMoment127
    (H : HarmanNormalizedSecondMoment127) : Remaining_Harman47 := by
  apply harman_from_bad_density127
  intro ε hε
  obtain ⟨N, hN⟩ := H ε hε
  refine ⟨max N 1, ?_⟩
  intro X hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hcount := lt_of_le_of_lt (bad_count_le_secondMoment127 X) (hN X hXN)
  rw [sub_zero, abs_of_nonneg (proportion_nonneg _ _)]
  exact (div_lt_iff₀ hXp).2 hcount


/-! ### F. Proposition 5.1: shared prime supply and elementary Weil range -/

/-- The dense hypothesis already contains the dyadic theta gap.  This removes
a genuinely redundant prime-supply assumption from the joint endgame. -/
theorem dyadicThetaGap_from_dense127
    (H : DenseTopThetaMass119) : RemainingAnalytic93.ChebyshevDyadicThetaGap93 := by
  obtain ⟨ND, hND⟩ := H ((1 : ℝ) / 2) (by norm_num) (by norm_num)
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 1
  refine ⟨(1 : ℝ) / 4, by norm_num, max ND (max NL 2), ?_⟩
  intro n hn
  have hnD : ND ≤ n := le_trans (le_max_left _ _) hn
  have hnL : NL ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn2 : 2 ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hsqn : 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hn2R)]
  have hsqrt_sq :
      (Real.sqrt (2 * (n : ℝ))) ^ 2 = 2 * (n : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * (n : ℝ)) :=
    Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt (2 * (n : ℝ)) ≤ (n : ℝ) := by
    nlinarith
  have hgap :
      (((2 * n : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) ≤
        (((2 * n - n : ℕ) : ℝ)) := by
    have hsub : 2 * n - n = n := by omega
    rw [hsub, ← Real.sqrt_eq_rpow]
    push_cast
    simpa using hsqrtle
  have hlog : 1 ≤ Real.log (((2 * n : ℕ) : ℝ)) :=
    hNL (2 * n) (by omega)
  have hlogsq : 1 ≤ (Real.log (((2 * n : ℕ) : ℝ))) ^ 2 := by
    nlinarith
  have hb : (n : ℝ) ≤
      100 * (((2 * n - n : ℕ) : ℝ)) *
        (Real.log (((2 * n : ℕ) : ℝ))) ^ 2 := by
    have hsub : 2 * n - n = n := by omega
    rw [hsub]
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_nonneg hnnonneg (sub_nonneg.mpr hlogsq)]
  have hmass :=
    hND (2 * n) n (2 * n) (by omega) (by omega) le_rfl hgap hb
  have hhalf : (2 * n) / 2 = n := by omega
  have hsets :
      denseTopPrimes115 n (2 * n) =
        RemainingAnalytic59.dyadicPrimes59 n := by
    ext p
    simp only [denseTopPrimes115, RemainingAnalytic59.dyadicPrimes59,
      Finset.mem_filter, Finset.mem_Icc, hhalf, max_self]
    constructor
    · rintro ⟨⟨hp1, hp2n⟩, hprime, hnp⟩
      exact ⟨⟨by omega, hp2n⟩, hprime⟩
    · rintro ⟨⟨hnp1, hp2n⟩, hprime⟩
      have hp1 : 1 ≤ p := by omega
      have hnp : n < p := by omega
      exact ⟨⟨hp1, hp2n⟩, hprime, hnp⟩
  rw [hsets] at hmass
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hmass
  change (1 : ℝ) / 4 * (n : ℝ) ≤
    ∑ p ∈ RemainingAnalytic59.dyadicPrimes59 n, Real.log (p : ℝ)
  nlinarith only [hmass]


/-- Absolute values of the actual quadratic-character wrapper are at most one. -/
theorem quadraticChar_abs_le_one127 {lam : ℕ} (hp : lam.Prime) (x : ZMod lam) :
    |((RemainingAnalytic62.quadraticCharValue62 lam x : ℤ) : ℝ)| ≤ 1 := by
  letI : Fact lam.Prime := ⟨hp⟩
  rw [RemainingAnalytic62.quadraticCharValue_of_prime62 hp x, quadraticChar_apply]
  unfold quadraticCharFun
  by_cases hx : x = 0 <;> by_cases hs : IsSquare x <;> simp [hx, hs]

/-- Trivial finite-field bound, valid without any Weil input. -/
theorem linearProductQuadraticSum_trivial127
    (lam : ℕ) (hp : lam.Prime) (c : ZMod lam) (r j t h ell : ℕ) :
    |((RemainingAnalytic96.linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| ≤
      (lam : ℝ) := by
  letI : Fact lam.Prime := ⟨hp⟩
  unfold RemainingAnalytic96.linearProductQuadraticSum96
  push_cast
  calc
    _ ≤ ∑ z : ZMod lam,
        |((RemainingAnalytic62.quadraticCharValue62 lam
          (c * RemainingAnalytic61.anchorIProduct61 r ell lam z *
            RemainingAnalytic61.anchorVProduct61 j t h lam z) : ℤ) : ℝ)| :=
      abs_finset_sum_le_sum_abs117 _ _
    _ ≤ ∑ _z : ZMod lam, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact quadraticChar_abs_le_one127 hp _
    _ = (lam : ℝ) := by simp

/-- Weil's deliberately loose project bound is elementary in this range. -/
theorem linearProductWeil_small_modulus127
    (lam : ℕ) (hp : lam.Prime) (c : ZMod lam) (r j t h ell : ℕ)
    (hsize : (lam : ℝ) ≤ 4 * (max h ell : ℝ) ^ 2) :
    |((RemainingAnalytic96.linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| ≤
      2 * (max h ell : ℝ) * Real.sqrt (lam : ℝ) := by
  have hH : (0 : ℝ) ≤ (max h ell : ℝ) := by positivity
  have hs0 := Real.sqrt_nonneg (lam : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ (lam : ℝ) by positivity)
  have hsle : Real.sqrt (lam : ℝ) ≤ 2 * (max h ell : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsle hs0
  have htarget : (lam : ℝ) ≤ 2 * (max h ell : ℝ) * Real.sqrt (lam : ℝ) := by
    nlinarith only [hmul, hs2]
  exact le_trans (linearProductQuadraticSum_trivial127 lam hp c r j t h ell) htarget

/-- The genuinely nontrivial part of the existing Weil interface.  This is an
explicit remaining hypothesis, not a formalized proof of Weil's theorem. -/
def LargeModulusLinearProductWeil127 : Prop :=
  ∀ r j t h ell lam : ℕ,
    0 < j → j < r → 0 < h → 0 < ell → t < h →
    (h ≠ 1 ∨ ell ≠ 1) → ∀ hp : lam.Prime,
    2 * r * max h ell < lam →
    4 * (max h ell : ℝ) ^ 2 < (lam : ℝ) →
    ∀ c : ZMod lam, c ≠ 0 →
      |((RemainingAnalytic96.linearProductQuadraticSum96 lam hp c r j t h ell : ℤ) : ℝ)| ≤
        2 * (max h ell : ℝ) * Real.sqrt (lam : ℝ)

theorem classicalLinearProductWeil_from_large127
    (H : LargeModulusLinearProductWeil127) :
    RemainingAnalytic96.ClassicalLinearProductQuadraticWeil96 := by
  intro r j t h ell lam hj hjr hh hell ht hnp hp hsep c hc
  by_cases hsize : (lam : ℝ) ≤ 4 * (max h ell : ℝ) ^ 2
  · exact linearProductWeil_small_modulus127 lam hp c r j t h ell hsize
  · exact H r j t h ell lam hj hjr hh hell ht hnp hp hsep (lt_of_not_ge hsize) c hc

/-- Construct the old three-part analytic package without an independent
dyadic-theta field.  The large sieve and large-modulus Weil input remain. -/
noncomputable def prop51Classical_from_dense127
    (HD : DenseTopThetaMass119)
    (HLS : RemainingAnalytic92.ClassicalPrimeAdditiveLargeSieve92)
    (HW : LargeModulusLinearProductWeil127) : ClassicalAnalyticCore101 where
  largeSieve := HLS
  dyadicTheta := dyadicThetaGap_from_dense127 HD
  linearProductWeil := classicalLinearProductWeil_from_large127 HW

/-- Direct access to the complete existing Proposition-5.1 analytic core. -/
theorem prop51AnalyticCore_from_theta127
    (Htheta : ThetaLogSqRemainder127)
    (HLS : RemainingAnalytic92.ClassicalPrimeAdditiveLargeSieve92)
    (HW : LargeModulusLinearProductWeil127) : RemainingAnalytic58.AnalyticCore58 :=
  RemainingAnalytic101.analyticCore58_from_classical101
    (prop51Classical_from_dense127
      (denseTopThetaMass_from_thetaRemainder127 Htheta) HLS HW)

/-! ### G. Integrated endgame and explicit assumption audit

NOT supplied here:
* the remaining cofactor arithmetic/counting and five-code inputs;
* the two A-density inputs;
* one-variable relative PNT and the factorial-growth PNT package;
* the scalar bare-kernel mass limit;
* the one-variable log-squared theta remainder estimate;
* the canonical sparse good-prime count and the canonical Harman bad-set density;
* the additive large sieve and the large-modulus character-sum bound.

DISCHARGED in the new proof scripts:
* both floor/log normalization inputs;
* the density/Abel transfer, conditional only on scalar kernel mass;
* all dense-interval geometry from the one-variable theta input;
* sparse packet construction/selection and the mass-minus-loss calculation;
* the conversion from a normalized second moment to Harman's bad-set estimate;
* the duplicate dyadic-prime-supply field and the elementary Weil range;
* the auxiliary-threshold and four-code fields, using earlier proved lemmas.

The term below is a function FROM these remaining hypotheses; it is not an
inhabitant of the input record, and it is not an unconditional Erdős theorem.
-/

structure EverythingLeftClassical127 where
  cofactor_inheritance : Remaining_CofactorInheritance47
  cofactor_integer_count : Remaining_CofactorIntegerCount47
  five_code_cardinality : Remaining_FiveCodeCardinality47
  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47
  prime_count_relative_pnt : PrimeCountRelativePNT123
  bare_kernel_mass : BareCofactorMassLimit127
  theta_logsq_remainder : ThetaLogSqRemainder127
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  pnt : Remaining_PNTPackage47
  large_sieve : RemainingAnalytic92.ClassicalPrimeAdditiveLargeSieve92
  large_modulus_weil : LargeModulusLinearProductWeil127

noncomputable def EverythingLeftClassical127.to126
    (H : EverythingLeftClassical127) : EverythingLeftClassical126 where
  cofactor_inheritance := H.cofactor_inheritance
  cofactor_integer_count := H.cofactor_integer_count
  legal_auxiliary_thresholds := RemainingAnalytic56.legalAuxiliaryThresholds_proved56
  four_code_cardinality := RemainingAnalytic52.legalFourCodeCardinality_proved52
  five_code_cardinality := H.five_code_cardinality
  A_density_limit := H.A_density_limit
  A_uniform_tail := H.A_uniform_tail
  prime_count_relative_pnt := H.prime_count_relative_pnt
  floor_kernel_comparison := floorKernelComparison_proved127
  main_term_floor_log := mainTermFloorLogTransfer_proved127
  cofactor_density_kernel := densityCofactorKernel_from_bareMass127 H.bare_kernel_mass
  pnt := H.pnt
  harman := harman_from_bad_density127 H.harman_bad_density
  dense_theta_mass := denseTopThetaMass_from_thetaRemainder127 H.theta_logsq_remainder
  sparse_weighted_transfer := sparseWeightedTransfer_from_count127 H.sparse_good_prime_count
  prop51_classical := prop51Classical_from_dense127
    (denseTopThetaMass_from_thetaRemainder127 H.theta_logsq_remainder)
    H.large_sieve H.large_modulus_weil

theorem candidate_main_from_classical_endgame127
    (H : EverythingLeftClassical127) : MainStatement :=
  candidate_main_from_classical_endgame126 H.to126

theorem positive_lower_density_from_classical_endgame127
    (H : EverythingLeftClassical127) : PositiveLowerDensity D6 :=
  positive_lower_density_from_classical_endgame126 H.to126

theorem everything_left_outputs_from_classical127
    (H : EverythingLeftClassical127) : EverythingLeftOutputs47 :=
  RemainingAnalytic123.everything_left_outputs_from_classical123 H.to126.to125.to123

/- Individual checkpoints matter: a clean conditional final theorem alone
would not establish that unrelated helper declarations compiled. -/
-- Historical audit output: #print axioms floor_main_term_bounds127
-- Historical audit output: #print axioms floorKernelComparison_proved127
-- Historical audit output: #print axioms mainTermFloorLogTransfer_proved127
-- Historical audit output: #print axioms floorLogNormalization_proved127
-- Historical audit output: #print axioms scaleUniformPrimeCount_from_relative127
-- Historical audit output: #print axioms finite_abel127
-- Historical audit output: #print axioms abel_affine_envelope127
-- Historical audit output: #print axioms abel_discrepancy_bound127
-- Historical audit output: #print axioms density_discrepancy_envelope127
-- Historical audit output: #print axioms centered_kernel_tends_zero127
-- Historical audit output: #print axioms density_kernel_transfer127
-- Historical audit output: #print axioms cofactorRow_regular127
-- Historical audit output: #print axioms cofactorRow_head_vanishes127
-- Historical audit output: #print axioms cofactorKernel_eq_row127
-- Historical audit output: #print axioms densityCofactorKernel_from_bareMass127
-- Historical audit output: #print axioms thetaPrefix_split127
-- Historical audit output: #print axioms denseTopMass_eq_thetaDifference127
-- Historical audit output: #print axioms denseTopMass_from_endpoint_errors127
-- Historical audit output: #print axioms theta_error_budget127
-- Historical audit output: #print axioms denseTopThetaMass_from_thetaRemainder127
-- Historical audit output: #print axioms sparsePacket_of_count127
-- Historical audit output: #print axioms sparsePacket_implies_count127
-- Historical audit output: #print axioms sparsePacket_iff_count127
-- Historical audit output: #print axioms sparseWeightedTransfer_from_count127
-- Historical audit output: #print axioms sparsePacket_of_mass_loss127
-- Historical audit output: #print axioms harman_iff_bad_density127
-- Historical audit output: #print axioms bad_count_le_secondMoment127
-- Historical audit output: #print axioms harman_from_secondMoment127
-- Historical audit output: #print axioms dyadicThetaGap_from_dense127
-- Historical audit output: #print axioms quadraticChar_abs_le_one127
-- Historical audit output: #print axioms linearProductQuadraticSum_trivial127
-- Historical audit output: #print axioms linearProductWeil_small_modulus127
-- Historical audit output: #print axioms classicalLinearProductWeil_from_large127
-- Historical audit output: #print axioms prop51AnalyticCore_from_theta127
-- Historical audit output: #print axioms EverythingLeftClassical127.to126
-- Historical audit output: #print axioms centered_prefix127
-- Historical audit output: #print axioms centered_kernel_tends_zero127
-- Historical audit output: #print axioms density_kernel_transfer127
-- Historical audit output: #print axioms densityCofactorKernel_from_bareMass127
-- Historical audit output: #print axioms theta_error_budget127
-- Historical audit output: #print axioms denseTopThetaMass_from_thetaRemainder127
-- Historical audit output: #print axioms dyadicThetaGap_from_dense127
-- Historical audit output: #print axioms prop51AnalyticCore_from_theta127
-- Historical audit output: #print axioms candidate_main_from_classical_endgame127
-- Historical audit output: #print axioms positive_lower_density_from_classical_endgame127
-- Historical audit output: #print axioms everything_left_outputs_from_classical127

-- Show the conditional types as well as their axiom dependencies.
-- Historical audit output: #check candidate_main_from_classical_endgame127
-- Historical audit output: #check positive_lower_density_from_classical_endgame127

end RemainingAnalytic127



/-! ## 130. Corrected endgame, derived PNT consequences, and arithmetic audit

This section deliberately bypasses the historical exact-prefix cofactor
identity and the obsolete five-code interface.  A fixed finite correction
belongs in the cofactor count, as Repair 57 already explained.

New proofs below derive prime-count decay from relative PNT and factorial
squareclass growth from the quantitative theta input.  No new axiom, sorry, or admit is introduced.  Remaining hypotheses are
explicitly retained, and the new proof scripts require compilation.
The new scripts have not been compiled in the authoring environment.
-/
namespace RemainingAnalytic130

open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic37 RemainingAnalytic47
open RemainingAnalytic117 RemainingAnalytic118 RemainingAnalytic119
open RemainingAnalytic120 RemainingAnalytic121 RemainingAnalytic122
open RemainingAnalytic123 RemainingAnalytic124 RemainingAnalytic125
open RemainingAnalytic126 RemainingAnalytic127

/-! ### A. Derive both older PNT-package fields from inputs already required -/

/-- Relative PNT implies prime-count decay; it need not be assumed twice. -/
theorem primeCountDecay_from_relative130
    (HP : PrimeCountRelativePNT123) : PrimeCountDecay := by
  intro ε hε
  obtain ⟨NP, hNP2, hNP⟩ :=
    oneVariablePrimeCountPNT_from_relative123 HP 1 (by norm_num)
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 (4 / ε)
  refine ⟨max NP NL, ?_⟩
  intro X hX
  have hXP : NP ≤ X := le_trans (le_max_left _ _) hX
  have hXL : NL ≤ X := le_trans (le_max_right _ _) hX
  have hX2 : 2 ≤ X := le_trans hNP2 hXP
  have hXp : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hlower := hNL X hXL
  have hfour : (0 : ℝ) < 4 / ε := by positivity
  have hlp : 0 < Real.log (X : ℝ) := lt_of_lt_of_le hfour hlower
  have hlocal := hNP X hXP
  have hupp := (abs_le.mp hlocal).2
  have hratio : (prefixCount {p : ℕ | p.Prime} X : ℝ) / (X : ℝ)
      ≤ 2 / Real.log (X : ℝ) := by
    simp only [one_mul] at hupp
    calc
      (prefixCount {p : ℕ | p.Prime} X : ℝ) / (X : ℝ)
          ≤ 1 / Real.log (X : ℝ) + 1 / Real.log (X : ℝ) := by
            linarith only [hupp]
      _ = 2 / Real.log (X : ℝ) := by ring
  have hlogscale : 4 ≤ ε * Real.log (X : ℝ) := by
    have hh := (div_le_iff₀ hε).mp hlower
    nlinarith only [hh]
  have hsmall : 2 / Real.log (X : ℝ) < ε := by
    apply (div_lt_iff₀ hlp).mpr
    linarith only [hlogscale]
  exact (div_lt_iff₀ hXp).mp (lt_of_le_of_lt hratio hsmall)

/-- Top-half primes are actual odd-valuation prime factors of the factorial. -/
theorem topHalfPrimes_subset_oddFactorial130 (a : ℕ) :
    denseTopPrimes115 0 a ⊆
      a.factorial.primeFactors.filter
        (fun p => a.factorial.factorization p % 2 = 1) := by
  intro p hp
  have hpdata := Finset.mem_filter.mp hp
  have hpp : p.Prime := hpdata.2.1
  have hpa : p ≤ a := (Finset.mem_Icc.mp hpdata.1).2
  have hhalf : a / 2 < p := lt_of_le_of_lt (le_max_right 0 (a / 2)) hpdata.2.2
  have halt : a < 2 * p := by omega
  have hexp : a.factorial.factorization p = 1 :=
    factorization_factorial_eq_one_of_prime_le_lt_two_mul hpp hpa halt
  apply Finset.mem_filter.mpr
  refine ⟨?_, by simp [hexp]⟩
  apply Nat.mem_primeFactors.mpr
  refine ⟨hpp, ?_, Nat.factorial_ne_zero a⟩
  apply Nat.dvd_of_factorization_pos
  omega

/-- The product of the top-half primes divides the factorial squareclass. -/
theorem topHalfPrimeProduct_dvd_q130 (a : ℕ) :
    (∏ p ∈ denseTopPrimes115 0 a, p) ∣ q a := by
  unfold q sf
  exact Finset.prod_dvd_prod_of_subset _ _ id (topHalfPrimes_subset_oddFactorial130 a)

/-- No analytic hypothesis is needed for this theta lower bound on log q. -/
theorem theta_topHalf_le_log_q130 (a : ℕ) :
    thetaPrefix127 a - thetaPrefix127 (a / 2) ≤ Real.log (q a : ℝ) := by
  have hprodpos := denseTopPrimeProduct_pos115 0 a
  have hqpos : 0 < q a := Nat.pos_of_ne_zero (q_ne_zero a)
  have hprodle : (∏ p ∈ denseTopPrimes115 0 a, p) ≤ q a :=
    Nat.le_of_dvd hqpos (topHalfPrimeProduct_dvd_q130 a)
  have hlogle :
      Real.log ((∏ p ∈ denseTopPrimes115 0 a, p : ℕ) : ℝ) ≤
        Real.log (q a : ℝ) :=
    Real.log_le_log (by exact_mod_cast hprodpos) (by exact_mod_cast hprodle)
  rw [log_denseTopPrimeProduct115] at hlogle
  have hid := denseTopMass_eq_thetaDifference127 (b := 0) (c := a) (Nat.zero_le a)
  simpa only [max_eq_right (Nat.zero_le (a / 2))] using hid.symm.trans_le hlogle

/-- The log-squared remainder implies the ordinary relative theta error. -/
theorem theta_relative_error130
    (HT : ThetaLogSqRemainder127) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |thetaPrefix127 n - (n : ℝ)| ≤ ε * (n : ℝ) := by
  obtain ⟨NT, hNT⟩ := HT ε hε
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 1
  refine ⟨max NT NL, ?_⟩
  intro n hn
  have hnT : NT ≤ n := le_trans (le_max_left _ _) hn
  have hnL : NL ≤ n := le_trans (le_max_right _ _) hn
  have hl := hNL n hnL
  have hsq : 1 ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (abs_nonneg (thetaPrefix127 n - (n : ℝ)))
  have hmain := hNT n hnT
  nlinarith only [hmul, hmain]

/-- Theta alone supplies the squareclass growth formerly kept in PNTPackage. -/
theorem logQGrowth_from_theta130
    (HT : ThetaLogSqRemainder127) : LogQGrowth := by
  obtain ⟨N, hN⟩ := theta_relative_error130 HT (ε := (1 : ℝ) / 12) (by norm_num)
  refine ⟨2 * N + 2, ?_⟩
  intro a ha
  have haN : N ≤ a := by omega
  have haHalf : N ≤ a / 2 := by omega
  have hfull := (abs_le.mp (hN a haN)).1
  have hhalf := (abs_le.mp (hN (a / 2) haHalf)).2
  have hhalfNat : 2 * (a / 2) ≤ a := by omega
  have hhalfReal : 2 * ((a / 2 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hhalfNat
  have hbound := theta_topHalf_le_log_q130 a
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
  linarith

/-- The older package is constructed, not retained as an independent field. -/
def pntPackage_from_relative_theta130
    (HP : PrimeCountRelativePNT123) (HT : ThetaLogSqRemainder127) :
    RemainingAnalytic21.PNTPackage where
  prime_count_decay := primeCountDecay_from_relative130 HP
  log_q_growth := logQGrowth_from_theta130 HT

/-! ### B. A concrete guard against the obsolete exact-prefix bijection -/

theorem one_mem_A130 : 1 ∈ A := by
  refine ⟨by omega, squarefree_one, ?_⟩
  intro a ha
  have hq : 1 ≤ q a := Nat.one_le_iff_ne_zero.mpr (q_ne_zero a)
  simpa using hq

theorem q_two130 : q 2 = 2 := by
  classical
  have hpf : (2 : ℕ).primeFactors = {2} := Nat.prime_two.primeFactors
  have hfac : (2 : ℕ).factorization 2 = 1 := Nat.prime_two.factorization_self
  have hfilter :
      ({2} : Finset ℕ).filter (fun p => (2 : ℕ).factorization p % 2 = 1) = {2} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro hp
      subst p
      exact ⟨rfl, by rw [hfac] <;> norm_num⟩
  change sf 2 = 2
  unfold sf
  rw [hpf, hfilter, Finset.prod_singleton]

theorem two_not_mem_A130 : 2 ∉ A := by
  intro hA
  have hbad := hA.2.2 2 (by omega)
  norm_num [q_two130] at hbad

/-- The pair (1,2) remains in every sufficiently large raw pair prefix. -/
theorem raw_pair_two130 {X : ℕ} (hX : 2 ≤ X) :
    RemainingAnalytic50.CofactorPair50 X 1 2 := by
  exact ⟨one_mem_A130, Nat.prime_two, by norm_num, by simpa using hX⟩

/-- The historical bijection is false: a large X does not remove endpoint 2.
This does NOT refute an eventual-in-m bijection or the corrected count. -/
theorem not_legacy_prefix_bijection130 :
    ¬ RemainingAnalytic50.CofactorUniqueBijection50 := by
  rintro ⟨N, hN⟩
  have hX : 2 ≤ max N 2 := le_max_right _ _
  have hpair : ∃! rp : ℕ × ℕ,
      RemainingAnalytic50.CofactorPair50 (max N 2) rp.1 rp.2 ∧
        2 = rp.1 * rp.2 := by
    refine ⟨(1, 2), ⟨raw_pair_two130 hX, by norm_num⟩, ?_⟩
    intro rp hrp
    rcases rp with ⟨r, p⟩
    rcases hrp with ⟨hlegal, hmul⟩
    have hpp : p.Prime := hlegal.2.1
    have hdiv : p ∣ 2 := by
      rw [hmul]
      exact dvd_mul_left p r
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hdiv
    have hr1 : r = 1 := by
      rw [hp2] at hmul
      omega
    simp [hr1, hp2]
  have hB : 2 ∈ B alpha :=
    (hN (max N 2) 2 (le_max_left _ _) (by omega) hX).mpr hpair
  exact two_not_mem_A130 hB.1

/-! ### C. Finite corrections vanish: use the actual Repair-57 interface -/

/-- Exact normalized count with its necessary finite correction implies the
B-density asymptotic.  The correction is never silently discarded. -/
theorem bDensity_from_corrected_decomposition130
    (HC : RemainingAnalytic57.BCofactorExactDecompositionCorrected57)
    (HM : BCofactorMainTerm) (HL : BCofactorLowerEndpointError)
    {δ : ℝ} (hA : HasDensity A δ) :
    HasDensity (B alpha) (densityConstant δ) := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨NC, E, hNC⟩ := HC
  obtain ⟨NE, hNE⟩ := RemainingAnalytic57.fixedInt_div_nat_eventually_small57 E hε3
  obtain ⟨NM, hNM⟩ := HM δ hA (ε / 3) hε3
  obtain ⟨NL, hNL⟩ := HL (ε / 3) hε3
  refine ⟨max NC (max NE (max NM NL)), ?_⟩
  intro X hX
  have hXC : NC ≤ X := le_trans (le_max_left _ _) hX
  have hXrest : max NE (max NM NL) ≤ X := le_trans (le_max_right _ _) hX
  have hXE : NE ≤ X := le_trans (le_max_left _ _) hXrest
  have hXlast : max NM NL ≤ X := le_trans (le_max_right _ _) hXrest
  have hXM : NM ≤ X := le_trans (le_max_left _ _) hXlast
  have hXL : NL ≤ X := le_trans (le_max_right _ _) hXlast
  have he := abs_lt.mp (hNE X hXE)
  have hm := abs_lt.mp (hNM X hXM)
  have hl := hNL X hXL
  have hl0 := RemainingAnalytic43.cofactorLowerSum_nonneg X
  rw [hNC X hXC]
  apply abs_lt.mpr
  constructor <;> linarith

/-- All PNT-to-cofactor adapters, with no exact-count or five-code hypothesis. -/
theorem cofactorMain_from_relative_bare130
    (HD : Remaining_AFiniteDensityLimit47)
    (HTail : Remaining_AUniformTail47)
    (HP : PrimeCountRelativePNT123)
    (HBare : BareCofactorMassLimit127) : BCofactorMainTerm := by
  have hDensity := densityCofactorKernel_from_bareMass127 HBare
  have hL1 := cofactorKernelL1Bound_from_density118 HD HTail hDensity
  have hScale := scaleUniformPrimeCount_from_relative127 HP
  have hLegal := legalPointwiseCofactorPNT_from_scale121 hScale
  have hRelative := uniformRelativeCofactorPNT_from_legal120 hLegal
  have hSum := cofactorPNTErrorSum_from_relative_l1_117 hRelative hL1
  have hUniform := RemainingAnalytic116.uniformCofactorPNTKernel_from_errorSum116 hSum
  exact cofactorMain_from_kernelPieces115 hUniform hDensity

/-- A corrected integer count is sufficient; the E=0 count is unnecessary. -/
theorem bDensity_from_corrected_count130
    (HD : Remaining_AFiniteDensityLimit47)
    (HTail : Remaining_AUniformTail47)
    (HP : PrimeCountRelativePNT123)
    (HBare : BareCofactorMassLimit127)
    (HC : RemainingAnalytic57.BCofactorIntegerCountIdentityCorrected57)
    {δ : ℝ} (hA : HasDensity A δ) :
    HasDensity (B alpha) (densityConstant δ) := by
  exact bDensity_from_corrected_decomposition130
    (RemainingAnalytic57.cofactorExactDecompositionCorrected_from_integer57 HC)
    (cofactorMain_from_relative_bare130 HD HTail HP HBare)
    (RemainingAnalytic109.cofactorLowerEndpointError_from_primeDecay_closed109
      (primeCountDecay_from_relative130 HP)) hA

/-! ### D. Cofactor inheritance is a consequence of factorial growth -/

/-- Elementary logarithm domination with an explicit multiplicative constant. -/
theorem scaled_log_le_rpow130 {β : ℝ} (hβ : 0 < β)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → C * Real.log (m : ℝ) ≤ (m : ℝ) ^ β := by
  obtain ⟨NL, hNL⟩ := RemainingAnalytic55.log_le_rpow_eventually55
    (gap := β / 2) (by linarith)
  obtain ⟨NC, hNC⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := β / 2) (C := C) (by linarith)
  refine ⟨max 1 (max NL NC), ?_⟩
  intro m hm
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
  have hmr : max NL NC ≤ m := le_trans (le_max_right _ _) hm
  have hmL : NL ≤ m := le_trans (le_max_left _ _) hmr
  have hmC : NC ≤ m := le_trans (le_max_right _ _) hmr
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hp : 0 ≤ (m : ℝ) ^ (β / 2) := Real.rpow_nonneg (le_of_lt hmp) _
  calc
    C * Real.log (m : ℝ) ≤ C * (m : ℝ) ^ (β / 2) :=
      mul_le_mul_of_nonneg_left (hNL m hmL) hC
    _ ≤ (m : ℝ) ^ (β / 2) * (m : ℝ) ^ (β / 2) :=
      mul_le_mul_of_nonneg_right (le_of_lt (hNC m hmC)) hp
    _ = (m : ℝ) ^ β := by
      rw [← Real.rpow_add hmp]
      congr 1
      ring

/-- The dominant prime exceeds the cofactor; the proof uses exact log algebra. -/
theorem cofactor_lt_dominant_prime130 {r P : ℕ} {α : ℝ}
    (hr : 1 ≤ r) (hP : P.Prime) (hα : α < (1 : ℝ) / 2)
    (hlarge : ((r * P : ℕ) : ℝ) ^ (1 - α) < (P : ℝ)) : r < P := by
  have hrp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hPp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP.pos
  have hmpos : (0 : ℝ) < ((r * P : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_pos hrp hPp
  have hpLog : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hP.one_lt)
  have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hmpos _) hlarge
  rw [Real.log_rpow hmpos] at hlog
  have hmulLog : Real.log ((r * P : ℕ) : ℝ) =
      Real.log (r : ℝ) + Real.log (P : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (ne_of_gt hrp) (ne_of_gt hPp)]
  rw [hmulLog] at hlog
  by_contra hnot
  have hPr : (P : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hnot)
  have hlogs := Real.log_le_log hPp hPr
  have hβ : 0 < 1 - α := by linarith
  have hweighted := mul_nonneg (le_of_lt hβ) (sub_nonneg.mpr hlogs)
  have hmargin := mul_pos (show 0 < 1 - 2 * α by linarith) hpLog
  nlinarith

/-- A sufficiently large prime can be adjoined without changing any gcd
restriction in A: below P the gcd is unchanged; at and above P it is tiny
compared with q(a).  All a >= 2 are covered, not just a below the endpoint. -/
theorem mem_A_mul_prime_of_growth130
    {r P Nq : ℕ}
    (hGrowth : ∀ a : ℕ, Nq ≤ a → (a : ℝ) / 3 ≤ Real.log (q a : ℝ))
    (hrA : r ∈ A) (hP : P.Prime) (hrP : r < P)
    (hNqP : Nq ≤ P)
    (hscale : 6 * Real.log ((r * P : ℕ) : ℝ) ≤ (P : ℝ)) :
    r * P ∈ A := by
  have hrpos : 0 < r := by have := hrA.1; omega
  have hmpos : 0 < r * P := Nat.mul_pos hrpos hP.pos
  have hmposR : (0 : ℝ) < ((r * P : ℕ) : ℝ) := by exact_mod_cast hmpos
  have hnot : ¬ P ∣ r := by
    intro hd
    exact (not_le_of_gt hrP) (Nat.le_of_dvd hrpos hd)
  have hcop : r.Coprime P := ((hP.coprime_iff_not_dvd).mpr hnot).symm
  have hsf : Squarefree (r * P) :=
    (Nat.squarefree_mul hcop).mpr ⟨hrA.2.1, hP.squarefree⟩
  refine ⟨by omega, hsf, ?_⟩
  intro a ha
  by_cases haP : a < P
  · have hnotq : ¬ P ∣ q a := by
      intro hd
      have hle := RemainingAnalytic65.primeDivisorQLe_proved65 a P hP hd
      omega
    have hcq : P.Coprime (q a) := (hP.coprime_iff_not_dvd).mpr hnotq
    have hgc : Nat.gcd (r * P) (q a) = Nat.gcd r (q a) :=
      Nat.Coprime.gcd_mul_right_cancel r hcq
    rw [hgc]
    exact hrA.2.2 a ha
  · have hPa : P ≤ a := Nat.le_of_not_gt haP
    have hNa : Nq ≤ a := le_trans hNqP hPa
    have haLog := hGrowth a hNa
    have hPaR : (P : ℝ) ≤ (a : ℝ) := by exact_mod_cast hPa
    have hlog : 2 * Real.log ((r * P : ℕ) : ℝ) ≤ Real.log (q a : ℝ) := by
      linarith
    have hqposR : (0 : ℝ) < (q a : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero (q_ne_zero a))
    have hm2pos : (0 : ℝ) < (((r * P : ℕ) : ℝ) ^ (2 : ℕ)) := by positivity
    have hlog2 : Real.log (((r * P : ℕ) : ℝ) ^ (2 : ℕ)) ≤ Real.log (q a : ℝ) := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
    have hboundR : (((r * P : ℕ) : ℝ) ^ (2 : ℕ)) ≤ (q a : ℝ) :=
      (Real.log_le_log_iff hm2pos hqposR).mp hlog2
    have hbound : (r * P) ^ 2 ≤ q a := by exact_mod_cast hboundR
    have hg : Nat.gcd (r * P) (q a) ≤ r * P :=
      Nat.le_of_dvd hmpos (Nat.gcd_dvd_left (r * P) (q a))
    have hg2 : (Nat.gcd (r * P) (q a)) ^ 2 ≤ (r * P) ^ 2 := by
      nlinarith
    exact le_trans hg2 hbound

/-- The entire inheritance assumption is derived from logarithmic q-growth. -/
theorem cofactorInheritance_from_logQGrowth130
    (HG : LogQGrowth) : Tasks.CofactorInheritance := by
  intro α hα0 hαhalf
  obtain ⟨Nq, hNq⟩ := HG
  have hβ : 0 < 1 - α := by linarith
  obtain ⟨NL, hNL⟩ := scaled_log_le_rpow130 hβ 6 (by norm_num)
  obtain ⟨NQ, hNQ⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := 1 - α) (C := (Nq : ℝ)) hβ
  refine ⟨max NL NQ, ?_⟩
  intro r P hm hP hlarge
  constructor
  · intro hmA
    exact A_divisor_closed hmA (dvd_mul_right r P)
  · intro hrA
    have hmL : NL ≤ r * P := le_trans (le_max_left _ _) hm
    have hmQ : NQ ≤ r * P := le_trans (le_max_right _ _) hm
    have hscale := le_trans (hNL (r * P) hmL) (le_of_lt hlarge)
    have hNP : (Nq : ℝ) < (P : ℝ) := lt_trans (hNQ (r * P) hmQ) hlarge
    have hNPnat : Nq ≤ P := by exact_mod_cast (le_of_lt hNP)
    exact mem_A_mul_prime_of_growth130 hNq hrA hP
      (cofactor_lt_dominant_prime130 hrA.1 hP hαhalf hlarge) hNPnat hscale

theorem cofactorInheritance_from_theta130
    (HT : ThetaLogSqRemainder127) : Tasks.CofactorInheritance :=
  cofactorInheritance_from_logQGrowth130 (logQGrowth_from_theta130 HT)

/-! ### E. The bare cofactor kernel: an explicit sum--integral squeeze -/

noncomputable def rawKernel130 (x t : ℝ) : ℝ :=
  1 / (t * Real.log (x / t))

/-- Increasing the upper endpoint increases the integral of a nonnegative
continuous function.  Stated with elementary interval hypotheses. -/
theorem integral_prefix_mono130 {f : ℝ → ℝ} {u v : ℝ}
    (hu : 1 ≤ u) (huv : u ≤ v)
    (hc : ContinuousOn f (Set.Icc 1 v))
    (hp : ∀ t ∈ Set.Icc 1 v, 0 ≤ f t) :
    (∫ t in (1 : ℝ)..u, f t) ≤ ∫ t in (1 : ℝ)..v, f t := by
  have hc1u : ContinuousOn f (Set.Icc 1 u) :=
    hc.mono (by intro t ht; exact ⟨ht.1, le_trans ht.2 huv⟩)
  have hcuv : ContinuousOn f (Set.Icc u v) :=
    hc.mono (by intro t ht; exact ⟨le_trans hu ht.1, ht.2⟩)
  have hi1u : IntervalIntegrable f MeasureTheory.volume 1 u :=
    ContinuousOn.intervalIntegrable_of_Icc hu hc1u
  have hiuv : IntervalIntegrable f MeasureTheory.volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv hcuv
  have hnonneg : 0 ≤ ∫ t in u..v, f t :=
    intervalIntegral.integral_nonneg huv (by
      intro t ht
      exact hp t ⟨le_trans hu ht.1, ht.2⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1u hiuv
  linarith

/-- Left endpoint samples of a positive decreasing function bracket its
integral at a real cutoff, with error at most its first value. -/
theorem sum_floor_integral_squeeze130 {f : ℝ → ℝ} {u : ℝ}
    (hu : 1 ≤ u)
    (hc : ContinuousOn f (Set.Icc 1 (u + 1)))
    (hp : ∀ t ∈ Set.Icc 1 (u + 1), 0 ≤ f t)
    (hm : AntitoneOn f (Set.Icc 1 (u + 1))) :
    (∫ t in (1 : ℝ)..u, f t) ≤
        ∑ i ∈ Finset.range ⌊u⌋₊, f ((i + 1 : ℕ) : ℝ) ∧
    (∑ i ∈ Finset.range ⌊u⌋₊, f ((i + 1 : ℕ) : ℝ)) ≤
        (∫ t in (1 : ℝ)..u, f t) + f 1 := by
  let M : ℕ := ⌊u⌋₊
  have hu0 : 0 ≤ u := by linarith
  have hM1 : 1 ≤ M := (Nat.le_floor_iff hu0).mpr (by simpa using hu)
  have hMu : (M : ℝ) ≤ u := Nat.floor_le hu0
  have huM : u < (M : ℝ) + 1 := Nat.lt_floor_add_one u
  have hMR1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hmBig : AntitoneOn f (Set.Icc 1 (1 + (M : ℝ))) :=
    hm.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hcBig : ContinuousOn f (Set.Icc 1 (1 + (M : ℝ))) :=
    hc.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hpBig : ∀ t ∈ Set.Icc 1 (1 + (M : ℝ)), 0 ≤ f t := by
    intro t ht
    exact hp t ⟨ht.1, by linarith [ht.2]⟩
  have hleft := hmBig.integral_le_sum
  have hleft' : (∫ t in (1 : ℝ)..((M : ℝ) + 1), f t) ≤
      ∑ i ∈ Finset.range M, f ((i + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hleft
  have hIleft : (∫ t in (1 : ℝ)..u, f t) ≤
      ∫ t in (1 : ℝ)..((M : ℝ) + 1), f t := by
    apply integral_prefix_mono130 hu (le_of_lt huM)
    · simpa only [add_comm] using hcBig
    · simpa only [add_comm] using hpBig
  constructor
  · exact le_trans hIleft hleft'
  · have hMsub : M - 1 + 1 = M := by omega
    have hMsubR : 1 + ((M - 1 : ℕ) : ℝ) = (M : ℝ) := by
      have hh : (((M - 1 + 1 : ℕ) : ℝ)) = (M : ℝ) := by rw [hMsub]
      push_cast at hh
      linarith
    have hmSmall : AntitoneOn f (Set.Icc 1 (1 + ((M - 1 : ℕ) : ℝ))) :=
      hm.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])
    have hright := hmSmall.sum_le_integral
    have hright' : (∑ i ∈ Finset.range (M - 1), f ((i + 2 : ℕ) : ℝ)) ≤
        ∫ t in (1 : ℝ)..(M : ℝ), f t := by
      convert hright using 1 <;>
        norm_num [hMsubR, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
    have hcSmall : ContinuousOn f (Set.Icc 1 u) :=
      hc.mono (by intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩)
    have hpSmall : ∀ t ∈ Set.Icc 1 u, 0 ≤ f t := by
      intro t ht
      exact hp t ⟨ht.1, by linarith [ht.2]⟩
    have hIright := integral_prefix_mono130 hMR1 hMu hcSmall hpSmall
    have hsplit : (∑ i ∈ Finset.range M, f ((i + 1 : ℕ) : ℝ)) =
        f 1 + ∑ i ∈ Finset.range (M - 1), f ((i + 2 : ℕ) : ℝ) := by
      have hh := Finset.sum_range_succ' (fun i : ℕ => f ((i + 1 : ℕ) : ℝ)) (M - 1)
      rw [hMsub] at hh
      convert hh using 1 <;>
        norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
    rw [hsplit]
    linarith

/-- Uniform positivity of the ratio on the interval used by the integral test. -/
theorem kernel_ratio_lower130 {x u t : ℝ}
    (hu : 1 ≤ u) (hs : Real.exp 1 * (u + 1) ≤ x)
    (ht : t ∈ Set.Icc 1 (u + 1)) :
    Real.exp 1 ≤ x / t ∧ 1 < x / t := by
  have htp : 0 < t := by linarith [ht.1]
  have hmul := mul_le_mul_of_nonneg_left ht.2 (le_of_lt (Real.exp_pos 1))
  have hratio : Real.exp 1 ≤ x / t := (le_div_iff₀ htp).mpr (le_trans hmul hs)
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num))
  exact ⟨hratio, lt_of_lt_of_le he hratio⟩

/-- The kernel is continuous and positive throughout the comparison interval. -/
theorem rawKernel_regular130 {x u : ℝ}
    (hu : 1 ≤ u) (hs : Real.exp 1 * (u + 1) ≤ x) :
    ContinuousOn (rawKernel130 x) (Set.Icc 1 (u + 1)) ∧
    (∀ t ∈ Set.Icc 1 (u + 1), 0 ≤ rawKernel130 x t) ∧
    AntitoneOn (rawKernel130 x) (Set.Icc 1 (u + 1)) := by
  have hxp : 0 < x := lt_of_lt_of_le
    (mul_pos (Real.exp_pos 1) (by linarith)) hs
  constructor
  · intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have hratio := kernel_ratio_lower130 hu hs ht
    have hr0 : x / t ≠ 0 := ne_of_gt (by linarith [hratio.2])
    have hl0 : Real.log (x / t) ≠ 0 := ne_of_gt (Real.log_pos hratio.2)
    have hq : ContinuousAt (fun y : ℝ => x / y) t :=
      continuousAt_const.div continuousAt_id (ne_of_gt htp)
    have hd : ContinuousAt (fun y : ℝ => y * Real.log (x / y)) t :=
      continuousAt_id.mul (hq.log hr0)
    exact (continuousAt_const.div hd (mul_ne_zero (ne_of_gt htp) hl0)).continuousWithinAt
  constructor
  · intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have hlp := Real.log_pos (kernel_ratio_lower130 hu hs ht).2
    exact le_of_lt (one_div_pos.mpr (mul_pos htp hlp))
  · intro r hr s hss hrs
    exact reciprocalLog_antitone127 hxp (by linarith [hr.1]) hrs
      (kernel_ratio_lower130 hu hs hss).2 (kernel_ratio_lower130 hu hs hss).1

/-- Differentiate the explicit antiderivative; this is an actual calculus
proof, not a newly introduced normalization assumption. -/
theorem rawKernel_hasPrimitive130 {x t : ℝ}
    (hx : 0 < x) (ht : 0 < t) (htx : t < x) :
    HasDerivAt (fun y : ℝ => -Real.log (Real.log x - Real.log y))
      (rawKernel130 x t) t := by
  have hlog : 0 < Real.log x - Real.log t := by
    have hh := Real.log_lt_log ht htx
    linarith
  have hder := (((Real.hasDerivAt_log (ne_of_gt ht)).const_sub (Real.log x)).log
    (ne_of_gt hlog)).neg
  convert hder using 1 <;>
    simp only [rawKernel130, Real.log_div (ne_of_gt hx) (ne_of_gt ht)] <;>
    field_simp [ne_of_gt ht, ne_of_gt hlog] <;> ring

/-- Exact integral at the real power cutoff. -/
theorem rawKernel_integral130 {x : ℝ} (hx : 1 < x) :
    (∫ t in (1 : ℝ)..(x ^ alpha), rawKernel130 x t) =
      Real.log ((100 : ℝ) / 99) := by
  have hxp : 0 < x := by linarith
  have hα0 : 0 ≤ alpha := by norm_num [alpha]
  have hu : 1 ≤ x ^ alpha := Real.one_le_rpow (le_of_lt hx) hα0
  have hux : x ^ alpha < x := rpow_alpha_lt_self118 hx
  have hcont : ContinuousOn (rawKernel130 x) (Set.Icc 1 (x ^ alpha)) := by
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have htx : t < x := lt_of_le_of_lt ht.2 hux
    have hratio : 1 < x / t := (lt_div_iff₀ htp).mpr (by simpa using htx)
    have hq : ContinuousAt (fun y : ℝ => x / y) t :=
      continuousAt_const.div continuousAt_id (ne_of_gt htp)
    have hd : ContinuousAt (fun y : ℝ => y * Real.log (x / y)) t :=
      continuousAt_id.mul (hq.log (ne_of_gt (by linarith : 0 < x / t)))
    exact (continuousAt_const.div hd
      (mul_ne_zero (ne_of_gt htp) (ne_of_gt (Real.log_pos hratio)))).continuousWithinAt
  have hder : ∀ t ∈ Set.uIcc (1 : ℝ) (x ^ alpha),
      HasDerivAt (fun y : ℝ => -Real.log (Real.log x - Real.log y))
        (rawKernel130 x t) t := by
    intro t ht
    rw [Set.uIcc_of_le hu] at ht
    exact rawKernel_hasPrimitive130 hxp (by linarith [ht.1]) (lt_of_le_of_lt ht.2 hux)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hcont.intervalIntegrable_of_Icc hu)
  rw [hI, Real.log_rpow hxp, Real.log_one, sub_zero]
  have hfactor : Real.log x - alpha * Real.log x = (1 - alpha) * Real.log x := by ring
  rw [hfactor, Real.log_mul (by norm_num [alpha] : 1 - alpha ≠ 0)
    (ne_of_gt (Real.log_pos hx))]
  have hrecip : Real.log ((100 : ℝ) / 99) = -Real.log (1 - alpha) := by
    have heq : (100 : ℝ) / 99 = (1 - alpha)⁻¹ := by norm_num [alpha]
    rw [heq, Real.log_inv]
  rw [hrecip]
  ring

/-- The cutoff lies well inside the decreasing part of the real kernel. -/
theorem kernel_scale_eventually130 :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      2 ≤ X ∧ Real.exp 1 * ((X : ℝ) ^ alpha + 1) ≤ (X : ℝ) := by
  obtain ⟨N, hN⟩ := RemainingAnalytic55.fixed_lt_rpow_eventually55
    (gap := 1 - alpha) (C := 2 * Real.exp 1) (by norm_num [alpha])
  refine ⟨max N 2, ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hU1 : 1 ≤ (X : ℝ) ^ alpha := Real.one_le_rpow hX1 (by norm_num [alpha])
  have hUp : 0 < (X : ℝ) ^ alpha := Real.rpow_pos_of_pos hXp _
  have hmul := mul_lt_mul_of_pos_right (hN X hXN) hUp
  have hprod : (X : ℝ) ^ (1 - alpha) * (X : ℝ) ^ alpha = (X : ℝ) := by
    rw [← Real.rpow_add hXp, sub_add_cancel, Real.rpow_one]
  rw [hprod] at hmul
  have hsmall := mul_le_mul_of_nonneg_left hU1 (le_of_lt (Real.exp_pos 1))
  refine ⟨hX2, ?_⟩
  nlinarith only [hmul, hsmall]

/-- The row cutoff agrees exactly with the floor-cutoff scalar sum. -/
theorem bareRow_eq_floor_sum130 {X : ℕ} (hX : 2 ≤ X) :
    (∑ i ∈ Finset.range X, cofactorRow127 X i) =
      ∑ i ∈ Finset.range ⌊(X : ℝ) ^ alpha⌋₊,
        rawKernel130 (X : ℝ) ((i + 1 : ℕ) : ℝ) := by
  classical
  let U : ℝ := (X : ℝ) ^ alpha
  let M : ℕ := ⌊U⌋₊
  have hU0 : 0 ≤ U := Real.rpow_nonneg (by positivity) _
  have hMU : (M : ℝ) ≤ U := Nat.floor_le hU0
  have hUX : U < (X : ℝ) := rpow_alpha_lt_self118 (by exact_mod_cast (show 1 < X by omega))
  have hMX : M ≤ X := by exact_mod_cast (le_of_lt (lt_of_le_of_lt hMU hUX))
  have hsubset : Finset.range M ⊆ Finset.range X := Finset.range_mono hMX
  have hzero : ∀ i ∈ Finset.range X, i ∉ Finset.range M → cofactorRow127 X i = 0 := by
    intro i hi hnot
    have hMi : M ≤ i := by simpa only [Finset.mem_range, not_lt] using hnot
    have hcut : ¬ ((i + 1 : ℕ) : ℝ) ≤ U := by
      intro hh
      have hn : i + 1 ≤ M := (Nat.le_floor_iff hU0).mpr hh
      omega
    unfold cofactorRow127
    exact if_neg (fun h => hcut h.2)
  calc
    (∑ i ∈ Finset.range X, cofactorRow127 X i) =
        ∑ i ∈ Finset.range M, cofactorRow127 X i :=
      (Finset.sum_subset hsubset hzero).symm
    _ = ∑ i ∈ Finset.range M, rawKernel130 (X : ℝ) ((i + 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiM : i < M := Finset.mem_range.mp hi
      have hiX : i < X := lt_of_lt_of_le hiM hMX
      have hiU : ((i + 1 : ℕ) : ℝ) ≤ U :=
        (Nat.le_floor_iff hU0).mp (show i + 1 ≤ M by omega)
      have hlegal : i < X ∧ ((i + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ alpha :=
        ⟨hiX, hiU⟩
      unfold cofactorRow127
      rw [if_pos hlegal]
      rfl

/-- An explicit quantitative estimate closes the residual scalar mass input. -/
theorem bareKernel_error_bound130 {X : ℕ}
    (hX : 2 ≤ X)
    (hs : Real.exp 1 * ((X : ℝ) ^ alpha + 1) ≤ (X : ℝ)) :
    0 ≤ (∑ i ∈ Finset.range X, cofactorRow127 X i) - Real.log ((100 : ℝ) / 99) ∧
    (∑ i ∈ Finset.range X, cofactorRow127 X i) - Real.log ((100 : ℝ) / 99) ≤
      1 / Real.log (X : ℝ) := by
  have hx : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hu : 1 ≤ (X : ℝ) ^ alpha := Real.one_le_rpow (le_of_lt hx) (by norm_num [alpha])
  obtain ⟨hc, hp, hm⟩ := rawKernel_regular130 hu hs
  have hb := sum_floor_integral_squeeze130 hu hc hp hm
  rw [rawKernel_integral130 hx] at hb
  rw [bareRow_eq_floor_sum130 hX]
  have hhead : rawKernel130 (X : ℝ) 1 = 1 / Real.log (X : ℝ) := by simp [rawKernel130]
  rw [hhead] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- The bare mass limit is proved without arithmetic or analytic inputs. -/
theorem bareCofactorMassLimit_proved130 : BareCofactorMassLimit127 := by
  intro ε hε
  obtain ⟨NS, hNS⟩ := kernel_scale_eventually130
  obtain ⟨NL, hNL⟩ := eventually_log_ge127 (1 / ε + 1)
  refine ⟨max NS NL, ?_⟩
  intro X hX
  have hXS : NS ≤ X := le_trans (le_max_left _ _) hX
  have hXL : NL ≤ X := le_trans (le_max_right _ _) hX
  have hscale := hNS X hXS
  have herr := bareKernel_error_bound130 hscale.1 hscale.2
  have hl := hNL X hXL
  have hlogp : 0 < Real.log (X : ℝ) := by
    have hh : 0 < 1 / ε := one_div_pos.mpr hε
    linarith
  have hsmall : 1 / Real.log (X : ℝ) < ε := by
    apply (div_lt_iff₀ hlogp).mpr
    have hh := mul_le_mul_of_nonneg_left hl (le_of_lt hε)
    have hid : ε * (1 / ε + 1) = 1 + ε := by field_simp [ne_of_gt hε] <;> ring
    rw [hid] at hh
    linarith
  rw [abs_of_nonneg herr.1]
  exact lt_of_le_of_lt herr.2 hsmall

/-- The original set-dependent density-kernel theorem now has a proof term. -/
theorem densityCofactorKernel_proved130 : DensityCofactorKernelLimit115 :=
  densityCofactorKernel_from_bareMass127 bareCofactorMassLimit_proved130


/-! ### F. The actual cofactor count, with a finite exceptional set

Unlike the historical pair interface, the raw endpoint set below is not
identified with B at small endpoints.  We count it exactly, prove that it
agrees with B eventually in the ENDPOINT, and retain the resulting correction.
-/

/-- Endpoint set counted by the raw cofactor-prime sum. -/
def rawEndpoints130 : Set ℕ :=
  {m | ∃ r P : ℕ, r ∈ A ∧ P.Prime ∧ r ^ 99 < P ∧ m = r * P}

/-- Actual finite pairs, in a constant-family sigma type. -/
def rawPairs130 (X : ℕ) : Finset (Sigma (fun _ : ℕ => ℕ)) :=
  (Finset.Icc 1 X).sigma (fun r =>
    (Finset.Icc (r ^ 99 + 1) (X / r)).filter (fun P => r ∈ A ∧ P.Prime))

/-- A positive integer is bounded by its 99th power. -/
theorem self_le_pow99_130 {r : ℕ} (hr : 1 ≤ r) : r ≤ r ^ 99 := by
  have hpow : 1 ≤ r ^ 98 := by
    have hp : 0 < r ^ 98 := pow_pos (by omega) _
    omega
  have hh := Nat.mul_le_mul_right r hpow
  simpa only [one_mul, ← pow_succ] using hh

/-- Two legal products have the same prime and cofactor: both displayed primes
exceed their cofactors, so Euclid's lemma forces them to coincide. -/
theorem dominant_pair_unique130 {r P s Q : ℕ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hP : P.Prime) (hQ : Q.Prime)
    (hrP : r ^ 99 < P) (hsQ : s ^ 99 < Q)
    (heq : r * P = s * Q) : r = s ∧ P = Q := by
  have hrlt : r < P := lt_of_le_of_lt (self_le_pow99_130 hr) hrP
  have hslt : s < Q := lt_of_le_of_lt (self_le_pow99_130 hs) hsQ
  have hPQ : P = Q := by
    by_contra hne
    have hPdiv : P ∣ s * Q := by rw [← heq]; exact dvd_mul_left P r
    have hQdiv : Q ∣ r * P := by rw [heq]; exact dvd_mul_left Q s
    have hPs : P ∣ s := by
      rcases hP.dvd_mul.mp hPdiv with hh | hh
      · exact hh
      · exact (hne ((Nat.prime_dvd_prime_iff_eq hP hQ).mp hh)).elim
    have hQr : Q ∣ r := by
      rcases hQ.dvd_mul.mp hQdiv with hh | hh
      · exact hh
      · exact (hne ((Nat.prime_dvd_prime_iff_eq hQ hP).mp hh).symm).elim
    have hPles := Nat.le_of_dvd (show 0 < s by omega) hPs
    have hQler := Nat.le_of_dvd (show 0 < r by omega) hQr
    omega
  have hrs : r = s := by
    rw [hPQ] at heq
    have hQpos := hQ.pos
    nlinarith
  exact ⟨hrs, hPQ⟩

/-- A sigma pair has exactly the raw-pair conditions. -/
theorem mem_rawPairs130 {X : ℕ} {rp : Sigma (fun _ : ℕ => ℕ)} :
    rp ∈ rawPairs130 X ↔
      rp.1 ∈ A ∧ rp.2.Prime ∧ rp.1 ^ 99 < rp.2 ∧ rp.1 * rp.2 ≤ X := by
  constructor
  · intro hp
    have h := Finset.mem_sigma.mp hp
    have hr := Finset.mem_Icc.mp h.1
    have hf := Finset.mem_filter.mp h.2
    have hP := Finset.mem_Icc.mp hf.1
    have hmul : rp.2 * rp.1 ≤ X :=
      (Nat.le_div_iff_mul_le (show 0 < rp.1 by omega)).mp hP.2
    exact ⟨hf.2.1, hf.2.2, by omega, by simpa only [mul_comm] using hmul⟩
  · rintro ⟨hrA, hP, hpow, hmul⟩
    have hr1 := hrA.1
    have hP1 := hP.one_lt
    have hrX : rp.1 ≤ X := by
      have hle := Nat.mul_le_mul_left rp.1 (show 1 ≤ rp.2 by omega)
      simp only [mul_one] at hle
      exact le_trans hle hmul
    have hPdiv : rp.2 ≤ X / rp.1 :=
      (Nat.le_div_iff_mul_le (show 0 < rp.1 by omega)).mpr
        (by simpa only [mul_comm] using hmul)
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_Icc.mpr ⟨hr1, hrX⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hPdiv⟩, hrA, hP⟩⟩

/-- Exact equality of the product image and the raw endpoint prefix. -/
theorem rawPairs_image130 (X : ℕ) :
    (rawPairs130 X).image (fun rp => rp.1 * rp.2) =
      (Finset.Icc 1 X).filter (fun m => m ∈ rawEndpoints130) := by
  ext m
  constructor
  · intro hm
    obtain ⟨rp, hrp, hmul⟩ := Finset.mem_image.mp hm
    obtain ⟨hrA, hP, hpow, hmX⟩ := mem_rawPairs130.mp hrp
    have hmpos : 0 < rp.1 * rp.2 := Nat.mul_pos (by have := hrA.1; omega) hP.pos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    exact ⟨rp.1, rp.2, hrA, hP, hpow, hmul.symm⟩
  · intro hm
    obtain ⟨hmI, r, P, hrA, hP, hpow, hmul⟩ := Finset.mem_filter.mp hm
    refine Finset.mem_image.mpr ⟨⟨r, P⟩, ?_, hmul.symm⟩
    apply mem_rawPairs130.mpr
    exact ⟨hrA, hP, hpow, by simpa only [← hmul] using (Finset.mem_Icc.mp hmI).2⟩

/-- The product map is injective on actual legal pairs. -/
theorem rawPairs_injective130 (X : ℕ) :
    Set.InjOn (fun rp : Sigma (fun _ : ℕ => ℕ) => rp.1 * rp.2) (rawPairs130 X) := by
  intro rp hrp sq hsq heq
  obtain ⟨hrA, hP, hrpow, hrX⟩ := mem_rawPairs130.mp hrp
  obtain ⟨hsA, hQ, hspow, hsX⟩ := mem_rawPairs130.mp hsq
  obtain ⟨hr, hPq⟩ := dominant_pair_unique130 hrA.1 hsA.1 hP hQ hrpow hspow heq
  cases rp with
  | mk r P =>
    cases sq with
    | mk s Q =>
      dsimp at hr hPq
      subst s
      subst Q
      rfl

/-- Exact raw endpoint count, before any use of cofactor inheritance. -/
theorem rawEndpointCount_eq_pairCount130 (X : ℕ) :
    prefixCount rawEndpoints130 X = RemainingAnalytic55.cofactorPairCount55 X := by
  have hcard := Finset.card_image_iff.mpr (rawPairs_injective130 X)
  rw [rawPairs_image130] at hcard
  calc
    prefixCount rawEndpoints130 X = (rawPairs130 X).card := hcard
    _ = RemainingAnalytic55.cofactorPairCount55 X := by
      simp only [rawPairs130, Finset.card_sigma, RemainingAnalytic55.cofactorPairCount55]

/-- The natural prefix count is monotone in its endpoint. -/
theorem prefixCount_endpoint_mono130 (S : Set ℕ) {n m : ℕ} (hnm : n ≤ m) :
    prefixCount S n ≤ prefixCount S m := by
  apply Finset.card_le_card
  intro k hk
  have h := Finset.mem_filter.mp hk
  have hkI := Finset.mem_Icc.mp h.1
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hkI.1, le_trans hkI.2 hnm⟩, h.2⟩

/-- The real power cutoff is exactly the integer 100th-power cutoff. -/
theorem cofactor_cutoff_iff_pow130 {X r : ℕ} (hX : 1 ≤ X) :
    (r : ℝ) ≤ (X : ℝ) ^ alpha ↔ r ^ 100 ≤ X := by
  have hpower := RemainingAnalytic109.rpow_alpha_pow_hundred109 hX
  have hU0 : 0 ≤ (X : ℝ) ^ alpha := Real.rpow_nonneg (by positivity) _
  constructor
  · intro hr
    have hh : (r : ℝ) ^ (100 : ℕ) ≤ ((X : ℝ) ^ alpha) ^ (100 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hr _
    rw [hpower] at hh
    exact_mod_cast hh
  · intro hr
    have hh : (r : ℝ) ^ (100 : ℕ) ≤ ((X : ℝ) ^ alpha) ^ (100 : ℕ) := by
      rw [hpower]
      exact_mod_cast hr
    exact le_of_pow_le_pow_left₀ (by norm_num : (100 : ℕ) ≠ 0) hU0 hh

/-- Cast the fiberwise Nat subtraction only where it is untruncated.  Outside
that range the Nat subtraction is zero and the power-cutoff indicator is zero. -/
theorem rawEndpointCount_integer130 {X : ℕ} (hX : 1 ≤ X) :
    (prefixCount rawEndpoints130 X : ℤ) =
      ∑ r ∈ Finset.Icc 1 X,
        if r ∈ A ∧ (r : ℝ) ≤ (X : ℝ) ^ alpha then
          (prefixCount {p : ℕ | p.Prime} (X / r) : ℤ) -
            (prefixCount {p : ℕ | p.Prime} (r ^ 99) : ℤ)
        else 0 := by
  rw [rawEndpointCount_eq_pairCount130, RemainingAnalytic55.cofactorPairCount_eq_sum55,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hrp : 0 < r := by omega
  by_cases hrA : r ∈ A
  · by_cases hcut : (r : ℝ) ≤ (X : ℝ) ^ alpha
    · have hpow : r ^ 100 ≤ X := (cofactor_cutoff_iff_pow130 hX).mp hcut
      have hmul : r ^ 99 * r ≤ X := by
        rw [show r ^ 100 = r ^ 99 * r from pow_succ r 99] at hpow
        exact hpow
      have hdiv : r ^ 99 ≤ X / r := (Nat.le_div_iff_mul_le hrp).mpr hmul
      have hpi := prefixCount_endpoint_mono130 {p : ℕ | p.Prime} hdiv
      simp only [hrA, hcut, and_self, ite_true]
      have hadd := Nat.sub_add_cancel hpi
      have haddZ :
          ((prefixCount {p : ℕ | p.Prime} (X / r) -
              prefixCount {p : ℕ | p.Prime} (r ^ 99) : ℕ) : ℤ) +
            (prefixCount {p : ℕ | p.Prime} (r ^ 99) : ℤ) =
          (prefixCount {p : ℕ | p.Prime} (X / r) : ℤ) := by
        exact_mod_cast hadd
      linarith only [haddZ]
    · have hpow : X < r ^ 100 := by
        have hh : ¬ r ^ 100 ≤ X := fun hh => hcut ((cofactor_cutoff_iff_pow130 hX).mpr hh)
        omega
      have hdiv : X / r < r ^ 99 := by
        by_contra hh
        have hle : r ^ 99 ≤ X / r := by omega
        have hmul := (Nat.le_div_iff_mul_le hrp).mp hle
        have hpowle : r ^ 100 ≤ X := by simpa only [← pow_succ] using hmul
        omega
      have hpi := prefixCount_endpoint_mono130 {p : ℕ | p.Prime} (le_of_lt hdiv)
      simp [hrA, hcut, Nat.sub_eq_zero_of_le hpi]
  · simp [hrA]

/-- Exact logarithmic conversion of the strict prime threshold for alpha=1/100. -/
theorem cofactor_large_iff_pow99_130 {r P : ℕ} (hr : 1 ≤ r) (hP : 0 < P) :
    ((r * P : ℕ) : ℝ) ^ (1 - alpha) < (P : ℝ) ↔ r ^ 99 < P := by
  have hrp : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hPp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hmp : (0 : ℝ) < ((r * P : ℕ) : ℝ) := by positivity
  have hlogpow : Real.log (((r ^ 99 : ℕ) : ℝ)) = 99 * Real.log (r : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogmul : Real.log (((r * P : ℕ) : ℝ)) =
      Real.log (r : ℝ) + Real.log (P : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (ne_of_gt hrp) (ne_of_gt hPp)]
  have hpowpos : (0 : ℝ) < ((r ^ 99 : ℕ) : ℝ) := by positivity
  constructor
  · intro hlarge
    have hh := Real.log_lt_log (Real.rpow_pos_of_pos hmp _) hlarge
    rw [Real.log_rpow hmp, hlogmul] at hh
    have hl : Real.log (((r ^ 99 : ℕ) : ℝ)) < Real.log (P : ℝ) := by
      rw [hlogpow]
      norm_num [alpha] at hh
      linarith
    have hR := (Real.log_lt_log_iff hpowpos hPp).mp hl
    exact_mod_cast hR
  · intro hpow
    have hR : ((r ^ 99 : ℕ) : ℝ) < (P : ℝ) := by exact_mod_cast hpow
    have hh := Real.log_lt_log hpowpos hR
    rw [hlogpow] at hh
    apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hmp _) hPp).mp
    rw [Real.log_rpow hmp, hlogmul]
    norm_num [alpha]
    linarith

/-- Every actual B endpoint is raw-counted, without an eventual qualification. -/
theorem B_subset_rawEndpoints130 : B alpha ⊆ rawEndpoints130 := by
  intro m hm
  have hmA : m ∈ A := hm.1
  have hm1 : 1 < m := by
    have hmge := hmA.1
    by_contra hnot
    have hmeq : m = 1 := by omega
    have hl := hm.2
    simp [LargePrime, largestPrime, hmeq] at hl
  let P : ℕ := largestPrime m
  let r : ℕ := m / P
  have hP : P.Prime := largestPrime_prime hm1
  have hPd : P ∣ m := largestPrime_dvd hm1
  have hrP : r * P = m := Nat.div_mul_cancel hPd
  have hrpos : (0 : ℕ) < r := by
    apply Nat.pos_of_ne_zero
    intro hr0
    have hmzero : m = 0 := by
      simpa only [hr0, zero_mul] using hrP.symm
    omega
  have hrA : r ∈ A := A_divisor_closed hmA ⟨P, hrP.symm⟩
  have hlarge : ((r * P : ℕ) : ℝ) ^ (1 - alpha) < (P : ℝ) := by
    rw [hrP]
    exact hm.2
  exact ⟨r, P, hrA, hP,
    (cofactor_large_iff_pow99_130 (by omega) hP.pos).mp hlarge, hrP.symm⟩

/-- Eventual equality is in the endpoint m, not in the ambient prefix X. -/
theorem rawEndpoints_eventually_B130 (HG : LogQGrowth) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (m ∈ rawEndpoints130 ↔ m ∈ B alpha) := by
  obtain ⟨N, hN⟩ := cofactorInheritance_from_logQGrowth130 HG alpha
    (by norm_num [alpha]) (by norm_num [alpha])
  refine ⟨max N 2, ?_⟩
  intro m hm
  constructor
  · rintro ⟨r, P, hrA, hP, hpow, hmul⟩
    have hlarge := (cofactor_large_iff_pow99_130 hrA.1 hP.pos).mpr hpow
    have hNm : N ≤ r * P := by rw [← hmul]; exact le_trans (le_max_left _ _) hm
    have hmA : m ∈ A := by
      rw [hmul]
      exact (hN r P hNm hP hlarge).mpr hrA
    have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
    have hPmem : P ∈ m.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hP, by rw [hmul]; exact dvd_mul_left P r, by omega⟩
    have hPle : P ≤ largestPrime m := by
      rw [largestPrime_eq_maxPrime (by omega : 1 < m)]
      exact Finset.le_max' _ P hPmem
    have hPleR : (P : ℝ) ≤ (largestPrime m : ℝ) := by exact_mod_cast hPle
    refine ⟨hmA, ?_⟩
    change (m : ℝ) ^ (1 - alpha) < (largestPrime m : ℝ)
    have hlargeM : (m : ℝ) ^ (1 - alpha) < (P : ℝ) := by
      simpa only [← hmul] using hlarge
    exact lt_of_lt_of_le hlargeM hPleR
  · intro hmB
    exact B_subset_rawEndpoints130 hmB

/-- A set confined below N contributes a constant to all prefixes X >= N. -/
theorem prefixCount_stable_below130 {S : Set ℕ} {N X : ℕ}
    (hS : ∀ m ∈ S, m < N) (hX : N ≤ X) : prefixCount S X = prefixCount S N := by
  unfold prefixCount
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hm1, hmX⟩, hmS⟩
    exact ⟨⟨hm1, le_of_lt (hS m hmS)⟩, hmS⟩
  · rintro ⟨⟨hm1, hmN⟩, hmS⟩
    exact ⟨⟨hm1, le_trans hmN hX⟩, hmS⟩

/-- Full corrected count, with the finite correction explicitly constructed
as minus the number of raw endpoints outside B. -/
theorem cofactorIntegerCountCorrected_from_growth130
    (HG : LogQGrowth) : RemainingAnalytic57.BCofactorIntegerCountIdentityCorrected57 := by
  obtain ⟨N, hN⟩ := rawEndpoints_eventually_B130 HG
  let Eset : Set ℕ := rawEndpoints130 \ B alpha
  have hE : ∀ m ∈ Eset, m < N := by
    intro m hm
    by_contra hh
    exact hm.2 ((hN m (by omega)).mp hm.1)
  refine ⟨max N 1, -(prefixCount Eset N : ℤ), ?_⟩
  intro X hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hstable := prefixCount_stable_below130 hE hXN
  have hinter : B alpha ∩ rawEndpoints130 = B alpha :=
    Set.inter_eq_left.mpr B_subset_rawEndpoints130
  have hpart := prefixCount_partition (B alpha) rawEndpoints130 X
  rw [hinter] at hpart
  change prefixCount (B alpha) X + prefixCount Eset X = prefixCount rawEndpoints130 X at hpart
  rw [hstable] at hpart
  have hpartZ : (prefixCount (B alpha) X : ℤ) + (prefixCount Eset N : ℤ) =
      (prefixCount rawEndpoints130 X : ℤ) := by exact_mod_cast hpart
  rw [rawEndpointCount_integer130 hX1] at hpartZ
  linarith only [hpartZ]

/-- The exact corrected cofactor count is no longer an independent field. -/
theorem cofactorIntegerCountCorrected_from_theta130
    (HT : ThetaLogSqRemainder127) : RemainingAnalytic57.BCofactorIntegerCountIdentityCorrected57 :=
  cofactorIntegerCountCorrected_from_growth130 (logQGrowth_from_theta130 HT)

/-- Repair 133: keep the set abstract while constructing the finite witness.
This avoids synthesizing competing DecidablePred instances for a set difference. -/
theorem prefixCount_pos_of_member133 {S : Set ℕ} {m X : ℕ}
    (hm1 : 1 ≤ m) (hmX : m ≤ X) (hmS : m ∈ S) :
    0 < prefixCount S X := by
  classical
  unfold prefixCount
  apply Finset.card_pos.mpr
  exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmX⟩, hmS⟩⟩

/-- The old E=0 count cannot be an input to an unconditional proof: the raw
prefix strictly contains B at every X >= 2, because it always contains 2. -/
theorem not_legacy_exact_cofactor_count130 :
    ¬ RemainingAnalytic46.BCofactorIntegerCountIdentity46 := by
  classical
  rintro ⟨N, hN⟩
  let X : ℕ := max N 2
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXN : N ≤ X := le_max_left _ _
  have hraw2 : 2 ∈ rawEndpoints130 :=
    ⟨1, 2, one_mem_A130, Nat.prime_two, by norm_num, by norm_num⟩
  have hnotB2 : 2 ∉ B alpha := fun hh => two_not_mem_A130 hh.1
  have hgap : 0 < prefixCount (rawEndpoints130 \ B alpha) X :=
    prefixCount_pos_of_member133 (by norm_num) hX2 ⟨hraw2, hnotB2⟩
  have hinter : B alpha ∩ rawEndpoints130 = B alpha :=
    Set.inter_eq_left.mpr B_subset_rawEndpoints130
  have hpart := prefixCount_partition (B alpha) rawEndpoints130 X
  rw [hinter] at hpart
  have heqZ : (prefixCount (B alpha) X : ℤ) = (prefixCount rawEndpoints130 X : ℤ) :=
    (hN X hXN).trans (rawEndpointCount_integer130 (by omega : 1 ≤ X)).symm
  have heq : prefixCount (B alpha) X = prefixCount rawEndpoints130 X := by
    exact_mod_cast heqZ
  omega

/-- Regression test only.  The former record is uninhabited because it asks
for the false uncorrected prefix identity.  It is never used to prove the
candidate main statement: the corrected construction below is independent. -/
theorem legacy_endgame_uninhabited130 : ¬ Nonempty EverythingLeftClassical127 := by
  rintro ⟨H⟩
  exact not_legacy_exact_cofactor_count130 H.cofactor_integer_count


/-! ### F2. Quantitative theta also implies the relative prime number theorem

This removes a further redundant external input.  Split prime counts at
n^(1-eta): the small-prime part is at most n^(1-eta), and every remaining
prime contributes at least (1-eta) log n to theta(n).
-/

theorem thetaPrefix_eq_primeSum130 (n : ℕ) :
    thetaPrefix127 n =
      ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime), Real.log (p : ℝ) := by
  rw [Finset.sum_filter]
  rfl

/-- Elementary lower estimate for pi(n): theta(n) <= pi(n) log n. -/
theorem theta_le_primeCount_log130 {n : ℕ} (hn : 2 ≤ n) :
    thetaPrefix127 n ≤ (prefixCount {p : ℕ | p.Prime} n : ℝ) * Real.log (n : ℝ) := by
  rw [thetaPrefix_eq_primeSum130]
  have hh :
      (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime), Real.log (p : ℝ)) ≤
        ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime), Real.log (n : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    have hf := Finset.mem_filter.mp hp
    exact Real.log_le_log (by exact_mod_cast hf.2.pos)
      (by exact_mod_cast (Finset.mem_Icc.mp hf.1).2)
  simpa only [Finset.sum_const, nsmul_eq_mul, prefixCount,
    Set.mem_setOf_eq] using hh

/-- Elementary upper estimate for pi(n), obtained by splitting at n^beta. -/
theorem primeCount_log_split130 {n : ℕ} {β : ℝ}
    (hn : 2 ≤ n) (hβ : 0 < β) :
    (prefixCount {p : ℕ | p.Prime} n : ℝ) * (β * Real.log (n : ℝ)) ≤
      thetaPrefix127 n + (n : ℝ) ^ β * (β * Real.log (n : ℝ)) := by
  classical
  let T : Finset ℕ := (Finset.Icc 1 n).filter (fun p : ℕ => p.Prime)
  let U : ℝ := (n : ℝ) ^ β
  let S : Finset ℕ := T.filter (fun p : ℕ => (p : ℝ) ≤ U)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hUpos : 0 < U := Real.rpow_pos_of_pos hnpos _
  have hSsub : S ⊆ Finset.Icc 1 ⌊U⌋₊ := by
    intro p hp
    have hs := Finset.mem_filter.mp hp
    have ht := Finset.mem_filter.mp hs.1
    have hpi := Finset.mem_Icc.mp ht.1
    exact Finset.mem_Icc.mpr ⟨hpi.1, (Nat.le_floor_iff hUpos.le).mpr hs.2⟩
  have hSleNat : S.card ≤ ⌊U⌋₊ := by
    simpa using Finset.card_le_card hSsub
  have hSle : (S.card : ℝ) ≤ U :=
    le_trans (by exact_mod_cast hSleNat) (Nat.floor_le hUpos.le)
  have hpoint : ∀ p ∈ T, β * Real.log (n : ℝ) ≤
      Real.log (p : ℝ) + (if (p : ℝ) ≤ U then β * Real.log (n : ℝ) else 0) := by
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hpLog : 0 ≤ Real.log (p : ℝ) :=
      (Real.log_pos (by exact_mod_cast hpPrime.one_lt)).le
    by_cases hsmall : (p : ℝ) ≤ U
    · simp only [hsmall, ite_true]
      linarith only [hpLog]
    · have hUp : U ≤ (p : ℝ) := le_of_lt (lt_of_not_ge hsmall)
      have hlogs := Real.log_le_log hUpos hUp
      change Real.log ((n : ℝ) ^ β) ≤ Real.log (p : ℝ) at hlogs
      rw [Real.log_rpow hnpos] at hlogs
      simpa only [hsmall, ite_false, add_zero] using hlogs
  have hsum := Finset.sum_le_sum hpoint
  have hselected :
      (∑ p ∈ T, if (p : ℝ) ≤ U then β * Real.log (n : ℝ) else 0) =
        (S.card : ℝ) * (β * Real.log (n : ℝ)) := by
    rw [← Finset.sum_filter]
    simp only [S, Finset.sum_const, nsmul_eq_mul]
  have htheta : (∑ p ∈ T, Real.log (p : ℝ)) = thetaPrefix127 n :=
    (thetaPrefix_eq_primeSum130 n).symm
  rw [Finset.sum_add_distrib, hselected, htheta] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hsmallMass := mul_le_mul_of_nonneg_right hSle (mul_pos hβ hL).le
  have hcount : prefixCount {p : ℕ | p.Prime} n = T.card := by
    simp only [prefixCount, Set.mem_setOf_eq, T]
  rw [hcount]
  change (T.card : ℝ) * (β * Real.log (n : ℝ)) ≤
    thetaPrefix127 n + U * (β * Real.log (n : ℝ))
  linarith only [hsum, hsmallMass]

/-- Relative PNT is derived from the quantitative theta input, rather than
being left as a second independent analytic assumption. -/
theorem primeCountRelativePNT_from_theta130
    (HT : ThetaLogSqRemainder127) : PrimeCountRelativePNT123 := by
  intro ρ hρ
  let η : ℝ := min (ρ / 8) (1 / 4)
  let β : ℝ := 1 - η
  have hηpos : 0 < η := lt_min (by positivity) (by norm_num)
  have hηρ : η ≤ ρ / 8 := min_le_left _ _
  have hηquarter : η ≤ (1 : ℝ) / 4 := min_le_right _ _
  have hβhalf : (1 : ℝ) / 2 ≤ β := by dsimp [β]; linarith
  have hβpos : 0 < β := by linarith
  have hηρ' : η ≤ ρ := by linarith
  obtain ⟨NT, hNT⟩ := theta_relative_error130 HT hηpos
  obtain ⟨NS, hNS⟩ := scaled_log_le_rpow130 hηpos (2 / ρ) (by positivity)
  refine ⟨max 2 (max NT NS), le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnrest : max NT NS ≤ n := le_trans (le_max_right _ _) hn
  have hnT : NT ≤ n := le_trans (le_max_left _ _) hnrest
  have hnS : NS ≤ n := le_trans (le_max_right _ _) hnrest
  have hnp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hUpos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnp _
  have hcut0 := mul_le_mul_of_nonneg_right (hNS n hnS) hUpos.le
  have hprod : (n : ℝ) ^ η * (n : ℝ) ^ β = (n : ℝ) := by
    rw [← Real.rpow_add hnp]
    have hsum : η + β = 1 := by dsimp [β]; ring
    rw [hsum, Real.rpow_one]
  rw [hprod] at hcut0
  have hcut1 := mul_le_mul_of_nonneg_right hcut0 (show 0 ≤ ρ / 2 by linarith)
  have hcancel :
      ((2 / ρ) * Real.log (n : ℝ) * (n : ℝ) ^ β) * (ρ / 2) =
        (n : ℝ) ^ β * Real.log (n : ℝ) := by
    field_simp [ne_of_gt hρ] <;> ring
  rw [hcancel] at hcut1
  have hcut : (n : ℝ) ^ β * Real.log (n : ℝ) ≤ (ρ / 2) * (n : ℝ) := by
    nlinarith only [hcut1]
  have hTheta := abs_le.mp (hNT n hnT)
  have hLower := theta_le_primeCount_log130 hn2
  have hUpper := primeCount_log_split130 hn2 hβpos
  have hLowRaw : (1 - ρ) * (n : ℝ) ≤
      (prefixCount {p : ℕ | p.Prime} n : ℝ) * Real.log (n : ℝ) := by
    have hηn := mul_le_mul_of_nonneg_right hηρ' hnp.le
    nlinarith only [hTheta.1, hLower, hηn]
  have hCoeff : 2 * η ≤ β * ρ / 2 := by
    have hh := mul_le_mul_of_nonneg_right hβhalf (show 0 ≤ ρ / 2 by linarith)
    nlinarith only [hηρ, hh]
  have hCoeffN := mul_le_mul_of_nonneg_right hCoeff hnp.le
  have hCutβ := mul_le_mul_of_nonneg_left hcut hβpos.le
  have hβn : β * (n : ℝ) + η * (n : ℝ) = (n : ℝ) := by dsimp [β]; ring
  have hHighScaled :
      β * ((prefixCount {p : ℕ | p.Prime} n : ℝ) * Real.log (n : ℝ)) ≤
        β * ((1 + ρ) * (n : ℝ)) := by
    nlinarith only [hUpper, hTheta.2, hCoeffN, hCutβ, hβn]
  have hHighRaw : (prefixCount {p : ℕ | p.Prime} n : ℝ) * Real.log (n : ℝ) ≤
      (1 + ρ) * (n : ℝ) := le_of_mul_le_mul_left hHighScaled hβpos
  have hlow := (div_le_iff₀ hL).mpr hLowRaw
  have hhigh := (le_div_iff₀ hL).mpr hHighRaw
  have hidLow : ((1 - ρ) * (n : ℝ)) / Real.log (n : ℝ) =
      (n : ℝ) / Real.log (n : ℝ) - ρ * ((n : ℝ) / Real.log (n : ℝ)) := by ring
  have hidHigh : ((1 + ρ) * (n : ℝ)) / Real.log (n : ℝ) =
      (n : ℝ) / Real.log (n : ℝ) + ρ * ((n : ℝ) / Real.log (n : ℝ)) := by ring
  rw [hidLow] at hlow
  rw [hidHigh] at hhigh
  exact abs_le.mpr ⟨by linarith only [hlow], by linarith only [hhigh]⟩

/-- All the PNT-package uses are consequences of this single theta input. -/
def pntPackage_from_theta130 (HT : ThetaLogSqRemainder127) : RemainingAnalytic21.PNTPackage :=
  pntPackage_from_relative_theta130 (primeCountRelativePNT_from_theta130 HT) HT

/-! ### G. Rebuild the main proof directly from the surviving analytic inputs

No conversion to EverythingLeftClassical127/126 is used here.  Those old
records include the false uncorrected cofactor identity.  In particular the
audit theorem above is NOT used to obtain MainStatement by contradiction.

The following seven inputs remain unconstructed in this file:
  * finite-condition density limit for A;
  * uniform omitted tail for A;
  * quantitative log-squared theta remainder;
  * sparse valuation-one prime count;
  * density-zero set of bad short prime intervals;
  * additive large sieve;
  * large-modulus linear-product Weil bound.

The bare scalar kernel, cofactor inheritance, corrected cofactor count,
relative PNT, prime-count decay, factorial growth, and the four/five finite enumerations
are now supplied by proof scripts.  Compilation of this new section still
needs to be checked; no unconditional theorem is claimed.
-/

structure EverythingLeftCorrected130 where
  A_density_limit : Remaining_AFiniteDensityLimit47
  A_uniform_tail : Remaining_AUniformTail47
  theta_logsq_remainder : ThetaLogSqRemainder127
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  large_sieve : RemainingAnalytic92.ClassicalPrimeAdditiveLargeSieve92
  large_modulus_weil : LargeModulusLinearProductWeil127

/-- Direct construction of the compact core.  This avoids all historical
endgame records containing the obsolete exact-prefix counting hypothesis. -/
noncomputable def EverythingLeftCorrected130.toCore18
    (H : EverythingLeftCorrected130) : AnalyticCore18 := by
  let hApprox := A_approximation_of_limit_tail H.A_density_limit H.A_uniform_tail
  have hAdensity : HasDensity A hApprox.delta := A_density_of_approximation hApprox
  have hPNT : PrimeCountRelativePNT123 := primeCountRelativePNT_from_theta130 H.theta_logsq_remainder
  have hLogQ : LogQGrowth := logQGrowth_from_theta130 H.theta_logsq_remainder
  have hGrowth : Tasks.FactorialClassGrowth := factorial_growth_of_log_q hLogQ
  have hB : HasDensity (B alpha) (densityConstant hApprox.delta) :=
    bDensity_from_corrected_count130 H.A_density_limit H.A_uniform_tail
      hPNT bareCofactorMassLimit_proved130
      (cofactorIntegerCountCorrected_from_growth130 hLogQ) hAdensity
  have hDenseTheta := denseTopThetaMass_from_thetaRemainder127 H.theta_logsq_remainder
  have hDense := denseBranch_from_topIntervalMass
    (denseTopIntervalPrimeMass_from_logMass115
      (denseTopLogPrimeMass_from_theta119 hDenseTheta))
  have hSparse := sparseWeightedTransfer_from_count127 H.sparse_good_prime_count
  have hAnchorCore := prop51AnalyticCore_from_theta127
    H.theta_logsq_remainder H.large_sieve H.large_modulus_weil
  exact {
    deltaA := hApprox.delta
    deltaA_pos := hApprox.delta_pos
    A_density := hAdensity
    B_density := hB
    prime_zero := prime_zero_of_count_decay
      (primeCountDecay_from_relative130 hPNT)
    short_second := harman_to_secondLargest_proved
      (harman_from_bad_density127 H.harman_bad_density)
    factorial_growth := hGrowth
    interval_comparison := RemainingAnalytic44.intervalComparison_from_hardened
      hDense hSparse hGrowth
    uniform_anchor := RemainingAnalytic58.uniformAnchorSieve_from_analyticCore58
      hGrowth hAnchorCore
  }

/-- A repaired conditional theorem, NOT an unconditional proof. -/
theorem candidate_main_from_corrected_endgame130
    (H : EverythingLeftCorrected130) : MainStatement :=
  candidate_main_from_analytic_core18 H.toCore18

/-- A repaired conditional positive-density theorem, with every remaining
analytic input visible in the argument H. -/
theorem positive_lower_density_from_corrected_endgame130
    (H : EverythingLeftCorrected130) : PositiveLowerDensity D6 :=
  positive_lower_density_from_analytic_core18 H.toCore18

/-! ### H. Focused compilation and dependency checkpoints -/

-- Historical audit output (142): #print axioms primeCountDecay_from_relative130
-- Historical audit output (142): #print axioms topHalfPrimes_subset_oddFactorial130
-- Historical audit output (142): #print axioms topHalfPrimeProduct_dvd_q130
-- Historical audit output (142): #print axioms theta_topHalf_le_log_q130
-- Historical audit output (142): #print axioms theta_relative_error130
-- Historical audit output (142): #print axioms logQGrowth_from_theta130
-- Historical audit output (142): #print axioms pntPackage_from_relative_theta130
-- Historical audit output (142): #print axioms one_mem_A130
-- Historical audit output (142): #print axioms q_two130
-- Historical audit output (142): #print axioms two_not_mem_A130
-- Historical audit output (142): #print axioms raw_pair_two130
-- Historical audit output (142): #print axioms not_legacy_prefix_bijection130
-- Historical audit output (142): #print axioms bDensity_from_corrected_decomposition130
-- Historical audit output (142): #print axioms cofactorMain_from_relative_bare130
-- Historical audit output (142): #print axioms bDensity_from_corrected_count130
-- Historical audit output (142): #print axioms scaled_log_le_rpow130
-- Historical audit output (142): #print axioms cofactor_lt_dominant_prime130
-- Historical audit output (142): #print axioms mem_A_mul_prime_of_growth130
-- Historical audit output (142): #print axioms cofactorInheritance_from_logQGrowth130
-- Historical audit output (142): #print axioms cofactorInheritance_from_theta130
-- Historical audit output (142): #print axioms integral_prefix_mono130
-- Historical audit output (142): #print axioms sum_floor_integral_squeeze130
-- Historical audit output (142): #print axioms kernel_ratio_lower130
-- Historical audit output (142): #print axioms rawKernel_regular130
-- Historical audit output (142): #print axioms rawKernel_hasPrimitive130
-- Historical audit output (142): #print axioms rawKernel_integral130
-- Historical audit output (142): #print axioms kernel_scale_eventually130
-- Historical audit output (142): #print axioms bareRow_eq_floor_sum130
-- Historical audit output (142): #print axioms bareKernel_error_bound130
-- Historical audit output (142): #print axioms bareCofactorMassLimit_proved130
-- Historical audit output (142): #print axioms densityCofactorKernel_proved130
-- Historical audit output (142): #print axioms self_le_pow99_130
-- Historical audit output (142): #print axioms dominant_pair_unique130
-- Historical audit output (142): #print axioms mem_rawPairs130
-- Historical audit output (142): #print axioms rawPairs_image130
-- Historical audit output (142): #print axioms rawPairs_injective130
-- Historical audit output (142): #print axioms rawEndpointCount_eq_pairCount130
-- Historical audit output (142): #print axioms prefixCount_endpoint_mono130
-- Historical audit output (142): #print axioms cofactor_cutoff_iff_pow130
-- Historical audit output (142): #print axioms rawEndpointCount_integer130
-- Historical audit output (142): #print axioms cofactor_large_iff_pow99_130
-- Historical audit output (142): #print axioms B_subset_rawEndpoints130
-- Historical audit output (142): #print axioms rawEndpoints_eventually_B130
-- Historical audit output (142): #print axioms prefixCount_stable_below130
-- Historical audit output (142): #print axioms cofactorIntegerCountCorrected_from_growth130
-- Historical audit output (142): #print axioms cofactorIntegerCountCorrected_from_theta130
-- Historical audit output (142): #print axioms not_legacy_exact_cofactor_count130
-- Historical audit output (142): #print axioms legacy_endgame_uninhabited130
-- Historical audit output (142): #print axioms thetaPrefix_eq_primeSum130
-- Historical audit output (142): #print axioms theta_le_primeCount_log130
-- Historical audit output (142): #print axioms primeCount_log_split130
-- Historical audit output (142): #print axioms primeCountRelativePNT_from_theta130
-- Historical audit output (142): #print axioms pntPackage_from_theta130
-- Historical audit output (142): #print axioms EverythingLeftCorrected130.toCore18
-- Historical audit output (142): #print axioms candidate_main_from_corrected_endgame130
-- Historical audit output (142): #print axioms positive_lower_density_from_corrected_endgame130

-- The first two theorems below have no project-specific assumptions.
-- Historical audit output (142): #check bareCofactorMassLimit_proved130
-- Historical audit output (142): #check densityCofactorKernel_proved130
-- The final theorem still explicitly requires the seven unconstructed inputs.
-- Historical audit output (142): #check candidate_main_from_corrected_endgame130
-- Historical audit output (142): #check positive_lower_density_from_corrected_endgame130
-- Historical audit output (142): #print EverythingLeftCorrected130

end RemainingAnalytic130


/-! ## 131. Uniform omitted-gcd tail from the quantitative theta input

This section does not add a new analytic assumption. It constructs
`RemainingAnalytic21.AUniformTail` from `ThetaLogSqRemainder127`.
The proof uses a uniform finite-prefix divisor cover, a powerset bound for
squarefree divisors, and an exponentially summable envelope.

Verification: new proof scripts; not compiled in the preparation environment.
The positive finite-density limit for A is still a separate obligation.
-/
namespace RemainingAnalytic131

open scoped BigOperators
open Filter
open RemainingAnalytic20 RemainingAnalytic47 RemainingAnalytic127
open RemainingAnalytic130

/-! ### A. Finite-prefix covering estimates, with explicit index types -/

/-- A finite collection of points uses only finitely many witnesses, even
when the available covering family is indexed by all natural numbers. -/
theorem finite_index_cover131 (s : Finset ℕ) (T : ℕ → Set ℕ) (B : ℕ)
    (H : ∀ m ∈ s, ∃ k : ℕ, B ≤ k ∧ m ∈ T k) :
    ∃ W : Finset ℕ, (∀ k ∈ W, B ≤ k) ∧
      ∀ m ∈ s, ∃ k ∈ W, m ∈ T k := by
  classical
  revert H
  induction s using Finset.induction_on with
  | empty =>
      intro H
      refine ⟨∅, ?_, ?_⟩ <;> simp
  | @insert m s hms ih =>
      intro H
      obtain ⟨k, hBk, hmk⟩ := H m (Finset.mem_insert_self m s)
      obtain ⟨W, hBW, hW⟩ := ih (fun n hn => H n (Finset.mem_insert_of_mem hn))
      refine ⟨insert k W, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hj | hj
        · simpa only [hj] using hBk
        · exact hBW j hj
      · intro n hn
        rcases Finset.mem_insert.mp hn with hn | hn
        · subst n
          exact ⟨k, Finset.mem_insert_self k W, hmk⟩
        · obtain ⟨j, hj, hnj⟩ := hW n hn
          exact ⟨j, Finset.mem_insert_of_mem hj, hnj⟩

/-- Real-valued union bound on a fixed natural-number prefix. No density
assumption and no countable-union interchange is used. -/
theorem prefixCount_real_le_sum_of_cover131
    (S : Set ℕ) (T : ℕ → Set ℕ) (W : Finset ℕ) (X : ℕ)
    (H : ∀ m : ℕ, 1 ≤ m → m ≤ X → m ∈ S → ∃ k ∈ W, m ∈ T k) :
    (prefixCount S X : ℝ) ≤ ∑ k ∈ W, (prefixCount (T k) X : ℝ) := by
  classical
  rw [prefixCount_eq_indicator_sum127]
  have hpoint : ∀ m ∈ Finset.Icc 1 X,
      (if m ∈ S then (1 : ℝ) else 0) ≤
        ∑ k ∈ W, (if m ∈ T k then (1 : ℝ) else 0) := by
    intro m hm
    have hmI := Finset.mem_Icc.mp hm
    by_cases hmS : m ∈ S
    · obtain ⟨k, hk, hmk⟩ := H m hmI.1 hmI.2 hmS
      rw [if_pos hmS]
      calc
        (1 : ℝ) = (if m ∈ T k then (1 : ℝ) else 0) := by rw [if_pos hmk]
        _ ≤ ∑ j ∈ W, (if m ∈ T j then (1 : ℝ) else 0) := by
          have hnonneg : ∀ j ∈ W,
              (0 : ℝ) ≤ (if m ∈ T j then (1 : ℝ) else 0) := by
            intro j hj
            by_cases hmj : m ∈ T j <;> simp only [hmj, ite_true, ite_false] <;> norm_num
          exact Finset.single_le_sum
            (f := fun j : ℕ => if m ∈ T j then (1 : ℝ) else 0) hnonneg hk
    · rw [if_neg hmS]
      exact Finset.sum_nonneg (fun k hk => by split_ifs <;> norm_num)
  calc
    (∑ m ∈ Finset.Icc 1 X, if m ∈ S then (1 : ℝ) else 0) ≤
        ∑ m ∈ Finset.Icc 1 X, ∑ k ∈ W,
          (if m ∈ T k then (1 : ℝ) else 0) := Finset.sum_le_sum hpoint
    _ = ∑ k ∈ W, (prefixCount (T k) X : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact (prefixCount_eq_indicator_sum127 (T k) X).symm

/-- Multiples of d in [1,X] inject into [1,floor(X/d)] by division. -/
theorem prefixCount_multiples_le_natDiv131 (d X : ℕ) (hd : 1 ≤ d) :
    prefixCount {m : ℕ | d ∣ m} X ≤ X / d := by
  classical
  let s : Finset ℕ := (Finset.Icc 1 X).filter (fun m : ℕ => d ∣ m)
  have hdata : ∀ m ∈ s, 1 ≤ m ∧ m ≤ X ∧ d ∣ m := by
    intro m hm
    have h := Finset.mem_filter.mp hm
    have hi := Finset.mem_Icc.mp h.1
    exact ⟨hi.1, hi.2, h.2⟩
  have hinj : Set.InjOn (fun m : ℕ => m / d) s := by
    intro m hm n hn hmn
    have hmd := (hdata m hm).2.2
    have hnd := (hdata n hn).2.2
    change m / d = n / d at hmn
    calc
      m = (m / d) * d := (Nat.div_mul_cancel hmd).symm
      _ = (n / d) * d := by rw [hmn]
      _ = n := Nat.div_mul_cancel hnd
  have hsub : s.image (fun m : ℕ => m / d) ⊆ Finset.Icc 1 (X / d) := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    have h := hdata m hm
    have hkpos : 0 < m / d := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hmzero : m = 0 := by
        simpa only [hz, zero_mul] using (Nat.div_mul_cancel h.2.2).symm
      omega
    have hquot : m / d ≤ X / d := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr
      exact le_trans (Nat.div_mul_le_self m d) h.2.1
    exact Finset.mem_Icc.mpr ⟨by omega, hquot⟩
  have heq : prefixCount {m : ℕ | d ∣ m} X = s.card := by
    simp only [prefixCount, Set.mem_setOf_eq, s]
  rw [heq]
  calc
    s.card = (s.image (fun m : ℕ => m / d)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Icc 1 (X / d)).card := Finset.card_le_card hsub
    _ = X / d := by simp

/-! ### B. The single-gcd-condition estimate -/

/-- The set excluded by the gcd condition associated with a fixed integer Q. -/
def gcdBadSet131 (Q : ℕ) : Set ℕ := {m : ℕ | Q < (Nat.gcd m Q) ^ 2}

/-- Only divisors exceeding sqrt(Q) can witness a failed gcd condition. -/
def largeDivisors131 (Q : ℕ) : Finset ℕ :=
  Q.divisors.filter (fun d : ℕ => Q < d ^ 2)

/-- The gcd itself supplies a divisor in the finite cover. -/
theorem gcdBadSet_divisor_cover131 {Q m : ℕ} (hQ : 0 < Q)
    (hm : m ∈ gcdBadSet131 Q) :
    ∃ d ∈ largeDivisors131 Q, d ∣ m := by
  refine ⟨Nat.gcd m Q, ?_, Nat.gcd_dvd_left m Q⟩
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right m Q, ne_of_gt hQ⟩, hm⟩

/-- Uniform counting bound. This estimate is valid for every positive Q,
not just for squarefree Q, and for every prefix endpoint X. -/
theorem gcdBad_count_le_divisor_envelope131 {Q : ℕ} (hQ : 0 < Q) (X : ℕ) :
    (prefixCount (gcdBadSet131 Q) X : ℝ) ≤
      (X : ℝ) * ((Q.divisors.card : ℝ) / Real.sqrt (Q : ℝ)) := by
  classical
  let D : Finset ℕ := largeDivisors131 Q
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hspos : 0 < Real.sqrt (Q : ℝ) := Real.sqrt_pos.mpr hQpos
  have hsquare : (Real.sqrt (Q : ℝ)) ^ 2 = (Q : ℝ) := Real.sq_sqrt hQpos.le
  have hdpos : ∀ d ∈ D, 1 ≤ d := by
    intro d hd
    have hdD := (Finset.mem_filter.mp hd).1
    have hp : 0 < d := Nat.pos_of_mem_divisors hdD
    omega
  have hsle : ∀ d ∈ D, Real.sqrt (Q : ℝ) ≤ (d : ℝ) := by
    intro d hd
    have hbound : (Q : ℝ) < (d : ℝ) ^ 2 := by
      exact_mod_cast (Finset.mem_filter.mp hd).2
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    nlinarith only [hsquare, hbound, hd0, hspos]
  have hcover := prefixCount_real_le_sum_of_cover131 (gcdBadSet131 Q)
    (fun d : ℕ => {m : ℕ | d ∣ m}) D X
    (fun m hm1 hmX hm => gcdBadSet_divisor_cover131 hQ hm)
  have hcard : (D.card : ℝ) ≤ (Q.divisors.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset
      (fun d : ℕ => Q < d ^ 2) Q.divisors))
  calc
    (prefixCount (gcdBadSet131 Q) X : ℝ)
        ≤ ∑ d ∈ D, (prefixCount {m : ℕ | d ∣ m} X : ℝ) := hcover
    _ ≤ ∑ d ∈ D, ((X / d : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast prefixCount_multiples_le_natDiv131 d X (hdpos d hd)
    _ ≤ ∑ d ∈ D, (X : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact RemainingAnalytic52.natDivCastLeRealDiv_proved52 X d (hdpos d hd)
    _ ≤ ∑ d ∈ D, (X : ℝ) / Real.sqrt (Q : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_left (by positivity) hspos (hsle d hd)
    _ = (D.card : ℝ) * ((X : ℝ) / Real.sqrt (Q : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q.divisors.card : ℝ) * ((X : ℝ) / Real.sqrt (Q : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (X : ℝ) * ((Q.divisors.card : ℝ) / Real.sqrt (Q : ℝ)) := by ring

/-- Division by the prefix length introduces no endpoint error. X=0 is
handled separately using the source's totalized proportion. -/
theorem gcdBad_proportion_le_divisor_envelope131 {Q : ℕ} (hQ : 0 < Q) (X : ℕ) :
    proportion (gcdBadSet131 Q) X ≤
      (Q.divisors.card : ℝ) / Real.sqrt (Q : ℝ) := by
  by_cases hX : X = 0
  · subst X
    simp only [proportion, Nat.cast_zero, div_zero]
    positivity
  · have hXp : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hX
    unfold proportion
    apply (div_le_iff₀ hXp).mpr
    simpa only [mul_comm] using gcdBad_count_le_divisor_envelope131 hQ X

/-! ### C. Squarefree divisor counts and exponential decay -/

/-- A squarefree divisor is determined by a subset of the ambient prime
factors. The powerset cardinality yields the needed bound without a tau API. -/
theorem squarefree_divisor_card_le_pow131 {Q : ℕ} (hQ : Squarefree Q) :
    Q.divisors.card ≤ 2 ^ Q.primeFactors.card := by
  classical
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hcover : Q.divisors ⊆
      Q.primeFactors.powerset.image (fun s : Finset ℕ => ∏ p ∈ s, p) := by
    intro d hd
    have hdQ : d ∣ Q := (Nat.mem_divisors.mp hd).1
    have hdSF : Squarefree d := by
      intro x hxx
      exact hQ x (dvd_trans hxx hdQ)
    have hsub : d.primeFactors ⊆ Q.primeFactors := by
      intro p hp
      have h := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primeFactors.mpr ⟨h.1, dvd_trans h.2.1 hdQ, hQ0⟩
    exact Finset.mem_image.mpr
      ⟨d.primeFactors, Finset.mem_powerset.mpr hsub,
        Nat.prod_primeFactors_of_squarefree hdSF⟩
  calc
    Q.divisors.card ≤
        (Q.primeFactors.powerset.image (fun s : Finset ℕ => ∏ p ∈ s, p)).card :=
      Finset.card_le_card hcover
    _ ≤ Q.primeFactors.powerset.card := Finset.card_image_le
    _ = 2 ^ Q.primeFactors.card := Finset.card_powerset _

/-- Every prime factor of q(a) lies at most a. -/
theorem q_primeFactor_card_le_primeCount131 (a : ℕ) :
    (q a).primeFactors.card ≤ prefixCount {p : ℕ | p.Prime} a := by
  classical
  have hsub : (q a).primeFactors ⊆
      (Finset.Icc 1 a).filter (fun p : ℕ => p.Prime) := by
    intro p hp
    have h := Nat.mem_primeFactors.mp hp
    have hpa := RemainingAnalytic65.primeDivisorQLe_proved65 a p h.1 h.2.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by have := h.1.two_le; omega, hpa⟩, h.1⟩
  simpa only [prefixCount, Set.mem_setOf_eq] using Finset.card_le_card hsub

/-- The divisor count in the actual factorial squareclass is bounded by 2^pi(a). -/
theorem q_divisor_card_le_primeCount_pow131 (a : ℕ) :
    (q a).divisors.card ≤ 2 ^ prefixCount {p : ℕ | p.Prime} a := by
  exact le_trans (squarefree_divisor_card_le_pow131 (q_squarefree a))
    (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
      (q_primeFactor_card_le_primeCount131 a))

noncomputable def qTailWeight131 (a : ℕ) : ℝ :=
  ((q a).divisors.card : ℝ) / Real.sqrt (q a : ℝ)

noncomputable def expTail131 (a : ℕ) : ℝ := Real.exp (-(a : ℝ) / 8)

/-- The specific theta input supplies both ingredients of an exponential
bound: log q(a) >= a/3 and pi(a) log 2 <= a/24. -/
theorem qTailWeight_eventually_le_exp131 (HT : ThetaLogSqRemainder127) :
    ∃ N : ℕ, ∀ a : ℕ, N ≤ a → qTailWeight131 a ≤ expTail131 a := by
  obtain ⟨NQ, hNQ⟩ := logQGrowth_from_theta130 HT
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have heps : 0 < 1 / (24 * Real.log (2 : ℝ)) := by positivity
  obtain ⟨NP, hNP⟩ := primeCountDecay_from_relative130
    (primeCountRelativePNT_from_theta130 HT) (1 / (24 * Real.log (2 : ℝ))) heps
  refine ⟨max NQ NP, ?_⟩
  intro a ha
  have haQ : NQ ≤ a := le_trans (le_max_left _ _) ha
  have haP : NP ≤ a := le_trans (le_max_right _ _) ha
  have hpi := hNP a haP
  have hpimul := mul_lt_mul_of_pos_right hpi hlog2
  have hcancel : (1 / (24 * Real.log (2 : ℝ)) * (a : ℝ)) * Real.log (2 : ℝ) =
      (a : ℝ) / 24 := by
    field_simp [ne_of_gt hlog2] <;> ring
  rw [hcancel] at hpimul
  have htauPow : ((q a).divisors.card : ℝ) ≤
      (2 : ℝ) ^ prefixCount {p : ℕ | p.Prime} a := by
    exact_mod_cast q_divisor_card_le_primeCount_pow131 a
  have hpowExp : (2 : ℝ) ^ prefixCount {p : ℕ | p.Prime} a =
      Real.exp ((prefixCount {p : ℕ | p.Prime} a : ℝ) * Real.log (2 : ℝ)) := by
    rw [← Real.log_pow]
    exact (Real.exp_log (by positivity)).symm
  have htau : ((q a).divisors.card : ℝ) ≤ Real.exp ((a : ℝ) / 24) := by
    rw [hpowExp] at htauPow
    exact le_trans htauPow (Real.exp_le_exp.mpr hpimul.le)
  have hqpos : (0 : ℝ) < (q a : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (q_ne_zero a)
  have hqexp : Real.exp ((a : ℝ) / 3) ≤ (q a : ℝ) := by
    have hh := Real.exp_le_exp.mpr (hNQ a haQ)
    simpa only [Real.exp_log hqpos] using hh
  have hsquare : (Real.sqrt (q a : ℝ)) ^ 2 = (q a : ℝ) := Real.sq_sqrt hqpos.le
  have hexpsquare : (Real.exp ((a : ℝ) / 6)) ^ 2 = Real.exp ((a : ℝ) / 3) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.exp ((a : ℝ) / 6) ≤ Real.sqrt (q a : ℝ) := by
    have hs0 := Real.sqrt_nonneg (q a : ℝ)
    have he0 := Real.exp_pos ((a : ℝ) / 6)
    nlinarith only [hsquare, hexpsquare, hqexp, hs0, he0]
  unfold qTailWeight131 expTail131
  calc
    ((q a).divisors.card : ℝ) / Real.sqrt (q a : ℝ) ≤
        Real.exp ((a : ℝ) / 24) / Real.sqrt (q a : ℝ) :=
      div_le_div_of_nonneg_right htau (Real.sqrt_nonneg _)
    _ ≤ Real.exp ((a : ℝ) / 24) / Real.exp ((a : ℝ) / 6) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hsqrt
    _ = Real.exp (-(a : ℝ) / 8) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- A one-condition exclusion therefore has exponentially small proportion,
uniformly in the endpoint, once its factorial index is large. -/
theorem gcdBad_q_proportion_eventually131 (HT : ThetaLogSqRemainder127) :
    ∃ N : ℕ, ∀ a : ℕ, N ≤ a → ∀ X : ℕ,
      proportion (gcdBadSet131 (q a)) X ≤ expTail131 a := by
  obtain ⟨N, hN⟩ := qTailWeight_eventually_le_exp131 HT
  refine ⟨N, ?_⟩
  intro a ha X
  exact le_trans (gcdBad_proportion_le_divisor_envelope131
    (Nat.pos_of_ne_zero (q_ne_zero a)) X) (hN a ha)

/-! ### D. Sum the genuinely infinite tail via finite witness covers -/

/-- An elementary identity exposes the geometric series. -/
theorem expTail_eq_geometric131 (a : ℕ) :
    expTail131 a = (Real.exp (-(1 : ℝ) / 8)) ^ a := by
  induction a with
  | zero => simp [expTail131]
  | succ a ih =>
      have hexp : -((a + 1 : ℕ) : ℝ) / 8 = -(a : ℝ) / 8 + (-(1 : ℝ) / 8) := by
        push_cast
        ring
      simp only [expTail131, hexp, Real.exp_add, pow_succ]
      exact congrArg (fun z : ℝ => z * Real.exp (-(1 : ℝ) / 8)) ih

theorem expTail_summable131 : Summable expTail131 := by
  have h0 : 0 ≤ Real.exp (-(1 : ℝ) / 8) := (Real.exp_pos _).le
  have h1 : Real.exp (-(1 : ℝ) / 8) < 1 := by
    have hh := Real.exp_lt_exp.mpr (show -(1 : ℝ) / 8 < 0 by norm_num)
    simpa only [Real.exp_zero] using hh
  have hs := summable_geometric_of_lt_one h0 h1
  have heq : expTail131 = (fun a : ℕ => Real.exp (-(1 : ℝ) / 8) ^ a) :=
    funext expTail_eq_geometric131
  rw [heq]
  exact hs

/-- Closed form of the exponential tail, with no project-specific hypothesis. -/
theorem expTail_shifted_sum131 (B : ℕ) :
    (∑' j : ℕ, expTail131 (j + B)) =
      expTail131 B / (1 - Real.exp (-(1 : ℝ) / 8)) := by
  have h0 : 0 ≤ Real.exp (-(1 : ℝ) / 8) := (Real.exp_pos _).le
  have h1 : Real.exp (-(1 : ℝ) / 8) < 1 := by
    have hh := Real.exp_lt_exp.mpr (show -(1 : ℝ) / 8 < 0 by norm_num)
    simpa only [Real.exp_zero] using hh
  have heq : (fun j : ℕ => expTail131 (j + B)) =
      (fun j : ℕ => Real.exp (-(1 : ℝ) / 8) ^ j *
        Real.exp (-(1 : ℝ) / 8) ^ B) := by
    funext j
    rw [expTail_eq_geometric131, pow_add]
  rw [heq, tsum_mul_right, tsum_geometric_of_lt_one h0 h1,
    expTail_eq_geometric131]
  ring

/-- A finite subset of indices at least B is bounded by the shifted infinite
tail. The reindexing by k-B is injective on that finite subset. -/
theorem finite_sum_le_shifted_tsum131
    (f : ℕ → ℝ) (hf : Summable f) (hf0 : ∀ k : ℕ, 0 ≤ f k)
    (B : ℕ) (W : Finset ℕ) (hW : ∀ k ∈ W, B ≤ k) :
    (∑ k ∈ W, f k) ≤ ∑' j : ℕ, f (j + B) := by
  classical
  let V : Finset ℕ := W.image (fun k : ℕ => k - B)
  have hinj : ∀ k ∈ W, ∀ l ∈ W, k - B = l - B → k = l := by
    intro k hk l hl heq
    have hkB := hW k hk
    have hlB := hW l hl
    omega
  have hsum : (∑ j ∈ V, f (j + B)) = ∑ k ∈ W, f k := by
    unfold V
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.sub_add_cancel (hW k hk)]
  have hshift : Summable (fun j : ℕ => f (j + B)) :=
    (summable_nat_add_iff B).mpr hf
  rw [← hsum]
  exact Summable.sum_le_tsum V (fun j hj => hf0 (j + B)) hshift

/-- Countable-cover estimate derived from finite-prefix counting. -/
theorem proportion_le_shifted_tsum_of_cover131
    (S : Set ℕ) (T : ℕ → Set ℕ) (f : ℕ → ℝ) (B X : ℕ)
    (hf : Summable f) (hf0 : ∀ k : ℕ, 0 ≤ f k)
    (hbound : ∀ k : ℕ, B ≤ k → proportion (T k) X ≤ f k)
    (hcover : ∀ m ∈ S, ∃ k : ℕ, B ≤ k ∧ m ∈ T k) :
    proportion S X ≤ ∑' j : ℕ, f (j + B) := by
  classical
  let s : Finset ℕ := (Finset.Icc 1 X).filter (fun m : ℕ => m ∈ S)
  have hc : ∀ m ∈ s, ∃ k : ℕ, B ≤ k ∧ m ∈ T k := by
    intro m hm
    exact hcover m (Finset.mem_filter.mp hm).2
  obtain ⟨W, hBW, hW⟩ := finite_index_cover131 s T B hc
  have hcount := prefixCount_real_le_sum_of_cover131 S T W X (by
    intro m hm1 hmX hmS
    exact hW m (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmX⟩, hmS⟩))
  have hnorm : proportion S X ≤ ∑ k ∈ W, proportion (T k) X := by
    unfold proportion
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hcount (by positivity)
  calc
    proportion S X ≤ ∑ k ∈ W, proportion (T k) X := hnorm
    _ ≤ ∑ k ∈ W, f k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hbound k (hBW k hk)
    _ ≤ ∑' j : ℕ, f (j + B) := finite_sum_le_shifted_tsum131 f hf hf0 B W hBW

/-- A point in the finite approximation but not in A must fail an omitted
condition, rather than a squarefreeness or positivity condition. -/
theorem Afinite_difference_has_large_witness131 {B m : ℕ}
    (hm : m ∈ RemainingAnalytic20.Afinite B \ A) :
    ∃ a : ℕ, B + 1 ≤ a ∧ m ∈ gcdBadSet131 (q a) := by
  have hmF := hm.1
  have hnot : ¬ ∀ a : ℕ, 2 ≤ a → (Nat.gcd m (q a)) ^ 2 ≤ q a := by
    intro hall
    exact hm.2 ⟨hmF.1, hmF.2.1, hall⟩
  push_neg at hnot
  obtain ⟨a, ha2, hbad⟩ := hnot
  have haB : B < a := by
    by_contra hle
    have hgood := hmF.2.2 a ha2 (by omega)
    omega
  exact ⟨a, by omega, hbad⟩

/-- Quantitative uniform omitted-tail bound. It is valid for all X, not only
after an endpoint threshold. -/
theorem Afinite_tail_le_exp_tsum131 (HT : ThetaLogSqRemainder127) :
    ∃ N : ℕ, ∀ B : ℕ, N ≤ B → ∀ X : ℕ,
      proportion (RemainingAnalytic20.Afinite B \ A) X ≤
        ∑' j : ℕ, expTail131 (j + (B + 1)) := by
  obtain ⟨N, hN⟩ := gcdBad_q_proportion_eventually131 HT
  refine ⟨N, ?_⟩
  intro B hB X
  apply proportion_le_shifted_tsum_of_cover131
    (RemainingAnalytic20.Afinite B \ A) (fun a : ℕ => gcdBadSet131 (q a))
    expTail131 (B + 1) X expTail_summable131
    (fun a => (Real.exp_pos _).le)
  · intro a ha
    exact hN a (by omega) X
  · intro m hm
    exact Afinite_difference_has_large_witness131 hm

/-- Explicit uniform error envelope for the actual finite approximants.
The threshold depends on the supplied theta theorem, not on X. -/
theorem Afinite_tail_explicit131 (HT : ThetaLogSqRemainder127) :
    ∃ N : ℕ, ∀ B : ℕ, N ≤ B → ∀ X : ℕ,
      proportion (RemainingAnalytic20.Afinite B \ A) X ≤
        Real.exp (-((B + 1 : ℕ) : ℝ) / 8) /
          (1 - Real.exp (-(1 : ℝ) / 8)) := by
  obtain ⟨N, hN⟩ := Afinite_tail_le_exp_tsum131 HT
  refine ⟨N, ?_⟩
  intro B hB X
  have hh := hN B hB X
  rw [expTail_shifted_sum131] at hh
  exact hh

/-- The entire old uniform-tail record is constructed from theta. This is
not a tail assumption in another notation. -/
noncomputable def AUniformTail_from_theta131 (HT : ThetaLogSqRemainder127) :
    RemainingAnalytic21.AUniformTail := by
  classical
  have H : ∀ ε : ℝ, ∃ N : ℕ, 0 < ε → ∀ B : ℕ, N ≤ B → ∀ X : ℕ,
      proportion (RemainingAnalytic20.Afinite B \ A) X < ε := by
    intro ε
    obtain ⟨NA, hNA⟩ := Afinite_tail_le_exp_tsum131 HT
    by_cases hε : 0 < ε
    · have ht : Tendsto (fun B : ℕ => ∑' j : ℕ, expTail131 (j + B)) atTop (nhds 0) :=
        tendsto_sum_nat_add expTail131
      have hev : ∀ᶠ B : ℕ in atTop, (∑' j : ℕ, expTail131 (j + B)) < ε :=
        (tendsto_order.mp ht).2 ε hε
      obtain ⟨NE, hNE⟩ := eventually_atTop.mp hev
      refine ⟨max NA NE, ?_⟩
      intro hε' B hB X
      have hBA : NA ≤ B := le_trans (le_max_left _ _) hB
      have hBE : NE ≤ B + 1 := by
        have hh : NE ≤ B := le_trans (le_max_right _ _) hB
        omega
      exact lt_of_le_of_lt (hNA B hBA X) (hNE (B + 1) hBE)
    · exact ⟨0, fun hh => (hε hh).elim⟩
  let cutoff : ℝ → ℕ := fun ε => Classical.choose (H ε)
  exact {
    cutoff := cutoff
    tail := fun ε hε B hB X => Classical.choose_spec (H ε) hε B hB X
  }

/-! ### E. Corrected endpoint with the independent A-tail field removed -/

/-- Six remaining mathematical inputs. Positive limiting density of A,
quantitative theta, sparse prime supply, Harman, large sieve and Weil are
still explicit inputs. The tail is derived rather than assumed. -/
structure EverythingLeftCorrected131 where
  A_density_limit : Remaining_AFiniteDensityLimit47
  theta_logsq_remainder : ThetaLogSqRemainder127
  sparse_good_prime_count : SparseGoodPrimeCount127
  harman_bad_density : DensityZero badShortIntervals127
  large_sieve : RemainingAnalytic92.ClassicalPrimeAdditiveLargeSieve92
  large_modulus_weil : LargeModulusLinearProductWeil127

noncomputable def EverythingLeftCorrected131.to130
    (H : EverythingLeftCorrected131) : EverythingLeftCorrected130 where
  A_density_limit := H.A_density_limit
  A_uniform_tail := AUniformTail_from_theta131 H.theta_logsq_remainder
  theta_logsq_remainder := H.theta_logsq_remainder
  sparse_good_prime_count := H.sparse_good_prime_count
  harman_bad_density := H.harman_bad_density
  large_sieve := H.large_sieve
  large_modulus_weil := H.large_modulus_weil

theorem candidate_main_from_corrected_endgame131
    (H : EverythingLeftCorrected131) : MainStatement :=
  candidate_main_from_corrected_endgame130 H.to130

theorem positive_lower_density_from_corrected_endgame131
    (H : EverythingLeftCorrected131) : PositiveLowerDensity D6 :=
  positive_lower_density_from_corrected_endgame130 H.to130

/-! Individual checks distinguish verified ingredients from a conditional
assembly. A clean axiom report is not an inhabitant of the input record. -/
-- Historical audit output (142): #print axioms finite_index_cover131
-- Historical audit output (142): #print axioms prefixCount_real_le_sum_of_cover131
-- Historical audit output (142): #print axioms prefixCount_multiples_le_natDiv131
-- Historical audit output (142): #print axioms gcdBadSet_divisor_cover131
-- Historical audit output (142): #print axioms gcdBad_count_le_divisor_envelope131
-- Historical audit output (142): #print axioms gcdBad_proportion_le_divisor_envelope131
-- Historical audit output (142): #print axioms squarefree_divisor_card_le_pow131
-- Historical audit output (142): #print axioms q_primeFactor_card_le_primeCount131
-- Historical audit output (142): #print axioms q_divisor_card_le_primeCount_pow131
-- Historical audit output (142): #print axioms qTailWeight_eventually_le_exp131
-- Historical audit output (142): #print axioms gcdBad_q_proportion_eventually131
-- Historical audit output (142): #print axioms expTail_eq_geometric131
-- Historical audit output (142): #print axioms expTail_summable131
-- Historical audit output (142): #print axioms expTail_shifted_sum131
-- Historical audit output (142): #print axioms finite_sum_le_shifted_tsum131
-- Historical audit output (142): #print axioms proportion_le_shifted_tsum_of_cover131
-- Historical audit output (142): #print axioms Afinite_difference_has_large_witness131
-- Historical audit output (142): #print axioms Afinite_tail_le_exp_tsum131
-- Historical audit output (142): #print axioms Afinite_tail_explicit131
-- Historical audit output (142): #print axioms AUniformTail_from_theta131
-- Historical audit output (142): #print axioms EverythingLeftCorrected131.to130
-- Historical audit output (142): #print axioms candidate_main_from_corrected_endgame131
-- Historical audit output (142): #print axioms positive_lower_density_from_corrected_endgame131
-- Historical audit output (142): #check AUniformTail_from_theta131
-- Historical audit output (142): #check candidate_main_from_corrected_endgame131
-- Historical audit output (142): #check positive_lower_density_from_corrected_endgame131
-- Historical audit output (142): #print EverythingLeftCorrected131

end RemainingAnalytic131

/-! ## 132. Finite periodic sieves, square-divisor tails, and density existence

The new results distinguish three different claims:
* each finite gcd-condition set has a natural density (proved below);
* those densities converge, and theta supplies a density of A (proved below);
* that density is positive (requires the explicitly stated finite margin).

The last point is not inferred merely from convergence of positive numbers.
These are new proof scripts, not a claim of a successful local Lean run.
-/
namespace RemainingAnalytic132

open scoped BigOperators
open RemainingAnalytic20 RemainingAnalytic47 RemainingAnalytic127
open RemainingAnalytic130 RemainingAnalytic131

/-! ### A. Order and limit tools for the source's actual density predicate -/

theorem proportion_mono132 {S T : Set ℕ} (hST : S ⊆ T) (X : ℕ) :
    proportion S X ≤ proportion T X := by
  classical
  have hcount : prefixCount S X ≤ prefixCount T X := by
    apply Finset.card_le_card
    intro m hm
    have h := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨h.1, hST h.2⟩
  unfold proportion
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)

theorem hasDensity_nonneg132 {S : Set ℕ} {δ : ℝ}
    (hD : HasDensity S δ) : 0 ≤ δ := by
  by_contra hh
  have hδ : δ < 0 := lt_of_not_ge hh
  obtain ⟨N, hN⟩ := hD (-δ / 2) (by linarith)
  have hb := (abs_lt.mp (hN N le_rfl)).2
  have hp := proportion_nonneg S N
  linarith

/-- Passing an additive upper bound to densities does not require the
existence of a density of a set difference. -/
theorem density_le_add132 {S T : Set ℕ} {δ ε c : ℝ}
    (hS : HasDensity S δ) (hT : HasDensity T ε)
    (hbound : ∀ X : ℕ, proportion S X ≤ proportion T X + c) :
    δ ≤ ε + c := by
  by_contra hh
  have hgap : 0 < (δ - ε - c) / 4 := by linarith
  obtain ⟨NS, hNS⟩ := hS ((δ - ε - c) / 4) hgap
  obtain ⟨NT, hNT⟩ := hT ((δ - ε - c) / 4) hgap
  have hs := (abs_lt.mp (hNS (max NS NT) (le_max_left _ _))).1
  have ht := (abs_lt.mp (hNT (max NS NT) (le_max_right _ _))).2
  have hb := hbound (max NS NT)
  linarith

theorem density_mono132 {S T : Set ℕ} {δ ε : ℝ}
    (hST : S ⊆ T) (hS : HasDensity S δ) (hT : HasDensity T ε) : δ ≤ ε := by
  have hh := density_le_add132 hS hT (c := 0) (fun X => by
    simpa only [add_zero] using proportion_mono132 hST X)
  simpa only [add_zero] using hh

/-- A uniform omitted-set bound bounds the difference between the densities. -/
theorem density_gap_le132 {S T : Set ℕ} {δ ε c : ℝ}
    (hST : S ⊆ T) (hS : HasDensity S δ) (hT : HasDensity T ε)
    (hgap : ∀ X : ℕ, proportion (T \ S) X ≤ c) : ε ≤ δ + c := by
  apply density_le_add132 hT hS
  intro X
  have hinter : S ∩ T = S := Set.inter_eq_left.mpr hST
  have hp := proportion_inter_eq_sub S T X
  rw [hinter] at hp
  have hh := hgap X
  linarith

/-- A decreasing nonnegative sequence approaches its infimum. The proof
supplies the epsilon cutoff, rather than assuming convergence. -/
theorem antitone_values_inf132 (d : ℕ → ℝ)
    (hd0 : ∀ k : ℕ, 0 ≤ d k) (hd : Antitone d) :
    (∀ k : ℕ, sInf (Set.range d) ≤ d k) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      |d k - sInf (Set.range d)| < ε) := by
  have hne : (Set.range d).Nonempty := ⟨d 0, ⟨0, rfl⟩⟩
  have hbb : BddBelow (Set.range d) := by
    refine ⟨0, ?_⟩
    rintro z ⟨k, rfl⟩
    exact hd0 k
  have hlow : ∀ k : ℕ, sInf (Set.range d) ≤ d k := by
    intro k
    exact csInf_le hbb (Set.mem_range_self k)
  refine ⟨hlow, ?_⟩
  intro ε hε
  obtain ⟨z, hz, hsmall⟩ := exists_lt_of_csInf_lt hne
    (show sInf (Set.range d) < sInf (Set.range d) + ε by linarith)
  obtain ⟨N, rfl⟩ := hz
  refine ⟨N, ?_⟩
  intro k hk
  rw [abs_of_nonneg (sub_nonneg.mpr (hlow k))]
  have hh := hd hk
  linarith

/-- Uniform upper approximations with known densities have a density. The
intersection itself need not be periodic, and positivity is not asserted. -/
theorem hasDensity_of_upper_approximations132
    (S : Set ℕ) (T : ℕ → Set ℕ) (d : ℕ → ℝ)
    (hD : ∀ k : ℕ, HasDensity (T k) (d k))
    (hmono : ∀ k l : ℕ, k ≤ l → T l ⊆ T k)
    (hST : ∀ k : ℕ, S ⊆ T k)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ X : ℕ, proportion (T k \ S) X < ε) :
    HasDensity S (sInf (Set.range d)) := by
  have hd0 : ∀ k : ℕ, 0 ≤ d k := fun k => hasDensity_nonneg132 (hD k)
  have hd : Antitone d := by
    intro k l hkl
    exact density_mono132 (hmono k l hkl) (hD l) (hD k)
  have hinf := antitone_values_inf132 d hd0 hd
  intro ε hε
  have he3 : 0 < ε / 3 := by linarith
  obtain ⟨NI, hNI⟩ := hinf.2 (ε / 3) he3
  obtain ⟨NT, hNT⟩ := htail (ε / 3) he3
  let k := max NI NT
  have hkI : NI ≤ k := le_max_left _ _
  have hkT : NT ≤ k := le_max_right _ _
  obtain ⟨NX, hNX⟩ := hD k (ε / 3) he3
  refine ⟨NX, ?_⟩
  intro X hX
  have ha := abs_lt.mp (hNX X hX)
  have hi := abs_lt.mp (hNI k hkI)
  have ht := hNT k hkT X
  have ht0 := proportion_nonneg (T k \ S) X
  have hinter : S ∩ T k = S := Set.inter_eq_left.mpr (hST k)
  have hpart := proportion_inter_eq_sub S (T k) X
  rw [hinter] at hpart
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-! ### B. Finite periodic predicates: a complete elementary density proof -/

/-- Repeat a period any natural number of times. -/
theorem periodic_shift_mul132 (f : ℕ → ℝ) (M : ℕ)
    (hper : ∀ n : ℕ, f (n + M) = f n) (n k : ℕ) :
    f (n + k * M) = f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        f (n + (k + 1) * M) = f ((n + k * M) + M) := by congr 1; ring
        _ = f (n + k * M) := hper _
        _ = f n := ih

/-- Exact sum over complete blocks of a periodic sequence. -/
theorem periodic_block_sum132 (f : ℕ → ℝ) (M : ℕ)
    (hper : ∀ n : ℕ, f (n + M) = f n) (k : ℕ) :
    (∑ i ∈ Finset.range (k * M), f i) =
      (k : ℝ) * (∑ i ∈ Finset.range M, f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hshift : (∑ i ∈ Finset.range M, f (k * M + i)) =
          ∑ i ∈ Finset.range M, f i := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [Nat.add_comm] using periodic_shift_mul132 f M hper i k
      rw [Nat.add_mul, one_mul, Finset.sum_range_add, ih, hshift]
      push_cast
      ring

/-- For values in [0,1], the error from an incomplete period is at most M. -/
theorem periodic_sum_error132 (f : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hper : ∀ n : ℕ, f (n + M) = f n)
    (hf : ∀ n : ℕ, 0 ≤ f n ∧ f n ≤ 1) (X : ℕ) :
    |(∑ i ∈ Finset.range X, f i) -
      (X : ℝ) * ((∑ i ∈ Finset.range M, f i) / (M : ℝ))| ≤ (M : ℝ) := by
  let W : ℝ := ∑ i ∈ Finset.range M, f i
  let R : ℝ := ∑ i ∈ Finset.range (X % M), f i
  have hMp : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun i hi => (hf i).1)
  have hW1 : W ≤ (M : ℝ) := by
    have hh := Finset.sum_le_sum (s := Finset.range M) (fun i hi => (hf i).2)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using hh
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun i hi => (hf i).1)
  have hR1 : R ≤ ((X % M : ℕ) : ℝ) := by
    have hh := Finset.sum_le_sum (s := Finset.range (X % M)) (fun i hi => (hf i).2)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using hh
  have hδ0 : 0 ≤ W / (M : ℝ) := div_nonneg hW0 hMp.le
  have hδ1 : W / (M : ℝ) ≤ 1 := (div_le_one hMp).mpr hW1
  have hrem0 : (0 : ℝ) ≤ ((X % M : ℕ) : ℝ) := by positivity
  have hrem : ((X % M : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.mod_lt X hM).le
  have hmult0 : 0 ≤ ((X % M : ℕ) : ℝ) * (W / (M : ℝ)) := mul_nonneg hrem0 hδ0
  have hmult1 : ((X % M : ℕ) : ℝ) * (W / (M : ℝ)) ≤ ((X % M : ℕ) : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1 hrem0
  have hdecomp : (X / M) * M + X % M = X := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod X M
  have hsum : (∑ i ∈ Finset.range X, f i) = ((X / M : ℕ) : ℝ) * W + R := by
    conv_lhs => rw [← hdecomp]
    rw [Finset.sum_range_add, periodic_block_sum132 f M hper]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Nat.add_comm] using periodic_shift_mul132 f M hper i (X / M)
  have hdecompR : ((X / M : ℕ) : ℝ) * (M : ℝ) + ((X % M : ℕ) : ℝ) = (X : ℝ) := by
    exact_mod_cast hdecomp
  have hidentity : ((X / M : ℕ) : ℝ) * W + R - (X : ℝ) * (W / (M : ℝ)) =
      R - ((X % M : ℕ) : ℝ) * (W / (M : ℝ)) := by
    rw [← hdecompR]
    field_simp [ne_of_gt hMp] <;> ring
  rw [hsum, hidentity]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Periodicity is needed only for the predicate; m=0 is irrelevant because
prefixCount starts at 1. No CRT or prime-number theorem is used here. -/
theorem periodic_predicate_hasDensity132 (P : ℕ → Prop) (M : ℕ) (hM : 0 < M)
    (hper : ∀ n : ℕ, P (n + M) ↔ P n) :
    HasDensity {m : ℕ | 1 ≤ m ∧ P m}
      ((∑ i ∈ Finset.range M, if P (i + 1) then (1 : ℝ) else 0) / (M : ℝ)) := by
  classical
  let f : ℕ → ℝ := fun i => if P (i + 1) then 1 else 0
  have hf : ∀ i : ℕ, 0 ≤ f i ∧ f i ≤ 1 := by
    intro i
    dsimp [f]
    split_ifs <;> norm_num
  have hfper : ∀ i : ℕ, f (i + M) = f i := by
    intro i
    have hh := hper (i + 1)
    have heq : i + M + 1 = i + 1 + M := by omega
    simp only [f, heq, hh]
  have hcount : ∀ X : ℕ,
      (prefixCount {m : ℕ | 1 ≤ m ∧ P m} X : ℝ) = ∑ i ∈ Finset.range X, f i := by
    intro X
    have hshift := sum_range_succ_eq_Icc127
      (fun m : ℕ => if P m then (1 : ℝ) else 0) X
    refine (prefixCount_eq_indicator_sum127 {m : ℕ | 1 ≤ m ∧ P m} X).trans ?_
    calc
      _ = ∑ m ∈ Finset.Icc 1 X, (if P m then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm1 := (Finset.mem_Icc.mp hm).1
        by_cases hmP : P m
        · simp only [Set.mem_setOf_eq, hm1, hmP, and_self, ite_true]
        · simp only [Set.mem_setOf_eq, hm1, hmP, and_false, ite_false]
      _ = ∑ i ∈ Finset.range X, f i := hshift.symm
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((M : ℝ) / ε)
  refine ⟨max N 1, ?_⟩
  intro X hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hscale : (M : ℝ) / ε < (X : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hXN)
  have hsmall : (M : ℝ) / (X : ℝ) < ε := by
    apply (div_lt_iff₀ hXp).mpr
    have hh := (div_lt_iff₀ hε).mp hscale
    nlinarith only [hh]
  have hb := periodic_sum_error132 f M hM hfper hf X
  have hid : (∑ i ∈ Finset.range X, f i) / (X : ℝ) -
      (∑ i ∈ Finset.range M, f i) / (M : ℝ) =
      ((∑ i ∈ Finset.range X, f i) - (X : ℝ) *
        ((∑ i ∈ Finset.range M, f i) / (M : ℝ))) / (X : ℝ) := by
    field_simp [ne_of_gt hXp] <;> ring
  change |proportion {m : ℕ | 1 ≤ m ∧ P m} X -
    (∑ i ∈ Finset.range M, f i) / (M : ℝ)| < ε
  unfold proportion
  rw [hcount, hid, abs_div, abs_of_pos hXp]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hb hXp.le) hsmall

/-! ### C. Actual finite gcd/square tests and their periods -/

/-- This finite predicate deliberately omits positivity, so that it is periodic. -/
def finiteTest132 (B K m : ℕ) : Prop :=
  (∀ a : ℕ, 2 ≤ a → a ≤ B → (Nat.gcd m (q a)) ^ 2 ≤ q a) ∧
  (∀ p : ℕ, p.Prime → p ≤ K → ¬ p ^ 2 ∣ m)

def finiteSieve132 (B K : ℕ) : Set ℕ := {m : ℕ | 1 ≤ m ∧ finiteTest132 B K m}

/-- A positive common multiple, not a claim of a minimal period. Products
avoid needing a separate primorial or least-common-multiple library. -/
def sievePeriod132 (B K : ℕ) : ℕ :=
  (∏ a ∈ Finset.range (B + 1), q a) *
    (∏ d ∈ Finset.range (K + 1), (d + 1) ^ 2)

theorem sievePeriod_pos132 (B K : ℕ) : 0 < sievePeriod132 B K := by
  unfold sievePeriod132
  apply Nat.mul_pos
  · exact Finset.prod_pos (fun a ha => Nat.pos_of_ne_zero (q_ne_zero a))
  · apply Finset.prod_pos
    intro d hd
    exact pow_pos (Nat.succ_pos d) 2

theorem q_dvd_sievePeriod132 {B K a : ℕ} (ha : a ≤ B) : q a ∣ sievePeriod132 B K := by
  have hd : q a ∣ ∏ i ∈ Finset.range (B + 1), q i :=
    Finset.dvd_prod_of_mem q (Finset.mem_range.mpr (by omega))
  exact dvd_trans hd (dvd_mul_right _ _)

theorem square_dvd_sievePeriod132 {B K p : ℕ} (hp : 1 ≤ p) (hpK : p ≤ K) :
    p ^ 2 ∣ sievePeriod132 B K := by
  have hidx : p - 1 ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  have hd := Finset.dvd_prod_of_mem (fun d : ℕ => (d + 1) ^ 2) hidx
  have heq : p - 1 + 1 = p := by omega
  rw [heq] at hd
  exact dvd_trans hd (dvd_mul_left _ _)

/-- Translating by a multiple of Q preserves the gcd with Q. -/
theorem gcd_add_multiple132 {Q M : ℕ} (hQM : Q ∣ M) (m : ℕ) :
    Nat.gcd (m + M) Q = Nat.gcd m Q := by
  obtain ⟨k, rfl⟩ := hQM
  exact Nat.gcd_add_mul_left_left Q m k

/-- Translating by a multiple of d preserves divisibility by d. -/
theorem dvd_add_multiple132 {d M : ℕ} (hdM : d ∣ M) (m : ℕ) :
    d ∣ m + M ↔ d ∣ m := by
  constructor
  · intro hh
    have hsub := Nat.dvd_sub hh hdM
    simpa only [Nat.add_sub_cancel] using hsub
  · intro hh
    exact dvd_add hh hdM

theorem finiteTest_periodic132 (B K m : ℕ) :
    finiteTest132 B K (m + sievePeriod132 B K) ↔ finiteTest132 B K m := by
  unfold finiteTest132
  have hg : ∀ a : ℕ, a ≤ B →
      Nat.gcd (m + sievePeriod132 B K) (q a) = Nat.gcd m (q a) := by
    intro a ha
    exact gcd_add_multiple132 (q_dvd_sievePeriod132 ha) m
  have hs : ∀ p : ℕ, p.Prime → p ≤ K →
      (p ^ 2 ∣ m + sievePeriod132 B K ↔ p ^ 2 ∣ m) := by
    intro p hp hpK
    exact dvd_add_multiple132 (square_dvd_sievePeriod132 (by have := hp.two_le; omega) hpK) m
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · intro a ha2 haB
      simpa only [hg a haB] using h1 a ha2 haB
    · intro p hp hpK hdiv
      exact h2 p hp hpK ((hs p hp hpK).mpr hdiv)
  · rintro ⟨h1, h2⟩
    constructor
    · intro a ha2 haB
      simpa only [hg a haB] using h1 a ha2 haB
    · intro p hp hpK hdiv
      exact h2 p hp hpK ((hs p hp hpK).mp hdiv)

noncomputable def finiteSieveDensity132 (B K : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (sievePeriod132 B K),
    if finiteTest132 B K (i + 1) then (1 : ℝ) else 0) / (sievePeriod132 B K : ℝ)

/-- Every finite periodic sieve has its explicitly computed block density. -/
theorem finiteSieve_hasDensity132 (B K : ℕ) :
    HasDensity (finiteSieve132 B K) (finiteSieveDensity132 B K) :=
  periodic_predicate_hasDensity132 (finiteTest132 B K) (sievePeriod132 B K)
    (sievePeriod_pos132 B K) (finiteTest_periodic132 B K)

theorem finiteSieve_antitone132 (B : ℕ) {K L : ℕ} (hKL : K ≤ L) :
    finiteSieve132 B L ⊆ finiteSieve132 B K := by
  rintro m ⟨hm1, hg, hs⟩
  exact ⟨hm1, hg, fun p hp hpK => hs p hp (le_trans hpK hKL)⟩

theorem Afinite_subset_finiteSieve132 (B K : ℕ) :
    Afinite B ⊆ finiteSieve132 B K := by
  intro m hm
  refine ⟨hm.1, hm.2.2, ?_⟩
  intro p hp hpK hdiv
  have hs := (Nat.squarefree_iff_prime_squarefree.mp hm.2.1) p hp
  exact hs (by simpa only [pow_two] using hdiv)

/-! ### D. Omitted square divisors: an explicit 1/K error for every prefix -/

/-- A telescoping comparison for reciprocal squares. -/
theorem inverse_square_step132 {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have hid : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp [ne_of_gt hx, ne_of_gt hx1] <;> ring
  rw [hid]
  apply one_div_le_one_div_of_le (mul_pos hx hx1)
  nlinarith

theorem inverse_square_tail_finite132 (K N : ℕ) (hK : 1 ≤ K) :
    (∑ j ∈ Finset.range N, (1 : ℝ) / (((j + K + 1 : ℕ) : ℝ) ^ 2)) ≤
      1 / (K : ℝ) := by
  have hKp : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have htel : ∀ n : ℕ,
      (∑ j ∈ Finset.range n, (1 : ℝ) / (((j + K + 1 : ℕ) : ℝ) ^ 2)) ≤
        1 / (K : ℝ) - 1 / ((n + K : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hxp : (0 : ℝ) < ((n + K : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < n + K by omega)
        have hh := inverse_square_step132 hxp
        have hcast : ((n + K + 1 : ℕ) : ℝ) = ((n + K : ℕ) : ℝ) + 1 := by push_cast; ring
        have hidx : n + 1 + K = n + K + 1 := by omega
        rw [Finset.sum_range_succ, hidx]
        rw [← hcast] at hh
        linarith only [ih, hh]
  have hnonneg : (0 : ℝ) ≤ 1 / ((N + K : ℕ) : ℝ) := by positivity
  linarith only [htel N, hnonneg]

/-- A failed squarefreeness condition produces an actual omitted prime square. -/
theorem finiteSieve_difference_square_witness132 {B K m : ℕ}
    (hm : m ∈ finiteSieve132 B K \ Afinite B) :
    ∃ p : ℕ, K < p ∧ p.Prime ∧ p ^ 2 ∣ m := by
  have hnotSF : ¬ Squarefree m := by
    intro hs
    exact hm.2 ⟨hm.1.1, hs, hm.1.2.1⟩
  have hnot : ¬ ∀ p : ℕ, p.Prime → ¬ p * p ∣ m := by
    intro hh
    exact hnotSF (Nat.squarefree_iff_prime_squarefree.mpr hh)
  push_neg at hnot
  obtain ⟨p, hp, hdiv⟩ := hnot
  have hpow : p ^ 2 ∣ m := by simpa only [pow_two] using hdiv
  have hpK : K < p := by
    by_contra hh
    exact hm.1.2.2 p hp (Nat.le_of_not_gt hh) hpow
  exact ⟨p, hpK, hp, hpow⟩

/-- The squarefree tail bound uses a finite union at each X. It does not
assume countable subadditivity of asymptotic density. -/
theorem finiteSieve_square_tail132 (B K X : ℕ) (hK : 1 ≤ K) :
    proportion (finiteSieve132 B K \ Afinite B) X ≤ 1 / (K : ℝ) := by
  classical
  let T : ℕ → Set ℕ := fun j => {m : ℕ | (j + K + 1) ^ 2 ∣ m}
  have hcover : ∀ m : ℕ, 1 ≤ m → m ≤ X →
      m ∈ finiteSieve132 B K \ Afinite B → ∃ j ∈ Finset.range (X + 1), m ∈ T j := by
    intro m hm1 hmX hm
    obtain ⟨p, hpK, hp, hdiv⟩ := finiteSieve_difference_square_witness132 hm
    have hp2 : p ^ 2 ≤ m := Nat.le_of_dvd (by omega) hdiv
    have hpX : p ≤ X := by
      have hppos := hp.two_le
      have hsq : p ≤ p ^ 2 := by nlinarith
      omega
    refine ⟨p - (K + 1), Finset.mem_range.mpr (by omega), ?_⟩
    have hid : p - (K + 1) + K + 1 = p := by omega
    change (p - (K + 1) + K + 1) ^ 2 ∣ m
    rw [hid]
    exact hdiv
  have hc := prefixCount_real_le_sum_of_cover131
    (finiteSieve132 B K \ Afinite B) T (Finset.range (X + 1)) X hcover
  have hmultiples : ∀ j : ℕ,
      (prefixCount (T j) X : ℝ) ≤ (X : ℝ) / (((j + K + 1 : ℕ) : ℝ) ^ 2) := by
    intro j
    have hd1 : 1 ≤ (j + K + 1) ^ 2 := by
      have hdp : 0 < (j + K + 1) ^ 2 := pow_pos (by omega) _
      omega
    have hnat := prefixCount_multiples_le_natDiv131 ((j + K + 1) ^ 2) X hd1
    have hreal : (prefixCount (T j) X : ℝ) ≤ ((X / (j + K + 1) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hdiv := RemainingAnalytic52.natDivCastLeRealDiv_proved52 X ((j + K + 1) ^ 2) hd1
    exact le_trans hreal (by simpa only [Nat.cast_pow] using hdiv)
  have hsum := Finset.sum_le_sum (s := Finset.range (X + 1)) (fun j hj => hmultiples j)
  have hfactor : (∑ j ∈ Finset.range (X + 1), (X : ℝ) / (((j + K + 1 : ℕ) : ℝ) ^ 2)) =
      (X : ℝ) * (∑ j ∈ Finset.range (X + 1), 1 / (((j + K + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfactor] at hsum
  have htail := mul_le_mul_of_nonneg_left (inverse_square_tail_finite132 K (X + 1) hK)
    (show (0 : ℝ) ≤ (X : ℝ) by positivity)
  have hcount : (prefixCount (finiteSieve132 B K \ Afinite B) X : ℝ) ≤
      (X : ℝ) * (1 / (K : ℝ)) := le_trans hc (le_trans hsum htail)
  by_cases hX : X = 0
  · subst X
    simp only [proportion, Nat.cast_zero, div_zero]
    positivity
  · have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hX
    unfold proportion
    apply (div_le_iff₀ hXp).mpr
    simpa only [mul_comm] using hcount

/-! ### E. Construct the finite-condition densities and their actual limit -/

noncomputable def AfiniteDensity132 (B : ℕ) : ℝ :=
  sInf (Set.range (finiteSieveDensity132 B))

/-- No project-specific analytic assumption is needed for any finite level. -/
theorem Afinite_hasDensity132 (B : ℕ) : HasDensity (Afinite B) (AfiniteDensity132 B) := by
  apply hasDensity_of_upper_approximations132 (Afinite B) (finiteSieve132 B)
    (finiteSieveDensity132 B) (finiteSieve_hasDensity132 B)
  · intro K L hKL
    exact finiteSieve_antitone132 B hKL
  · exact Afinite_subset_finiteSieve132 B
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨max N 1, ?_⟩
    intro K hK X
    have hK1 : 1 ≤ K := le_trans (le_max_right _ _) hK
    have hKN : N ≤ K := le_trans (le_max_left _ _) hK
    have hKp : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
    have hlarge : 1 / ε < (K : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hKN)
    have hsmall : 1 / (K : ℝ) < ε := by
      apply (div_lt_iff₀ hKp).mpr
      have hh := (div_lt_iff₀ hε).mp hlarge
      nlinarith only [hh]
    exact lt_of_le_of_lt (finiteSieve_square_tail132 B K X hK1) hsmall

/-- The finite density is within 1/K of its finite periodic block density. -/
theorem AfiniteDensity_bracket132 (B K : ℕ) (hK : 1 ≤ K) :
    AfiniteDensity132 B ≤ finiteSieveDensity132 B K ∧
    finiteSieveDensity132 B K ≤ AfiniteDensity132 B + 1 / (K : ℝ) := by
  have hsub := Afinite_subset_finiteSieve132 B K
  exact ⟨density_mono132 hsub (Afinite_hasDensity132 B) (finiteSieve_hasDensity132 B K),
    density_gap_le132 hsub (Afinite_hasDensity132 B) (finiteSieve_hasDensity132 B K)
      (fun X => finiteSieve_square_tail132 B K X hK)⟩

theorem Afinite_antitone132 {B C : ℕ} (hBC : B ≤ C) : Afinite C ⊆ Afinite B := by
  intro m hm
  exact ⟨hm.1, hm.2.1, fun a ha2 haB => hm.2.2 a ha2 (le_trans haB hBC)⟩

theorem AfiniteDensity_antitone132 : Antitone AfiniteDensity132 := by
  intro B C hBC
  exact density_mono132 (Afinite_antitone132 hBC) (Afinite_hasDensity132 C) (Afinite_hasDensity132 B)

noncomputable def ADensity132 : ℝ := sInf (Set.range AfiniteDensity132)

/-- Convergence is proved; strict positivity is deliberately not inferred. -/
theorem AfiniteDensity_converges132 :
    (∀ B : ℕ, ADensity132 ≤ AfiniteDensity132 B) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ B : ℕ, N ≤ B →
      |AfiniteDensity132 B - ADensity132| < ε) :=
  antitone_values_inf132 AfiniteDensity132
    (fun B => hasDensity_nonneg132 (Afinite_hasDensity132 B)) AfiniteDensity_antitone132

/-- The existence of a natural density of A follows from theta and the
constructed finite-level densities. Its positivity remains a distinct claim. -/
theorem A_hasDensity_from_theta132 (HT : ThetaLogSqRemainder127) : HasDensity A ADensity132 := by
  let Htail := AUniformTail_from_theta131 HT
  apply hasDensity_of_upper_approximations132 A Afinite AfiniteDensity132 Afinite_hasDensity132
  · intro B C hBC
    exact Afinite_antitone132 hBC
  · exact A_subset_Afinite
  · intro ε hε
    exact ⟨Htail.cutoff ε, fun B hB X => Htail.tail ε hε B hB X⟩

/-- Both squarefree and gcd tails appear explicitly in a quantitative
lower bracket for the density of A. -/
theorem ADensity_finite_lower_bound132 (HT : ThetaLogSqRemainder127)
    (B K : ℕ) (hK : 1 ≤ K) (E : ℝ)
    (hE : ∀ X : ℕ, proportion (Afinite B \ A) X ≤ E) :
    finiteSieveDensity132 B K - 1 / (K : ℝ) - E ≤ ADensity132 := by
  have hsquare := (AfiniteDensity_bracket132 B K hK).2
  have hgcd := density_gap_le132 (A_subset_Afinite B) (A_hasDensity_from_theta132 HT)
    (Afinite_hasDensity132 B) hE
  linarith only [hsquare, hgcd]

/-! ### F. The remaining positivity obligation is exposed as a finite margin

A finite periodic count, larger than the two explicit tail costs, is enough.
No such positive-margin witness is manufactured or asserted in this release.
-/

noncomputable def thetaTailCutoff132 (HT : ThetaLogSqRemainder127) : ℕ :=
  Classical.choose (Afinite_tail_explicit131 HT)

/-- This is the only remaining A-density obligation in the new interface.
The threshold is supplied by the already-required theta input. -/
def FinitePositiveMargin132 (HT : ThetaLogSqRemainder127) : Prop :=
  ∃ B K : ℕ, thetaTailCutoff132 HT ≤ B ∧ 1 ≤ K ∧
    1 / (K : ℝ) + Real.exp (-((B + 1 : ℕ) : ℝ) / 8) /
      (1 - Real.exp (-(1 : ℝ) / 8)) < finiteSieveDensity132 B K

theorem ADensity_pos_of_finite_margin132 (HT : ThetaLogSqRemainder127)
    (Hpos : FinitePositiveMargin132 HT) : 0 < ADensity132 := by
  obtain ⟨B, K, hB, hK, hmargin⟩ := Hpos
  have htail : ∀ X : ℕ, proportion (Afinite B \ A) X ≤
      Real.exp (-((B + 1 : ℕ) : ℝ) / 8) / (1 - Real.exp (-(1 : ℝ) / 8)) :=
    Classical.choose_spec (Afinite_tail_explicit131 HT) B hB
  have hlower := ADensity_finite_lower_bound132 HT B K hK _ htail
  linarith only [hmargin, hlower]

/-- The old positive finite-density-limit record is constructed from actual
finite densities and a positive margin, not retained as a single black box. -/
noncomputable def AFiniteDensityLimit_from_margin132 (HT : ThetaLogSqRemainder127)
    (Hpos : FinitePositiveMargin132 HT) : RemainingAnalytic21.AFiniteDensityLimit := by
  classical
  have HC : ∀ ε : ℝ, ∃ N : ℕ, 0 < ε → ∀ B : ℕ, N ≤ B →
      |AfiniteDensity132 B - ADensity132| < ε := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨N, hN⟩ := AfiniteDensity_converges132.2 ε hε
      exact ⟨N, fun _ B hB => hN B hB⟩
    · exact ⟨0, fun hh => (hε hh).elim⟩
  let cutoff : ℝ → ℕ := fun ε => Classical.choose (HC ε)
  exact {
    delta := ADensity132
    delta_pos := ADensity_pos_of_finite_margin132 HT Hpos
    cutoff := cutoff
    densityAt := AfiniteDensity132
    finite_density := fun ε hε B hB => Afinite_hasDensity132 B
    close := fun ε hε B hB => Classical.choose_spec (HC ε) hε B hB
  }


end RemainingAnalytic132
end RemainingAnalytic115
end Erdos374
end
end Update150_Component_1
end Update151_Component_1
end Update152_Component_1

end
