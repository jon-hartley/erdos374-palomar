module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
-- Modules visible before the module-system port (privately imported upstream):
public import Aesop.Constants
public import Aesop.Exception
public import Aesop.Forward.State.ApplyGoalDiff
public import Aesop.Forward.State.Initial
public import Aesop.Script.OptimizeSyntax
public import Aesop.Script.StructureDynamic
public import Aesop.Script.StructureStatic
public import Aesop.Script.UScriptToSScript
public import Aesop.Script.Util
public import Aesop.Search.Expansion.Basic
public import Aesop.Search.Expansion.Simp
public import Aesop.Search.Queue
public import Aesop.Tree.Free
public import Aesop.Tree.Stats
public import Aesop.Util.EqualUpToIds
public import Aesop.Util.Tactic
public import Aesop.Util.Tactic.Unfold
public import Aesop.Util.UnionFind
public import Batteries.Data.UInt
public import Batteries.Lean.HashSet
public import Batteries.Lean.Meta.DiscrTree
public import Batteries.Lean.Meta.Inaccessible
public import Batteries.Lean.PersistentHashSet
public import Init.Data.Array.Bootstrap
public import Init.Data.Array.Count
public import Init.Data.Array.Extract
public import Init.Data.Array.Find
public import Init.Data.Array.InsertIdx
public import Init.Data.Array.MapIdx
public import Init.Data.Array.Mem
public import Init.Data.Array.Monadic
public import Init.Data.Array.Nat
public import Init.Data.Array.OfFn
public import Init.Data.BitVec.Decidable
public import Init.Data.Char.Lemmas
public import Init.Data.Char.Order
public import Init.Data.Erased
public import Init.Data.Fin.Iterate
public import Init.Data.Fin.Log2
public import Init.Data.Int.Cooper
public import Init.Data.Int.DivMod
public import Init.Data.Int.OfNat
public import Init.Data.Iterators.Lemmas
public import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.Iterators.Lemmas.Monadic.Basic
public import Init.Data.List.Count
public import Init.Data.List.Erase
public import Init.Data.List.Find
public import Init.Data.List.Lex
public import Init.Data.List.Nat.BEq
public import Init.Data.List.Nat.Basic
public import Init.Data.List.Nat.Count
public import Init.Data.List.Nat.Erase
public import Init.Data.List.Nat.Find
public import Init.Data.List.Nat.InsertIdx
public import Init.Data.List.Nat.Modify
public import Init.Data.List.Nat.Prod
public import Init.Data.List.Nat.Range
public import Init.Data.List.Nat.Sum
public import Init.Data.List.Nat.TakeDrop
public import Init.Data.List.Pairwise
public import Init.Data.List.Range
public import Init.Data.List.Sublist
public import Init.Data.List.TakeDrop
public import Init.Data.List.Zip
public import Init.Data.Nat.Power2.Lemmas
public import Init.Data.Nat.Simproc
public import Init.Data.Option.Array
public import Init.Data.Option.Function
public import Init.Data.Option.List
public import Init.Data.Prod
public import Init.Data.Range.Polymorphic
public import Init.Data.Range.Polymorphic.Internal.SignedBitVec
public import Init.Data.Slice.InternalLemmas
public import Init.Data.String.Lemmas.Basic
public import Init.Data.String.Lemmas.FindPos
public import Init.Data.String.Lemmas.Iterate
public import Init.Data.String.Lemmas.StringOrder
public import Init.Data.String.Modify
public import Init.Data.String.OrderInstances
public import Init.Data.Subtype.Basic
public import Init.Data.Vector.Lemmas
public import Init.Grind
public import Init.Hints
public import Init.LawfulBEqTactics
public import Init.System.Platform
public import Init.TacticsExtra
public import Lean.BuiltinDocAttr
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.LCNF.Basic
public import Lean.Compiler.NameMangling
public import Lean.Compiler.Options
public import Lean.Elab.ConfigEval.Util
public import Lean.Elab.DeprecatedArg
public import Lean.Elab.DeprecatedSyntax
public import Lean.Elab.DocString
public import Lean.Elab.ErrorUtils
public import Lean.Elab.Quotation
public import Lean.Elab.Tactic.Ext
public import Lean.Elab.Tactic.Induction
public import Lean.Elab.Tactic.RenameInaccessibles
public import Lean.Language.Lean.Util
public import Lean.Linter.UnusedVariables
public import Lean.Meta.Constructions.CtorIdx
public import Lean.Meta.Constructions.SparseCasesOn
public import Lean.Meta.HasNotBit
public import Lean.Meta.HaveTelescope
public import Lean.Meta.Match.CaseArraySizes
public import Lean.Meta.Match.CaseValues
public import Lean.Meta.Match.NamedPatterns
public import Lean.Meta.Match.SimpH
public import Lean.Meta.Match.SolveOverlap
public import Lean.Meta.MethodSpecs
public import Lean.Meta.NatInstTesters
public import Lean.Meta.PPBinder
public import Lean.Meta.ProdN
public import Lean.Meta.StringLitProof
public import Lean.Meta.Tactic.ExposeNames
public import Lean.Meta.Tactic.FunIndCollect
public import Lean.PrettyPrinter.Delaborator.DeclWithSig
public import Lean.Runtime
public import Lean.Server.CodeActions
public import Lean.Util.UnusedBinders
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.GRewrite
public import Std.Time.Format
public import Std.Time.Zoned.Database.PosixTz

@[expose] public section


/-!
UNCOMPILED PROOF-BODY DRAFT. At most six ordered prime triples per product;
repeated primes are permitted. The bound is not claimed for composite triples.
The coefficient-energy lemmas are finite and need no divisor-function estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
namespace Item1PrimeTripleFibers

abbrev Triple := ℕ × ℕ × ℕ

def product (t : Triple) : ℕ := t.1*t.2.1*t.2.2

def allPrime (t : Triple) : Prop :=
  t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime

def orbit (t : Triple) : Finset Triple :=
  {(t.1,t.2.1,t.2.2), (t.1,t.2.2,t.2.1),
   (t.2.1,t.1,t.2.2), (t.2.1,t.2.2,t.1),
   (t.2.2,t.1,t.2.1), (t.2.2,t.2.1,t.1)}

theorem pair_cases (p q a b : ℕ) (hp : p.Prime) (ha : a.Prime) (hb : b.Prime)
    (h : p*q=a*b) : (p=a ∧ q=b) ∨ (p=b ∧ q=a) := by
  have hd : p ∣ a*b := ⟨q,h.symm⟩
  rcases hp.dvd_mul.mp hd with hpa | hpb
  · have hap : a=p := (ha.dvd_iff_eq hp.ne_one).mp hpa
    subst a
    exact Or.inl ⟨rfl,mul_left_cancel₀ hp.ne_zero h⟩
  · have hbp : b=p := (hb.dvd_iff_eq hp.ne_one).mp hpb
    subst b
    have hh : p*q=p*a := by simpa only [mul_comm a p] using h
    exact Or.inr ⟨rfl,mul_left_cancel₀ hp.ne_zero hh⟩

theorem member_orbit_of_product_eq (t a : Triple) (ht : allPrime t)
    (ha : allPrime a) (h : product t=product a) : t ∈ orbit a := by
  rcases t with ⟨p,q,r⟩
  rcases a with ⟨a,b,c⟩
  rcases ht with ⟨hp,hq,hr⟩
  rcases ha with ⟨ha,hb,hc⟩
  change p*q*r=a*b*c at h
  have hd : p ∣ (a*b)*c := ⟨q*r, by simpa only [mul_assoc] using h.symm⟩
  rcases hp.dvd_mul.mp hd with hab | hpc
  · rcases hp.dvd_mul.mp hab with hpa | hpb
    · have hap : a=p := (ha.dvd_iff_eq hp.ne_one).mp hpa
      subst a
      have he : q*r=b*c := mul_left_cancel₀ hp.ne_zero (by simpa only [mul_assoc] using h)
      rcases pair_cases q r b c hq hb hc he with ⟨hqb,hrc⟩ | ⟨hqc,hrb⟩
      · subst q; subst r; simp [orbit]
      · subst q; subst r; simp [orbit]
    · have hbp : b=p := (hb.dvd_iff_eq hp.ne_one).mp hpb
      subst b
      have he : q*r=a*c := by
        apply mul_left_cancel₀ hp.ne_zero
        calc
          p*(q*r)=a*p*c := by simpa only [mul_assoc] using h
          _=p*(a*c) := by ring
      rcases pair_cases q r a c hq ha hc he with ⟨hqa,hrc⟩ | ⟨hqc,hra⟩
      · subst q; subst r; simp [orbit]
      · subst q; subst r; simp [orbit]
  · have hcp : c=p := (hc.dvd_iff_eq hp.ne_one).mp hpc
    subst c
    have he : q*r=a*b := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p*(q*r)=a*b*p := by simpa only [mul_assoc] using h
        _=p*(a*b) := by ring
    rcases pair_cases q r a b hq ha hb he with ⟨hqa,hrb⟩ | ⟨hqb,hra⟩
    · subst q; subst r; simp [orbit]
    · subst q; subst r; simp [orbit]

theorem orbit_card_le (a : Triple) : (orbit a).card ≤ 6 := by
  exact Finset.card_le_six

/-- Every finite prime-only product fiber has at most six members. -/
theorem fiber_card_le (S : Finset Triple) (m : ℕ)
    (hprime : ∀ t ∈ S, allPrime t) (hprod : ∀ t ∈ S, product t=m) :
    S.card ≤ 6 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have hsub : S ⊆ orbit a := by
      intro t ht
      exact member_orbit_of_product_eq t a (hprime t ht) (hprime a ha)
        ((hprod t ht).trans (hprod a ha).symm)
    exact (Finset.card_le_card hsub).trans (orbit_card_le a)
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hz]

theorem fiber_weight_le (S : Finset Triple) (m : ℕ) (ell : ℝ) (w : Triple → ℝ)
    (hl : 0 ≤ ell) (hprime : ∀ t ∈ S, allPrime t)
    (hprod : ∀ t ∈ S, product t=m) (hw : ∀ t ∈ S, w t ≤ ell^3) :
    (∑ t ∈ S, w t) ≤ 6*ell^3 := by
  have hc : (S.card : ℝ) ≤ 6 := by exact_mod_cast fiber_card_le S m hprime hprod
  calc
    (∑ t ∈ S, w t) ≤ ∑ t ∈ S, ell^3 := Finset.sum_le_sum hw
    _ = (S.card : ℝ)*ell^3 := by simp
    _ ≤ 6*ell^3 := mul_le_mul_of_nonneg_right hc (by positivity)

/-- A real scalar estimate used after collecting the actual prime triples. -/
theorem coefficient_square_le (X ell n c : ℝ) (hX : 0 < X) (hl : 0 ≤ ell)
    (hn : X/8 ≤ n) (hc0 : 0 ≤ c) (hc : c ≤ 6*ell^3) :
    (c/n)^2 ≤ (48*ell^3/X)*(c/n) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hb0 : 0 ≤ c/n := div_nonneg hc0 hnpos.le
  have hb : c/n ≤ 48*ell^3/X := by
    calc
      c/n ≤ (6*ell^3)/n := div_le_div_of_nonneg_right hc hnpos.le
      _ ≤ (6*ell^3)/(X/8) := div_le_div_of_nonneg_left (by positivity) (by positivity) hn
      _ = 48*ell^3/X := by field_simp <;> ring
  calc
    (c/n)^2=(c/n)*(c/n) := by ring
    _ ≤ (48*ell^3/X)*(c/n) := mul_le_mul_of_nonneg_right hb hb0

/-- Uniform actual-coefficient energy once the elementary reciprocal mass is inserted. -/
theorem coefficient_energy_le (S : Finset ℕ) (X ell : ℝ) (c : ℕ → ℝ)
    (hX : 0 < X) (hl : 0 ≤ ell)
    (hn : ∀ n ∈ S, X/8 ≤ (n:ℝ))
    (hc0 : ∀ n ∈ S, 0 ≤ c n) (hc : ∀ n ∈ S, c n ≤ 6*ell^3)
    (hmass : (∑ n ∈ S, c n/(n:ℝ)) ≤ 32*ell^3) :
    (∑ n ∈ S, (c n/(n:ℝ))^2) ≤ 1536*ell^6/X := by
  calc
    (∑ n ∈ S, (c n/(n:ℝ))^2) ≤
        ∑ n ∈ S, (48*ell^3/X)*(c n/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro n hnS
      exact coefficient_square_le X ell n (c n) hX hl (hn n hnS) (hc0 n hnS) (hc n hnS)
    _ = (48*ell^3/X)*(∑ n ∈ S, c n/(n:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (48*ell^3/X)*(32*ell^3) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 1536*ell^6/X := by ring

#print axioms fiber_card_le
#print axioms coefficient_energy_le
run_cmd do
  for n in [``pair_cases, ``member_orbit_of_product_eq, ``orbit_card_le,
      ``fiber_card_le, ``fiber_weight_le, ``coefficient_square_le, ``coefficient_energy_le] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
end Item1PrimeTripleFibers

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1PrimeTripleFibers.pair_cases,
    ``Item1PrimeTripleFibers.member_orbit_of_product_eq,
    ``Item1PrimeTripleFibers.orbit_card_le,
    ``Item1PrimeTripleFibers.fiber_card_le,
    ``Item1PrimeTripleFibers.fiber_weight_le,
    ``Item1PrimeTripleFibers.coefficient_square_le,
    ``Item1PrimeTripleFibers.coefficient_energy_le] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PrimeTripleFibers: 7 original theorem guards passed."
