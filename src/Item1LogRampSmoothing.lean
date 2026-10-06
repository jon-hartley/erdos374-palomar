module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
public import ImportGraph.Imports.ImportGraph
public import ImportGraph.Lean.Environment
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
public import Init.Data.List.Nat.Perm
public import Init.Data.List.Nat.Prod
public import Init.Data.List.Nat.Range
public import Init.Data.List.Nat.Sum
public import Init.Data.List.Nat.TakeDrop
public import Init.Data.List.Pairwise
public import Init.Data.List.Range
public import Init.Data.List.Sort
public import Init.Data.List.Sublist
public import Init.Data.List.TakeDrop
public import Init.Data.List.Zip
public import Init.Data.Nat.Power2.Lemmas
public import Init.Data.Nat.Simproc
public import Init.Data.Option.Array
public import Init.Data.Option.Function
public import Init.Data.Option.List
public import Init.Data.Prod
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
public import Lean.Elab.ComputedFields
public import Lean.Elab.ConfigEval.Util
public import Lean.Elab.DeprecatedArg
public import Lean.Elab.DeprecatedSyntax
public import Lean.Elab.DocString
public import Lean.Elab.ErrorUtils
public import Lean.Elab.PreDefinition.EqnsUtils
public import Lean.Elab.Quotation
public import Lean.Elab.Tactic.Grind.Anchor
public import Lean.Elab.Tactic.Grind.Param
public import Lean.Elab.Tactic.Induction
public import Lean.Elab.Tactic.RenameInaccessibles
public import Lean.Language.Lean.Util
public import Lean.Linter.MissingDocs
public import Lean.Meta.Constructions.CtorElim
public import Lean.Meta.Constructions.CtorIdx
public import Lean.Meta.CtorIdxHInj
public import Lean.Meta.HasNotBit
public import Lean.Meta.HaveTelescope
public import Lean.Meta.IndPredBelow
public import Lean.Meta.Injective
public import Lean.Meta.Match.CaseArraySizes
public import Lean.Meta.Match.CaseValues
public import Lean.Meta.Match.MatcherApp
public import Lean.Meta.Match.NamedPatterns
public import Lean.Meta.Match.SimpH
public import Lean.Meta.Match.SolveOverlap
public import Lean.Meta.MethodSpecs
public import Lean.Meta.NatInstTesters
public import Lean.Meta.NatTable
public import Lean.Meta.PPBinder
public import Lean.Meta.ProdN
public import Lean.Meta.SameCtorUtils
public import Lean.Meta.StringLitProof
public import Lean.Meta.Sym.AbstractS
public import Lean.Meta.Sym.Arith.EvalNum
public import Lean.Meta.Sym.Arith.Poly
public import Lean.Meta.Sym.Eta
public import Lean.Meta.Sym.InstantiateMVarsS
public import Lean.Meta.Sym.InstantiateS
public import Lean.Meta.Sym.IsClass
public import Lean.Meta.Sym.LooseBVarsS
public import Lean.Meta.Sym.MaxFVar
public import Lean.Meta.Sym.Offset
public import Lean.Meta.Sym.ProofInstInfo
public import Lean.Meta.Sym.Simp.Attr
public import Lean.Meta.Sym.Simp.DiscrTree
public import Lean.Meta.Tactic.CasesOnStuckLHS
public import Lean.Meta.Tactic.Grind.AC.DenoteExpr
public import Lean.Meta.Tactic.Grind.AC.PP
public import Lean.Meta.Tactic.Grind.AC.Seq
public import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
public import Lean.Meta.Tactic.Grind.Arith.CommRing.PP
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
public import Lean.Meta.Tactic.Grind.Arith.FieldNormNum
public import Lean.Meta.Tactic.Grind.Arith.Insts
public import Lean.Meta.Tactic.Grind.Arith.IsRelevant
public import Lean.Meta.Tactic.Grind.Arith.Linear.Model
public import Lean.Meta.Tactic.Grind.Arith.Linear.PP
public import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
public import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
public import Lean.Meta.Tactic.Grind.Arith.Linear.Util
public import Lean.Meta.Tactic.Grind.Arith.Linear.Var
public import Lean.Meta.Tactic.Grind.Arith.ModelUtil
public import Lean.Meta.Tactic.Grind.Arith.Simproc
public import Lean.Meta.Tactic.Grind.Beta
public import Lean.Meta.Tactic.Grind.CasesMatch
public import Lean.Meta.Tactic.Grind.CastLike
public import Lean.Meta.Tactic.Grind.CollectParams
public import Lean.Meta.Tactic.Grind.Core
public import Lean.Meta.Tactic.Grind.Ctor
public import Lean.Meta.Tactic.Grind.CtorIdx
public import Lean.Meta.Tactic.Grind.EMatch
public import Lean.Meta.Tactic.Grind.EMatchAction
public import Lean.Meta.Tactic.Grind.EMatchDiagnostics
public import Lean.Meta.Tactic.Grind.EMatchTheoremParam
public import Lean.Meta.Tactic.Grind.EMatchTheoremPtr
public import Lean.Meta.Tactic.Grind.EqResolution
public import Lean.Meta.Tactic.Grind.Finish
public import Lean.Meta.Tactic.Grind.ForallProp
public import Lean.Meta.Tactic.Grind.Injection
public import Lean.Meta.Tactic.Grind.Internalize
public import Lean.Meta.Tactic.Grind.Inv
public import Lean.Meta.Tactic.Grind.LawfulEqCmp
public import Lean.Meta.Tactic.Grind.MarkAccessible
public import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
public import Lean.Meta.Tactic.Grind.MatchCond
public import Lean.Meta.Tactic.Grind.MatchDiscrOnly
public import Lean.Meta.Tactic.Grind.OrderInsts
public import Lean.Meta.Tactic.Grind.PP
public import Lean.Meta.Tactic.Grind.Parser
public import Lean.Meta.Tactic.Grind.Proj
public import Lean.Meta.Tactic.Grind.PropagateInj
public import Lean.Meta.Tactic.Grind.ReflCmp
public import Lean.Meta.Tactic.Grind.Simp
public import Lean.Meta.Tactic.Grind.SimpUtil
public import Lean.Meta.Tactic.Grind.Solve
public import Lean.Meta.Tactic.Grind.Split
public import Lean.PrettyPrinter.Delaborator.DeclWithSig
public import Lean.Runtime
public import Lean.Server.CodeActions
public import Lean.Util.ParamMinimizer
public import Lean.Util.UnusedBinders
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.DSimpPercent
public import Mathlib.Tactic.InferParam
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology
public import Std.Data.DHashMap.IteratorLemmas
public import Std.Data.DTreeMap.Internal.Lemmas
public import Std.Data.ExtHashSet.Lemmas
public import Std.Data.ExtTreeSet.Lemmas
public import Std.Data.HashMap.RawLemmas
public import Std.Data.HashSet.Lemmas
public import Std.Data.TreeMap.Lemmas
public import Std.Data.TreeSet.Lemmas
public import Std.Time.Format
public import Std.Time.Zoned.Database.PosixTz

@[expose] public section


/-!
Elementary finite smoothing for the literal half-open dyadic block.
The smoothing is auxiliary to the pointwise cap; it does not change the source
window or its full-Mangoldt reference. No asymptotic cap is a premise here.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace Item1LogRampSmoothing

def ramp (δ u : ℝ) : ℝ := min 1 (max 0 (u/δ))
def weight («λ» δ u : ℝ) : ℝ := ramp δ u-ramp δ (u-«λ»)
def sharp («λ» u : ℝ) : ℝ := if 0 ≤ u ∧ u < «λ» then 1 else 0
def Edge («λ» δ u : ℝ) : Prop := u ∈ Set.Icc 0 δ ∨ u ∈ Set.Icc «λ» («λ»+δ)

instance («λ» δ u : ℝ) : Decidable (Edge «λ» δ u) := Classical.propDecidable _

theorem ramp_nonneg (δ u : ℝ) : 0 ≤ ramp δ u :=
  le_min (by norm_num) (le_max_left _ _)

theorem ramp_le_one (δ u : ℝ) : ramp δ u ≤ 1 := min_le_left _ _

theorem ramp_mono (δ u v : ℝ) (hδ : 0 < δ) (huv : u ≤ v) :
    ramp δ u ≤ ramp δ v := by
  unfold ramp
  gcongr

theorem ramp_zero (δ u : ℝ) (hδ : 0 < δ) (hu : u ≤ 0) : ramp δ u = 0 := by
  have hh : u/δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hδ.le
  simp [ramp, max_eq_left hh]

theorem ramp_one (δ u : ℝ) (hδ : 0 < δ) (hu : δ ≤ u) : ramp δ u = 1 := by
  have hh : (1:ℝ) ≤ u/δ := (le_div_iff₀ hδ).mpr (by simpa using hu)
  exact min_eq_left (hh.trans (le_max_right _ _))

theorem weight_bounds («λ» δ u : ℝ) («hλ» : 0 ≤ «λ») (hδ : 0 < δ) :
    0 ≤ weight «λ» δ u ∧ weight «λ» δ u ≤ 1 := by
  have hm := ramp_mono δ (u-«λ») u hδ (by linarith)
  have hn := ramp_nonneg δ (u-«λ»)
  have hh := ramp_le_one δ u
  unfold weight
  constructor <;> linarith

theorem weight_left («λ» δ u : ℝ) («hλ» : 0 ≤ «λ») (hδ : 0 < δ) (hu : u ≤ 0) :
    weight «λ» δ u = 0 := by
  simp [weight, ramp_zero δ u hδ hu, ramp_zero δ (u-«λ») hδ (by linarith)]

theorem weight_right («λ» δ u : ℝ) («hλ» : 0 ≤ «λ») (hδ : 0 < δ)
    (hu : «λ»+δ ≤ u) : weight «λ» δ u = 0 := by
  simp [weight, ramp_one δ u hδ (by linarith), ramp_one δ (u-«λ») hδ (by linarith)]

theorem weight_core («λ» δ u : ℝ) (hδ : 0 < δ) (hlo : δ ≤ u) (hhi : u ≤ «λ») :
    weight «λ» δ u = 1 := by
  simp [weight, ramp_one δ u hδ hlo, ramp_zero δ (u-«λ») hδ (by linarith)]

theorem sharp_bounds («λ» u : ℝ) : 0 ≤ sharp «λ» u ∧ sharp «λ» u ≤ 1 := by
  unfold sharp
  split_ifs <;> norm_num

/-- Exact agreement outside the two transition strips; endpoints are included
in those strips, rather than incorrectly dropped from the Mangoldt block. -/
theorem weight_eq_sharp_off_edge («λ» δ u : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    (ho : ¬ Edge «λ» δ u) : weight «λ» δ u = sharp «λ» u := by
  have «hλ» : 0 ≤ «λ» := by linarith
  by_cases hlo : u < 0
  · rw [weight_left «λ» δ u «hλ» hδ hlo.le]
    simp [sharp, not_le.mpr hlo]
  have hu0 : 0 ≤ u := le_of_not_gt hlo
  by_cases hhi : «λ»+δ < u
  · rw [weight_right «λ» δ u «hλ» hδ hhi.le]
    have hn : ¬ u < «λ» := by linarith
    simp [sharp,hn]
  have huhi : u ≤ «λ»+δ := le_of_not_gt hhi
  have hdu : δ < u := by
    by_contra hh
    exact ho (Or.inl ⟨hu0,le_of_not_gt hh⟩)
  have hul : u < «λ» := by
    by_contra hh
    exact ho (Or.inr ⟨le_of_not_gt hh,huhi⟩)
  rw [weight_core «λ» δ u hδ hdu.le hul.le]
  simp [sharp,hu0,hul]

theorem difference_bound («λ» δ u : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ») :
    |sharp «λ» u-weight «λ» δ u| ≤ if Edge «λ» δ u then 1 else 0 := by
  by_cases hh : Edge «λ» δ u
  · rw [ite_eq_left hh]
    have hs := sharp_bounds «λ» u
    have hw := weight_bounds «λ» δ u (by linarith) hδ
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · rw [ite_eq_right hh,weight_eq_sharp_off_edge «λ» δ u hδ «hδλ» hh]
    simp

/-- A generic finite coefficient bound, valid for complex coefficients and
repeated positions. The caller must still instantiate its actual edge count. -/
theorem finite_desmoothing (s : Finset ℕ) (a : ℕ → ℂ) (u : ℕ → ℝ)
    («λ» δ M : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ») (hM : 0 ≤ M)
    (ha : ∀ n ∈ s, ‖a n‖ ≤ M) :
    ‖(∑ n ∈ s, a n*(sharp «λ» (u n):ℂ))-
      (∑ n ∈ s, a n*(weight «λ» δ (u n):ℂ))‖ ≤
      ((s.filter (fun n => Edge «λ» δ (u n))).card:ℝ)*M := by
  classical
  have hid : (∑ n ∈ s, a n*(sharp «λ» (u n):ℂ))-
      (∑ n ∈ s, a n*(weight «λ» δ (u n):ℂ)) =
      ∑ n ∈ s, a n*((sharp «λ» (u n)-weight «λ» δ (u n):ℝ):ℂ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hid]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ s, if Edge «λ» δ (u n) then M else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      have hd := difference_bound «λ» δ (u n) hδ «hδλ»
      by_cases hh : Edge «λ» δ (u n)
      · rw [ite_eq_left hh] at hd ⊢
        exact (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans
          (by simpa using ha n hn)
      · rw [ite_eq_right hh] at hd ⊢
        have he : |sharp «λ» (u n)-weight «λ» δ (u n)|=0 :=
          le_antisymm hd (abs_nonneg _)
        simp [he]
    _ = ∑ n ∈ s.filter (fun n => Edge «λ» δ (u n)), M := by
      rw [Finset.sum_filter]
    _ = _ := by simp

/-- Entire-integral definition: no erroneous 0/0 convention at Mellin frequency 0. -/
def kernel («λ» δ : ℝ) (z : ℂ) : ℂ :=
  (∫ u in (0:ℝ)..«λ», Complex.exp (z*(u:ℂ))) *
    (∫ v in (0:ℝ)..δ, Complex.exp (z*(v:ℂ))) / (δ:ℂ)

theorem kernel_zero («λ» δ : ℝ) (hδ : δ ≠ 0) : kernel «λ» δ 0 = («λ»:ℂ) := by
  have hd : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ
  simp [kernel, intervalIntegral.integral_const, hd]

end Item1LogRampSmoothing


run_cmd do
  for target in [
``Item1LogRampSmoothing.ramp_nonneg, ``Item1LogRampSmoothing.ramp_le_one, ``Item1LogRampSmoothing.ramp_mono, ``Item1LogRampSmoothing.ramp_zero, ``Item1LogRampSmoothing.ramp_one, ``Item1LogRampSmoothing.weight_bounds, ``Item1LogRampSmoothing.weight_left, ``Item1LogRampSmoothing.weight_right, ``Item1LogRampSmoothing.weight_core, ``Item1LogRampSmoothing.sharp_bounds, ``Item1LogRampSmoothing.weight_eq_sharp_off_edge, ``Item1LogRampSmoothing.difference_bound, ``Item1LogRampSmoothing.finite_desmoothing, ``Item1LogRampSmoothing.kernel_zero
] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
#print axioms Item1LogRampSmoothing.ramp_nonneg
#print axioms Item1LogRampSmoothing.ramp_le_one
#print axioms Item1LogRampSmoothing.ramp_mono
#print axioms Item1LogRampSmoothing.ramp_zero
#print axioms Item1LogRampSmoothing.ramp_one
#print axioms Item1LogRampSmoothing.weight_bounds
#print axioms Item1LogRampSmoothing.weight_left
#print axioms Item1LogRampSmoothing.weight_right
#print axioms Item1LogRampSmoothing.weight_core
#print axioms Item1LogRampSmoothing.sharp_bounds
#print axioms Item1LogRampSmoothing.weight_eq_sharp_off_edge
#print axioms Item1LogRampSmoothing.difference_bound
#print axioms Item1LogRampSmoothing.finite_desmoothing
#print axioms Item1LogRampSmoothing.kernel_zero
