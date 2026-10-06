module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.DSimpPercent
public import Mathlib.Tactic.InferParam
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


/-! v6: extract the entire moment surplus from the FIRST factor.
UNCOMPILED DRAFT. Only nonnegative moment algebra and integration are proved
here. No pointwise prime-polynomial estimate is declared or assumed as an axiom.
The integrated lemma exposes its pointwise-smallness hypothesis explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open MeasureTheory Set
namespace SourceFirstFactorSaving

def firstWeight (_A B C : ℝ) : ℝ := 1-2/B-2/C

def extracted (A B C : ℝ) : ℝ := 2-A*firstWeight A B C

theorem weight_data (A B C : ℝ) (hA : 4 ≤ A) (hB : 4 ≤ B) (hC : 4 ≤ C)
    (hS : (2001/2000:ℝ) ≤ 2/A+2/B+2/C) :
    0 ≤ firstWeight A B C ∧ firstWeight A B C ≤ 1 ∧
      0 ≤ 2/B ∧ 2/B ≤ 1 ∧ 0 ≤ 2/C ∧ 2/C ≤ 1 ∧
      firstWeight A B C+2/B+2/C=1 ∧
      (1/500:ℝ) ≤ extracted A B C ∧ extracted A B C ≤ 2 := by
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hCp : 0 < C := by linarith
  have hb0 : 0 ≤ 2/B := by positivity
  have hc0 : 0 ≤ 2/C := by positivity
  have hb1 : 2/B ≤ (1/2:ℝ) := (div_le_iff₀ hBp).mpr (by linarith)
  have hc1 : 2/C ≤ (1/2:ℝ) := (div_le_iff₀ hCp).mpr (by linarith)
  have hw0 : 0 ≤ firstWeight A B C := by unfold firstWeight; linarith
  have hw1 : firstWeight A B C ≤ 1 := by unfold firstWeight; linarith
  have he : extracted A B C = A*(2/A+2/B+2/C-1) := by
    unfold extracted firstWeight
    field_simp
    <;> ring
  have hm := mul_le_mul_of_nonneg_left hS hAp.le
  have htwo : A*(2/A) = 2 := by field_simp
  have halow : (1/500:ℝ) ≤ extracted A B C := by
    rw [he]
    nlinarith [htwo]
  refine ⟨hw0,hw1,hb0,by linarith,hc0,by linarith,?_,halow,?_⟩
  · unfold firstWeight; ring
  · unfold extracted
    nlinarith [mul_nonneg hAp.le hw0]

/-- All amplitude sizes are allowed. In particular b and c need no cap. -/
theorem scalar (a b c A B C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 4 ≤ A) (hB : 4 ≤ B) (hC : 4 ≤ C)
    (hS : (2001/2000:ℝ) ≤ 2/A+2/B+2/C) :
    (a*b*c)^2 ≤ a^(extracted A B C)*(a^A+b^B+c^C) := by
  have hg := weight_data A B C hA hB hC hS
  by_cases haz : a=0
  · subst a
    simp only [zero_mul,zero_pow (by decide : (2:ℕ) ≠ 0)]
    positivity
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hAp : 0 ≤ a^A := Real.rpow_nonneg ha _
  have hBp : 0 ≤ b^B := Real.rpow_nonneg hb _
  have hCp : 0 ≤ c^C := Real.rpow_nonneg hc _
  have he1 : 0 ≤ firstWeight A B C := hg.1
  have he2 : 0 ≤ 2/B := hg.2.2.1
  have he3 : 0 ≤ 2/C := hg.2.2.2.2.1
  have hesum : firstWeight A B C+2/B+2/C=1 := hg.2.2.2.2.2.2.1
  have hgm := Real.geom_mean_le_arith_mean3_weighted he1 he2 he3 hAp hBp hCp hesum
  have hBne : B ≠ 0 := by linarith
  have hCne : C ≠ 0 := by linarith
  have hpowB : (b^B)^(2/B) = b^2 := by
    rw [←Real.rpow_mul hb]
    have hid : B*(2/B)=(2:ℝ) := by field_simp
    rw [hid,Real.rpow_two]
  have hpowC : (c^C)^(2/C) = c^2 := by
    rw [←Real.rpow_mul hc]
    have hid : C*(2/C)=(2:ℝ) := by field_simp
    rw [hid,Real.rpow_two]
  have hpowA : (a^A)^(firstWeight A B C) = a^(A*firstWeight A B C) :=
    (Real.rpow_mul ha _ _).symm
  rw [hpowA,hpowB,hpowC] at hgm
  have hweighted : firstWeight A B C*a^A+(2/B)*b^B+(2/C)*c^C ≤ a^A+b^B+c^C := by
    have hu := mul_le_mul_of_nonneg_right hg.2.1 hAp
    have hv := mul_le_mul_of_nonneg_right hg.2.2.2.1 hBp
    have hw := mul_le_mul_of_nonneg_right hg.2.2.2.2.2.1 hCp
    nlinarith
  have hs := mul_le_mul_of_nonneg_left (hgm.trans hweighted)
    (Real.rpow_nonneg ha (extracted A B C))
  have hid : a^(extracted A B C)*(a^(A*firstWeight A B C)*b^2*c^2)=(a*b*c)^2 := by
    rw [show a^(extracted A B C)*(a^(A*firstWeight A B C)*b^2*c^2) =
      (a^(extracted A B C)*a^(A*firstWeight A B C))*b^2*c^2 by ring,
      ←Real.rpow_add hap]
    have hsum : extracted A B C+A*firstWeight A B C=(2:ℝ) := by unfold extracted; ring
    rw [hsum,Real.rpow_two]
    ring
  simpa only [hid] using hs

/-- A single small factor pays all excess reciprocal moment. -/
theorem scalar_of_cap (a b c A B C ε : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 4 ≤ A) (hB : 4 ≤ B) (hC : 4 ≤ C)
    (hS : (2001/2000:ℝ) ≤ 2/A+2/B+2/C)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hsmall : a ≤ ε) :
    (a*b*c)^2 ≤ ε^(1/500:ℝ)*(a^A+b^B+c^C) := by
  have hg := weight_data A B C hA hB hC hS
  have hα : (1/500:ℝ) ≤ extracted A B C := hg.2.2.2.2.2.2.2.1
  have hbound : a^(extracted A B C) ≤ ε^(1/500:ℝ) := by
    calc
      _ ≤ ε^(extracted A B C) := Real.rpow_le_rpow ha hsmall (by linarith)
      _ ≤ ε^(1/500:ℝ) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hα
  exact (scalar a b c A B C ha hb hc hA hB hC hS).trans
    (mul_le_mul_of_nonneg_right hbound (by positivity))

/-- Integration pays the three moment bounds, but no caps on factors 2 or 3.
Integrability is supplied separately, not deduced from a purported estimate. -/
theorem integral_of_cap (μ : Measure ℝ) (a b c : ℝ → ℝ) (A B C ε H : ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) (hc : ∀ t, 0 ≤ c t)
    (hA : 4 ≤ A) (hB : 4 ≤ B) (hC : 4 ≤ C)
    (hS : (2001/2000:ℝ) ≤ 2/A+2/B+2/C)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : ∀ᵐ t ∂μ, a t ≤ ε)
    (hfa : Integrable (fun t => a t^A) μ)
    (hfb : Integrable (fun t => b t^B) μ)
    (hfc : Integrable (fun t => c t^C) μ)
    (hp : AEStronglyMeasurable (fun t => (a t*b t*c t)^2) μ)
    (hIa : (∫ t, a t^A ∂μ) ≤ H) (hIb : (∫ t, b t^B ∂μ) ≤ H)
    (hIc : (∫ t, c t^C ∂μ) ≤ H) :
    (∫ t, (a t*b t*c t)^2 ∂μ) ≤ 3*H*ε^(1/500:ℝ) := by
  have hmajor : Integrable (fun t => ε^(1/500:ℝ)*(a t^A+b t^B+c t^C)) μ :=
    ((hfa.add hfb).add hfc).const_mul _
  have hpoint : ∀ᵐ t ∂μ, (a t*b t*c t)^2 ≤ ε^(1/500:ℝ)*(a t^A+b t^B+c t^C) := by
    filter_upwards [hsmall] with t ht
    exact scalar_of_cap (a t) (b t) (c t) A B C ε (ha t) (hb t) (hc t)
      hA hB hC hS hε hε1 ht
  have hint : Integrable (fun t => (a t*b t*c t)^2) μ := by
    apply hmajor.mono' hp
    filter_upwards [hpoint] with t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (a t*b t*c t))] using ht
  have hh := integral_mono_ae hint hmajor hpoint
  have hfab : Integrable (fun t => a t^A+b t^B) μ := hfa.add hfb
  rw [integral_const_mul,integral_add hfab hfc,integral_add hfa hfb] at hh
  have hm := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hIa hIb) hIc)
    (Real.rpow_nonneg hε.le (1/500:ℝ))
  nlinarith

theorem log_budget (L K : ℝ) (hL : 0 < L) :
    3*(K*L^18)*(L^(-26000:ℝ))^(1/500:ℝ)=3*K/L^34 := by
  have hpower : (L^(-26000:ℝ))^(1/500:ℝ)=L^(-52:ℝ) := by
    rw [←Real.rpow_mul hL.le]
    norm_num
  have hinv : L^(-52:ℝ)=(L^52)⁻¹ := by
    rw [Real.rpow_neg hL.le]
    exact congrArg (fun r : ℝ => r⁻¹) (Real.rpow_natCast L 52)
  rw [hpower,hinv]
  field_simp
  <;> ring

#print axioms scalar_of_cap
#print axioms integral_of_cap
run_cmd do
  for n in [``weight_data,``scalar,``scalar_of_cap,``integral_of_cap,``log_budget] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "FIRST-FACTOR MOMENT EXTRACTION: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceFirstFactorSaving
