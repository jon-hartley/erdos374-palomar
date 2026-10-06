module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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


/-!
UNCOMPILED PROOF-BODY DRAFT, source-merge copy.
Adapted from the supplied physical-pruning atom lemma; not a new classical result. A finite nonnegative sharp-window first-mean
estimate, independent of Fourier analysis and prime distribution.
All measures are Lebesgue measure. Product collisions remain separate indices.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Item1SharpAtomMean

/-- Exact endpoint convention: m ≤ x < m/(1-eta). -/
def atom (eta m w : ℝ) : ℝ → ℝ :=
  (Ico m (m/(1-eta))).indicator (fun x => w/(eta*x))

theorem window_iff (eta m x : ℝ) (heta : eta < 1) :
    ((1-eta)*x < m ∧ m ≤ x) ↔ x ∈ Ico m (m/(1-eta)) := by
  have hq : 0 < 1-eta := by linarith
  simp only [mem_Ico]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨h₂, (lt_div_iff₀ hq).mpr (by simpa [mul_comm] using h₁)⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨by simpa [mul_comm] using (lt_div_iff₀ hq).mp h₂, h₁⟩

theorem atom_literal (eta m w x : ℝ) (heta : eta < 1) :
    atom eta m w x =
      if (1-eta)*x < m ∧ m ≤ x then w/(eta*x) else 0 := by
  classical
  simp only [atom, Set.indicator_apply, window_iff eta m x heta]

theorem atom_measurable (eta m w : ℝ) : Measurable (atom eta m w) := by
  unfold atom
  apply Measurable.indicator _ measurableSet_Ico
  fun_prop

theorem atom_nonneg (eta m w : ℝ) (heta : 0 < eta) (hm : 0 < m)
    (hw : 0 ≤ w) (x : ℝ) : 0 ≤ atom eta m w x := by
  classical
  unfold atom
  by_cases hx : x ∈ Ico m (m/(1-eta))
  · rw [Set.indicator_of_mem hx]
    exact div_nonneg hw (mul_nonneg heta.le (hm.le.trans hx.1))
  · simp only [Set.indicator_of_notMem hx, le_refl]

def majorant (eta m w : ℝ) : ℝ → ℝ :=
  (Ico m (m/(1-eta))).indicator (fun _ => w/(eta*m))

theorem atom_le_majorant (eta m w : ℝ) (heta : 0 < eta) (hm : 0 < m)
    (hw : 0 ≤ w) (x : ℝ) : atom eta m w x ≤ majorant eta m w x := by
  classical
  unfold atom majorant
  by_cases hx : x ∈ Ico m (m/(1-eta))
  · simp only [Set.indicator_of_mem hx]
    exact div_le_div_of_nonneg_left hw (mul_pos heta hm)
      (mul_le_mul_of_nonneg_left hx.1 heta.le)
  · simp only [Set.indicator_of_notMem hx, le_refl]

theorem majorant_nonneg (eta m w : ℝ) (heta : 0 < eta) (hm : 0 < m)
    (hw : 0 ≤ w) (x : ℝ) : 0 ≤ majorant eta m w x := by
  classical
  unfold majorant
  by_cases hx : x ∈ Ico m (m/(1-eta))
  · rw [Set.indicator_of_mem hx]
    positivity
  · simp only [Set.indicator_of_notMem hx, le_refl]

theorem majorant_integrable (eta m w : ℝ) : Integrable (majorant eta m w) := by
  have hc : IntegrableOn (fun _ : ℝ => w/(eta*m)) (Ico m (m/(1-eta))) := by
    exact integrable_const _
  exact hc.integrable_indicator measurableSet_Ico

/-- Qualitative integrability is proved separately; no default-zero integral trick. -/
theorem atom_integrable (eta m w : ℝ) (heta : 0 < eta) (hm : 0 < m)
    (hw : 0 ≤ w) : Integrable (atom eta m w) := by
  apply (majorant_integrable eta m w).mono'
    (atom_measurable eta m w).aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (atom_nonneg eta m w heta hm hw x)]
    using atom_le_majorant eta m w heta hm hw x

theorem majorant_integral (eta m w : ℝ) (heta : 0 < eta)
    (heta1 : eta < 1) (hm : 0 < m) :
    (∫ x : ℝ, majorant eta m w x) = w/(1-eta) := by
  have hq : 0 < 1-eta := by linarith
  have hml : m ≤ m/(1-eta) := by
    apply (le_div_iff₀ hq).mpr
    nlinarith [mul_nonneg hm.le heta.le]
  unfold majorant
  rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico_of_le hml]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt heta, ne_of_gt hm, ne_of_gt hq]
  <;> ring

/-- Uniform bound for an individual atom, including products outside [X,2X]. -/
theorem atom_first_mean (X eta m w : ℝ) (hX : 0 < X)
    (heta : 0 < eta) (heta2 : eta ≤ 1/2) (hm : 0 < m) (hw : 0 ≤ w) :
    (∫ x in Icc X (2*X), atom eta m w x)/X ≤ 4*w/m := by
  have heta1 : eta < 1 := by linarith
  have hq : 0 < 1-eta := by linarith
  by_cases hmX : m ≤ 2*X
  · have hcompare :
        (∫ x in Icc X (2*X), atom eta m w x) ≤ w/(1-eta) := by
      calc
        (∫ x in Icc X (2*X), atom eta m w x) ≤
            ∫ x in Icc X (2*X), majorant eta m w x := by
          apply setIntegral_mono_of_nonneg
          · intro x hx
            exact atom_nonneg eta m w heta hm hw x
          · intro x hx
            exact atom_le_majorant eta m w heta hm hw x
          · exact (majorant_integrable eta m w).integrableOn
        _ ≤ ∫ x : ℝ, majorant eta m w x :=
          setIntegral_le_integral (majorant_integrable eta m w)
            (Filter.Eventually.of_forall (majorant_nonneg eta m w heta hm hw))
        _ = w/(1-eta) := majorant_integral eta m w heta heta1 hm
    have hden : m ≤ 4*((1-eta)*X) := by nlinarith
    calc
      (∫ x in Icc X (2*X), atom eta m w x)/X ≤ (w/(1-eta))/X :=
        div_le_div_of_nonneg_right hcompare hX.le
      _ = w/((1-eta)*X) := by rw [div_div]
      _ ≤ 4*w/m := by
        apply (div_le_div_iff₀ (mul_pos hq hX) hm).mpr
        have hh := mul_le_mul_of_nonneg_left hden hw
        nlinarith
  · have hz : (∫ x in Icc X (2*X), atom eta m w x) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      unfold atom
      apply Set.indicator_of_notMem
      intro hmemb
      exact hmX (hmemb.1.trans hx.2)
    rw [hz, zero_div]
    positivity

/-- Ordered representations can be the indexing type; repeated products are allowed. -/
theorem finite_first_mean {ι : Type*} (S : Finset ι) (m w : ι → ℝ)
    (X eta : ℝ) (hX : 0 < X) (heta : 0 < eta) (heta2 : eta ≤ 1/2)
    (hm : ∀ a ∈ S, 0 < m a) (hw : ∀ a ∈ S, 0 ≤ w a) :
    (∫ x in Icc X (2*X), ∑ a ∈ S, atom eta (m a) (w a) x)/X ≤
      4*∑ a ∈ S, w a/m a := by
  rw [integral_finsetSum S (fun a ha =>
    (atom_integrable eta (m a) (w a) heta (hm a ha) (hw a ha)).integrableOn)]
  rw [Finset.sum_div]
  calc
    (∑ a ∈ S, (∫ x in Icc X (2*X), atom eta (m a) (w a) x)/X) ≤
        ∑ a ∈ S, 4*w a/m a := by
      apply Finset.sum_le_sum
      intro a ha
      exact atom_first_mean X eta (m a) (w a) hX heta heta2 (hm a ha) (hw a ha)
    _ = 4*∑ a ∈ S, w a/m a := by simp only [Finset.mul_sum, mul_div_assoc]


end Item1SharpAtomMean

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1SharpAtomMean.window_iff,
    ``Item1SharpAtomMean.atom_literal,
    ``Item1SharpAtomMean.atom_measurable,
    ``Item1SharpAtomMean.atom_nonneg,
    ``Item1SharpAtomMean.atom_le_majorant,
    ``Item1SharpAtomMean.majorant_nonneg,
    ``Item1SharpAtomMean.majorant_integrable,
    ``Item1SharpAtomMean.atom_integrable,
    ``Item1SharpAtomMean.majorant_integral,
    ``Item1SharpAtomMean.atom_first_mean,
    ``Item1SharpAtomMean.finite_first_mean] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1SharpAtomMean: 11 original theorem guards passed."
