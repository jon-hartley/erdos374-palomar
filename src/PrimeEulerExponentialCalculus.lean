module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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


/-! Explicit exponential-test calculus for a later finite prime-measure
comparison. Every integral here is an ordinary real interval integral; no
arithmetic weighted-transfer estimate is asserted in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Set MeasureTheory

namespace PrimeEulerExponentialCalculus

def test (A x : ℝ) : ℝ := exp (1-A/log x)
def moment (A x : ℝ) : ℝ := test A x*(A+log x)/(A^2*log x)
def logKernel (A : ℝ) (k : ℕ) (x : ℝ) : ℝ := test A x/(x*(log x)^k)

theorem test_pos (A x : ℝ) : 0 < test A x := exp_pos _

theorem test_hasDerivAt (A x : ℝ) (hx : 1 < x) :
    HasDerivAt (test A) (test A x*A/(x*(log x)^2)) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hl0 : log x ≠ 0 := ne_of_gt (log_pos hx)
  have hlog := hasDerivAt_log hx0
  have hh : HasDerivAt (fun y : ℝ => 1-A/log y) (A/(x*(log x)^2)) x := by
    convert! (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_const x A).div hlog hl0) using 1
    field_simp
    ring
  convert! hh.exp using 1
  unfold test
  ring

theorem derivative_nonneg (A x : ℝ) (hA : 0 ≤ A) (hx : 1 < x) :
    0 ≤ test A x*A/(x*(log x)^2) := by
  exact div_nonneg (mul_nonneg (test_pos A x).le hA)
    (mul_nonneg (zero_lt_one.trans hx).le (sq_nonneg _))

theorem test_continuousOn (A a b : ℝ) (ha : 1 < a) :
    ContinuousOn (test A) (Icc a b) := by
  intro x hx
  exact (test_hasDerivAt A x (ha.trans_le hx.1)).continuousAt.continuousWithinAt

theorem test_continuousOn_two (A b : ℝ) : ContinuousOn (test A) (Icc 2 b) :=
  test_continuousOn A 2 b (by norm_num)

theorem first_antiderivative_hasDerivAt (A x : ℝ) (hA : 0 < A) (hx : 1 < x) :
    HasDerivAt (fun y => test A y/A) (logKernel A 2 x) x := by
  convert! (test_hasDerivAt A x hx).div_const A using 1
  unfold logKernel
  field_simp

theorem moment_hasDerivAt (A x : ℝ) (hA : 0 < A) (hx : 1 < x) :
    HasDerivAt (moment A) (logKernel A 3 x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hl0 : log x ≠ 0 := ne_of_gt (log_pos hx)
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hlog := hasDerivAt_log hx0
  have hden : A^2*log x ≠ 0 := mul_ne_zero (pow_ne_zero _ hA0) hl0
  convert! ((test_hasDerivAt A x hx).mul ((hasDerivAt_const x A).add hlog)).div
    (hlog.const_mul (A^2)) hden using 1
  dsimp [logKernel]
  field_simp
  ring

theorem moment_nonneg (A x : ℝ) (hA : 0 < A) (hx : 1 < x) :
    0 ≤ moment A x := by
  unfold moment
  exact div_nonneg (mul_nonneg (test_pos A x).le (add_pos hA (log_pos hx)).le)
    (mul_pos (sq_pos_of_pos hA) (log_pos hx)).le

theorem logKernel_nonneg (A x : ℝ) (k : ℕ) (hx : 1 < x) :
    0 ≤ logKernel A k x :=
  div_nonneg (test_pos A x).le
    (mul_nonneg (zero_lt_one.trans hx).le (pow_nonneg (log_pos hx).le _))

theorem logKernel_continuousOn (A a b : ℝ) (k : ℕ) (ha : 1 < a) :
    ContinuousOn (logKernel A k) (Icc a b) := by
  intro x hx
  have hxx : 1 < x := ha.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hxx)
  apply ContinuousAt.continuousWithinAt
  apply (test_hasDerivAt A x hxx).continuousAt.div
    (continuousAt_id.mul ((continuousAt_log hx0).pow k))
  exact ne_of_gt (mul_pos (zero_lt_one.trans hxx) (pow_pos (log_pos hxx) _))

theorem logKernel_intervalIntegrable (A a b : ℝ) (k : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (logKernel A k) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact logKernel_continuousOn A a b k (by linarith)

theorem integral_log_sq_eq (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, test A x/(x*(log x)^2)) = test A b/A - test A a/A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact first_antiderivative_hasDerivAt A x hA (by linarith [hx.1])
  · exact logKernel_intervalIntegrable A a b 2 ha hab

theorem integral_log_cube_eq (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, test A x/(x*(log x)^3)) = moment A b - moment A a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact moment_hasDerivAt A x hA (by linarith [hx.1])
  · exact logKernel_intervalIntegrable A a b 3 ha hab

theorem integral_log_sq_le (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, test A x/(x*(log x)^2)) ≤ test A b/A := by
  rw [integral_log_sq_eq A a b hA ha hab]
  exact sub_le_self _ (div_nonneg (test_pos A a).le hA.le)

theorem integral_log_cube_le (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, test A x/(x*(log x)^3)) ≤ moment A b := by
  rw [integral_log_cube_eq A a b hA ha hab]
  exact sub_le_self _ (moment_nonneg A a hA (by linarith))

run_cmd do
  for decl in [``test_pos, ``test_hasDerivAt, ``derivative_nonneg, ``test_continuousOn,
      ``test_continuousOn_two, ``first_antiderivative_hasDerivAt, ``moment_hasDerivAt,
      ``moment_nonneg, ``logKernel_nonneg, ``logKernel_continuousOn,
      ``logKernel_intervalIntegrable, ``integral_log_sq_eq, ``integral_log_cube_eq,
      ``integral_log_sq_le, ``integral_log_cube_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "PRIME EULER EXPONENTIAL TEST CALCULUS: STANDARD AXIOMS ONLY"

end PrimeEulerExponentialCalculus
end

end
