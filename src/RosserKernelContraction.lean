module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.RingTheory.PrincipalIdealDomain
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


/-! A certified numerical contraction majorant for the dimension-one,
two-step continuous Rosser tail operator. This is a scalar estimate only;
the integral comparison and the arithmetic transfer are separate results. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace RosserKernelContraction

def majorant (r : ℝ) : ℝ :=
  if r ≤ 4 then Real.exp (r-2)/r*(Real.log (3/(r-1))+1/3)
  else Real.exp 2/(r*(r-1))

theorem exp_one_le : Real.exp 1 ≤ (68/25:ℝ) := by
  exact Real.exp_one_lt_d9.le.trans (by norm_num)

theorem exp_half_le : Real.exp (1/2:ℝ) ≤ 33/20 := by
  have hh : Real.exp (1/2:ℝ)^2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hp := Real.exp_pos (1/2:ℝ)
  have hb := exp_one_le
  nlinarith

theorem exp_three_halves_le : Real.exp (3/2:ℝ) ≤ 9/2 := by
  have heq : Real.exp (3/2:ℝ) = Real.exp 1 * Real.exp (1/2:ℝ) := by
    rw [← Real.exp_add]
    norm_num
  rw [heq]
  have hh := mul_le_mul exp_one_le exp_half_le (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 68/25)
  exact hh.trans (by norm_num)

theorem exp_two_le : Real.exp 2 ≤ (15/2:ℝ) := by
  have heq : Real.exp (2:ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [heq]
  have hh := mul_le_mul exp_one_le exp_one_le (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 68/25)
  exact hh.trans (by norm_num)

theorem log_three_le : Real.log 3 ≤ (10/9:ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<3)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 10/9) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
  linarith

theorem log_two_le : Real.log 2 ≤ (7/10:ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<2)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 7/10) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
  linarith

theorem log_three_halves_le : Real.log (3/2:ℝ) ≤ 5/12 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<3/2)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 5/12) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
  linarith

theorem log_six_fifths_le : Real.log (6/5:ℝ) ≤ 3/16 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<6/5)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3/16) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
  linarith

theorem exp_div_mono (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    Real.exp (x-2)/x ≤ Real.exp (y-2)/y := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hlin : y ≤ x*(1+(y-x)) := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hxy)]
  have hexp : 1+(y-x) ≤ Real.exp (y-x) := by
    simpa only [add_comm] using Real.add_one_le_exp (y-x)
  have hmul : y ≤ x*Real.exp (y-x) :=
    hlin.trans (mul_le_mul_of_nonneg_left hexp hxpos.le)
  have heq : Real.exp (y-2) = Real.exp (x-2)*Real.exp (y-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_le_div_iff₀ hxpos hypos).mpr
  rw [heq]
  nlinarith only [mul_le_mul_of_nonneg_left hmul (Real.exp_pos (x-2)).le]

theorem interval_bound (r a b E L : ℝ) (ha : 2 ≤ a)
    (hra : a ≤ r) (hrb : r ≤ b) (hb : b ≤ 4)
    (hE : Real.exp (b-2) ≤ E) (hL : Real.log (3/(a-1)) ≤ L) :
    Real.exp (r-2)/r*(Real.log (3/(r-1))+1/3) ≤ (E/b)*(L+1/3) := by
  have hrpos : 0 < r := by linarith
  have hbpos : 0 < b := by linarith
  have hra1 : 0 < r-1 := by linarith
  have ha1 : 0 < a-1 := by linarith
  have hquot : (3:ℝ)/(r-1) ≤ 3/(a-1) :=
    div_le_div_of_nonneg_left (by norm_num) ha1 (by linarith)
  have hlog : Real.log (3/(r-1)) ≤ L :=
    (Real.log_le_log (div_pos (by norm_num) hra1) hquot).trans hL
  have hratio : (1:ℝ) ≤ 3/(r-1) := (le_div_iff₀ hra1).mpr (by linarith)
  have hnonneg : 0 ≤ Real.log (3/(r-1))+1/3 := by
    have hh := Real.log_nonneg hratio
    linarith
  have hfirst : Real.exp (r-2)/r ≤ E/b :=
    (exp_div_mono r b (by linarith) hrb).trans
      (div_le_div_of_nonneg_right hE hbpos.le)
  have hEpos : 0 ≤ E/b :=
    div_nonneg ((Real.exp_pos _).le.trans hE) hbpos.le
  exact mul_le_mul hfirst (by linarith) hnonneg hEpos

theorem majorant_le (r : ℝ) (hr : 2 ≤ r) : majorant r ≤ (99/100:ℝ) := by
  unfold majorant
  split_ifs with hr4
  · by_cases h1 : r ≤ 5/2
    · have hh := interval_bound r 2 (5/2) (33/20) (10/9) (by norm_num) hr h1
        (by norm_num) (by convert exp_half_le using 1; norm_num)
        (by convert log_three_le using 1; norm_num)
      exact hh.trans (by norm_num)
    · by_cases h2 : r ≤ 3
      · have hh := interval_bound r (5/2) 3 (11/4) (7/10) (by norm_num)
          (le_of_not_ge h1) h2 (by norm_num)
          (by convert exp_one_le.trans (by norm_num : (68/25:ℝ) ≤ 11/4) using 1; norm_num)
          (by convert log_two_le using 1; norm_num)
        exact hh.trans (by norm_num)
      · by_cases h3 : r ≤ 7/2
        · have hh := interval_bound r 3 (7/2) (9/2) (5/12) (by norm_num)
            (le_of_not_ge h2) h3 (by norm_num)
            (by convert exp_three_halves_le using 1; norm_num)
            (by convert log_three_halves_le using 1; norm_num)
          exact hh.trans (by norm_num)
        · have hh := interval_bound r (7/2) 4 (15/2) (3/16) (by norm_num)
            (le_of_not_ge h3) hr4 (by norm_num)
            (by convert exp_two_le using 1; norm_num)
            (by convert log_six_fifths_le using 1; norm_num)
          exact hh.trans (by norm_num)
  · have hrp : 0 < r*(r-1) := mul_pos (by linarith) (by linarith)
    apply (div_le_iff₀ hrp).mpr
    have hh := exp_two_le
    have hrr : 12 ≤ r*(r-1) := by nlinarith
    nlinarith

theorem majorant_lt_one (r : ℝ) (hr : 2 ≤ r) : majorant r < 1 :=
  (majorant_le r hr).trans_lt (by norm_num)

run_cmd do
  for decl in [``exp_one_le, ``exp_half_le, ``exp_three_halves_le, ``exp_two_le,
      ``log_three_le, ``log_two_le, ``log_three_halves_le, ``log_six_fifths_le,
      ``exp_div_mono, ``interval_bound, ``majorant_le, ``majorant_lt_one] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ROSSER KERNEL SCALAR CONTRACTION: STANDARD AXIOMS ONLY"

end RosserKernelContraction
end

end
