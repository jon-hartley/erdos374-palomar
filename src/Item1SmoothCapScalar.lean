module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
public import Lean.Elab.ConfigEval.Util
public import Lean.Elab.DeprecatedArg
public import Lean.Elab.DeprecatedSyntax
public import Lean.Elab.DocString
public import Lean.Elab.ErrorUtils
public import Lean.Elab.Quotation
public import Lean.Elab.Tactic.Grind.Anchor
public import Lean.Elab.Tactic.Grind.Param
public import Lean.Elab.Tactic.Induction
public import Lean.Elab.Tactic.RenameInaccessibles
public import Lean.Language.Lean.Util
public import Lean.Linter.MissingDocs
public import Lean.Linter.UnusedVariables
public import Lean.Meta.Constructions.CtorIdx
public import Lean.Meta.Constructions.SparseCasesOn
public import Lean.Meta.CtorIdxHInj
public import Lean.Meta.HasNotBit
public import Lean.Meta.HaveTelescope
public import Lean.Meta.Injective
public import Lean.Meta.Match.CaseArraySizes
public import Lean.Meta.Match.CaseValues
public import Lean.Meta.Match.MatcherApp
public import Lean.Meta.Match.NamedPatterns
public import Lean.Meta.Match.SimpH
public import Lean.Meta.Match.SolveOverlap
public import Lean.Meta.MethodSpecs
public import Lean.Meta.NatInstTesters
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
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
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


/-!
Scalar absorption for the five-term envelope in the accompanying
written contour proof. No small prime polynomial, smoothed Mellin formula or
zero-free estimate is assumed or proved by the scalar theorem. The retained
medium-log proof is adapted solely as an elementary exponential domination lemma.
This bounded module is Mathlib-only and does not import the full Erdos project.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter
namespace Item1SmoothCapScalar
/-- Adapted from Update152, lines 31240--31263. The original theorem is
`medium_logPower_eventually_small141`; only name/namespace and layout change.
Its argument is an elementary limit, not a PNT or zeta input. -/
private theorem eventually_log_power_small
    (k : ℕ) (c : ℝ) (hc : 0 < c) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) *
        (Real.log x) ^ k < eps := by
  have hroot : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((10 * k : ℕ) : ℝ) c hc).comp hroot
  have hsmall := (tendsto_order.mp hlim).2 eps heps
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
    Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < eps at hxsmall
  rw [hpower] at hxsmall
  simpa only [mul_comm] using hxsmall

def lowerExponent (B : ℕ) : ℕ := 2*B+6

def normalizedBudget (B : ℕ) (a C ell : ℝ) : ℝ :=
  12/ell + 4*(Real.exp (-ell)*ell^(B+1)) +
  (9*(4:ℝ)^9*C)*(Real.exp (-(a/4)*ell^(1/4:ℝ))*ell^(2*B+11)) +
  (216*(4:ℝ)^9*C)/ell^(2*B+1) + 324/ell^2

theorem target_parameters :
    lowerExponent 26001=52008 ∧ 26001+2=26003 ∧
      26001+11=26012 ∧ 2*26001+11=52013 := by
  norm_num [lowerExponent]

/-- Reuse the existing elementary exponential/log-power limit after u=exp ell.
This is not an application of the prime number theorem. -/
theorem eventually_power_exp_small (m : ℕ) (c r eps : ℝ)
    (hc : 0 < c) (hr : (1/10:ℝ) ≤ r) (heps : 0 < eps) :
    ∀ᶠ ell : ℝ in atTop, Real.exp (-c*ell^r)*ell^m ≤ eps := by
  have hh := Real.tendsto_exp_atTop.eventually
    (eventually_log_power_small m c hc eps heps)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with ell he hL
  have hbase : Real.exp (-c*ell^(1/10:ℝ))*ell^m < eps := by
    simpa only [Real.log_exp] using he
  have hp := Real.rpow_le_rpow_of_exponent_le hL hr
  have hecomp : Real.exp (-c*ell^r) ≤ Real.exp (-c*ell^(1/10:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_right hecomp (pow_nonneg (by linarith) m)).trans hbase.le

theorem reciprocal_power_le (ell : ℝ) (k : ℕ) (hL : 1 ≤ ell) (hk : 1 ≤ k) :
    1/ell^k ≤ 1/ell := by
  have hp : ell ≤ ell^k := by
    simpa only [pow_one] using pow_le_pow_right₀ hL hk
  exact one_div_le_one_div_of_le (by linarith : 0 < ell) hp

/-- All five normalized error terms tend to zero; one common threshold suffices.
The analytic derivation of this envelope is written, not fully formalized here. -/
theorem eventually_budget_le_one (B : ℕ) (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∀ᶠ ell : ℝ in atTop, normalizedBudget B a C ell ≤ 1 := by
  have h2 := eventually_power_exp_small (B+1) 1 1 (1/20)
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := eventually_power_exp_small (2*B+11) (a/4) (1/4)
    (1/(45*(4:ℝ)^9*C)) (by positivity) (by norm_num) (by positivity)
  filter_upwards [h2,h3,eventually_ge_atTop (1620:ℝ),
    eventually_ge_atTop (1080*(4:ℝ)^9*C)] with ell he2 he3 hL hLC
  have hL0 : 0 < ell := by linarith
  have hL1 : 1 ≤ ell := by linarith
  have ht1 : 12/ell ≤ (1/5:ℝ) := (div_le_iff₀ hL0).mpr (by linarith)
  have ht2 : 4*(Real.exp (-ell)*ell^(B+1)) ≤ (1/5:ℝ) := by
    simpa only [Real.rpow_one, neg_mul, one_mul, mul_one_div, show (4:ℝ)/20=1/5 by norm_num] using
      mul_le_mul_of_nonneg_left he2 (by norm_num : (0:ℝ) ≤ 4)
  have ht3 : (9*(4:ℝ)^9*C)*
      (Real.exp (-(a/4)*ell^(1/4:ℝ))*ell^(2*B+11)) ≤ (1/5:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left he3
      (show 0 ≤ 9*(4:ℝ)^9*C by positivity)
    have hid : (9*(4:ℝ)^9*C)*(1/(45*(4:ℝ)^9*C))=(1/5:ℝ) := by
      field_simp [hC.ne']
      <;> ring
    exact hh.trans_eq hid
  have ht4 : (216*(4:ℝ)^9*C)/ell^(2*B+1) ≤ (1/5:ℝ) := by
    have hp := mul_le_mul_of_nonneg_left
      (reciprocal_power_le ell (2*B+1) hL1 (by omega))
      (show 0 ≤ 216*(4:ℝ)^9*C by positivity)
    have hh : (216*(4:ℝ)^9*C)/ell ≤ (1/5:ℝ) :=
      (div_le_iff₀ hL0).mpr (by nlinarith)
    have hp' : (216*(4:ℝ)^9*C)/ell^(2*B+1) ≤ (216*(4:ℝ)^9*C)/ell := by
      simpa only [mul_one_div] using hp
    exact hp'.trans hh
  have ht5 : 324/ell^2 ≤ (1/5:ℝ) := by
    have hp := mul_le_mul_of_nonneg_left
      (reciprocal_power_le ell 2 hL1 (by norm_num)) (by norm_num : (0:ℝ) ≤ 324)
    have hh : (324:ℝ)/ell ≤ (1/5:ℝ) := (div_le_iff₀ hL0).mpr (by linarith)
    have hp' : (324:ℝ)/ell^2 ≤ 324/ell := by
      simpa only [mul_one_div] using hp
    exact hp'.trans hh
  unfold normalizedBudget
  linarith

run_cmd do
  for target in [``eventually_log_power_small, ``target_parameters,
    ``eventually_power_exp_small, ``reciprocal_power_le, ``eventually_budget_le_one] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms eventually_log_power_small
#print axioms eventually_budget_le_one

end Item1SmoothCapScalar
