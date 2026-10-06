module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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


/-! Absolute and normalized scalar collision budgets. The normalized budget
charges the Euler ratio as well; attaching actual arithmetic estimates is
a separate theorem. The absolute budget alone does not control that ratio. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace SieveCollisionDecay

def error (s : ℝ) : ℝ :=
  5 * s^9 * (4 * Real.log (1/s^2) + 1) * Real.exp (17/16) *
    (1/s^2 : ℝ)^(17/4 : ℝ)

/-- The budget after combining the constant-2 prime mass estimate with both
the ordered-profile factor and the Euler-product ratio factor. -/
def normalizedError (s : ℝ) : ℝ :=
  3 * s^9 * (2 * Real.log (1/s^2) + 1) * Real.exp (17/8) *
    (1/s^2 : ℝ)^(17/4 : ℝ)

theorem reciprocal_power_balance (s : ℝ) (hs : 0 < s) :
    s^9 * (1/s^2 : ℝ)^(17/4 : ℝ) = s^(1/2 : ℝ) := by
  rw [one_div, Real.inv_rpow (sq_nonneg s), ← Real.rpow_neg (sq_nonneg s)]
  rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
    ← Real.rpow_natCast s 9, ← Real.rpow_add hs]
  norm_num

theorem log_reciprocal_square (s : ℝ) :
    Real.log (1/s^2) = 2 * Real.log (1/s) := by
  rw [one_div, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
  ring

theorem error_eq (s : ℝ) (hs : 0 < s) :
    error s = 5 * Real.exp (17/16) * s^(1/2 : ℝ) *
      (8 * Real.log (1/s) + 1) := by
  unfold error
  rw [log_reciprocal_square]
  calc
    _ = 5 * Real.exp (17/16) * (s^9 * (1/s^2 : ℝ)^(17/4 : ℝ)) *
        (8 * Real.log (1/s) + 1) := by ring
    _ = _ := by rw [reciprocal_power_balance s hs]

theorem normalizedError_eq (s : ℝ) (hs : 0 < s) :
    normalizedError s = 3 * Real.exp (17/8) * s^(1/2 : ℝ) *
      (4 * Real.log (1/s) + 1) := by
  unfold normalizedError
  rw [log_reciprocal_square]
  calc
    _ = 3 * Real.exp (17/8) * (s^9 * (1/s^2 : ℝ)^(17/4 : ℝ)) *
        (4 * Real.log (1/s) + 1) := by ring
    _ = _ := by rw [reciprocal_power_balance s hs]

theorem error_nonneg (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : 0 ≤ error s := by
  rw [error_eq s hs]
  have hl : 0 ≤ Real.log (1/s) := Real.log_nonneg
    ((one_le_div hs).mpr hs1)
  positivity

theorem normal_form_tendsto_zero (a b c : ℝ) :
    Tendsto (fun s : ℝ => a * Real.exp c * s^(1/2 : ℝ) *
      (b * Real.log (1/s) + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : Tendsto (fun s : ℝ => s^(1/2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/2)).tendsto 0).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hl := tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1/2)
  have h := ((hl.neg.const_mul b).add hp).const_mul (a * Real.exp c)
  simp only [neg_zero, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [] with s
  simp only [one_div, Real.log_inv]
  ring

theorem tendsto_error_zero : Tendsto error (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (normal_form_tendsto_zero 5 8 (17/16)).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (error_eq s hs).symm

theorem tendsto_normalizedError_zero :
    Tendsto normalizedError (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (normal_form_tendsto_zero 3 4 (17/8)).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (normalizedError_eq s hs).symm

theorem eventually_error_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), error s < ε :=
  (tendsto_order.mp tendsto_error_zero).2 ε hε

theorem eventually_normalizedError_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), normalizedError s < ε :=
  (tendsto_order.mp tendsto_normalizedError_zero).2 ε hε

theorem normalizedError_small (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ → normalizedError s < ε := by
  obtain ⟨s₀, hs₀, hb⟩ := Metric.mem_nhdsWithin_iff.mp
    (eventually_normalizedError_lt ε hε)
  refine ⟨s₀, hs₀, fun s hs hss => hb ⟨?_, hs⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs] using hss

#print axioms tendsto_error_zero
run_cmd do
  for decl in [``reciprocal_power_balance, ``log_reciprocal_square, ``error_eq,
      ``normalizedError_eq, ``error_nonneg, ``normal_form_tendsto_zero,
      ``tendsto_error_zero, ``tendsto_normalizedError_zero, ``eventually_error_lt,
      ``eventually_normalizedError_lt, ``normalizedError_small] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE COLLISION DECAY PASSED; standard axioms only"

end SieveCollisionDecay
end

end
