module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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


/-! Algebraic budget for a WEAKER short-phase hypothesis.
This file proves no exponential-sum cancellation. Its sum-of-squares identity
explains precisely how much loss the final zeta-growth argument can tolerate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
namespace Item1WeakCubicBudget

theorem cubic_certificate (v : ℝ) :
    v^3-200*v+1200 =
      v*(v-8)^2+16*(v-33/4)^2+111 := by ring

theorem cubic_upper (v : ℝ) (hv : 0≤v) : v-v^3/200≤6 := by
  have hid := cubic_certificate v
  have hpos := mul_nonneg hv (sq_nonneg (v-8))
  nlinarith [sq_nonneg (v-33/4)]

/-- A scaled polynomial inequality, with all divisibility/positivity guards.
x = (log t)^(1/3), y = log log t in the application. -/
theorem cubic_exponent (x y u Delta : ℝ) (hx : 0<x) (hy : 0<y)
    (hu : 0≤u) (hD : Delta≤1/x^2) :
    Delta*u-u^3/(200*x^6*y^2) ≤ 6*y := by
  let v := u/(x^2*y)
  have hv : 0≤v := by dsimp [v]; positivity
  have hc := mul_le_mul_of_nonneg_left (cubic_upper v hv) hy.le
  have hid : u/x^2-u^3/(200*x^6*y^2)=y*(v-v^3/200) := by
    dsimp [v]
    field_simp
  have hDu := mul_le_mul_of_nonneg_right hD hu
  have hDu' : Delta*u≤u/x^2 := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hDu
  have hh : Delta*u-u^3/(200*x^6*y^2) ≤
      u/x^2-u^3/(200*x^6*y^2) := sub_le_sub_right hDu' _
  rw [←hid] at hc
  nlinarith only [hh, hc]

theorem cube_root_ids (L : ℝ) (hL : 0<L) :
    (L^(1/3:ℝ))^2=L^(2/3:ℝ) ∧
    (L^(1/3:ℝ))^6=L^2 := by
  constructor
  · rw [←Real.rpow_mul_natCast hL.le (1/3:ℝ) 2]
    norm_num
  · rw [←Real.rpow_mul_natCast hL.le (1/3:ℝ) 6]
    norm_num

theorem logarithmic_cubic_exponent (L u Delta : ℝ) (hL : 1<L)
    (hu : 0≤u) (hD : Delta≤1/L^(2/3:ℝ)) :
    Delta*u-u^3/(200*L^2*(Real.log L)^2)≤6*Real.log L := by
  have hp : 0<L := by linarith
  obtain ⟨hi2,hi6⟩ := cube_root_ids L hp
  have hh := cubic_exponent (L^(1/3:ℝ)) (Real.log L) u Delta
    (Real.rpow_pos_of_pos hp _) (Real.log_pos hL) hu (by rw [hi2]; exact hD)
  simpa only [hi6] using hh

theorem exponential_cubic_envelope (L u Delta : ℝ) (hL : 1<L)
    (hu : 0≤u) (hD : Delta≤1/L^(2/3:ℝ)) :
    Real.exp (Delta*u-u^3/(200*L^2*(Real.log L)^2))≤L^6 := by
  have hh := Real.exp_le_exp.mpr (logarithmic_cubic_exponent L u Delta hL hu hD)
  have he : Real.exp (6*Real.log L)=L^6 := by
    rw [←show Real.log (L^6)=6*Real.log L by exact Real.log_pow L 6,
      Real.exp_log (pow_pos (by linarith) 6)]
  simpa [he] using hh

/-- The count is the number of dyadic blocks, not a fixed geometric host count. -/
theorem block_sum_budget {ι : Type*} (s : Finset ι) (b : ι → ℝ) (L : ℝ)
    (hL : 0≤L) (hc : (s.card:ℝ)≤5*L) (hb : ∀ j∈s, b j≤16*L^6) :
    (∑ j∈s, b j)≤80*L^7 := by
  have hcoef : 0≤16*L^6 := mul_nonneg (by norm_num) (pow_nonneg hL _)
  calc
    _ ≤ ∑ _j∈s, 16*L^6 := Finset.sum_le_sum hb
    _ = (s.card:ℝ)*(16*L^6) := by simp
    _ ≤ (5*L)*(16*L^6) := mul_le_mul_of_nonneg_right hc hcoef
    _ = 80*L^7 := by ring

theorem final_growth_budget (Z S L : ℝ) (hL : 1≤L)
    (hZ : Z≤S+8) (hS : S≤80*L^7) : Z≤128*L^7 := by
  have hp : 1≤L^7 := one_le_pow₀ hL
  nlinarith

/-- A safe Euler-tail bound once the finite cutoff is at least t^2.
q and p are Q^(1-sigma) and Q^(-sigma); their scalar bounds are explicit. -/
theorem euler_tail_budget (t sigma q p : ℝ) (ht : 1≤t)
    (hs : 1/2≤sigma) (hq : q≤t) (hp0 : 0≤p) (hp : p≤1/t) :
    q/t+(3/2)*p+2*t*p/sigma≤8 := by
  have htp : 0<t := by linarith
  have hsp : 0<sigma := by linarith
  have hqt : q/t≤1 := (div_le_one htp).mpr hq
  have hpt : t*p≤1 := by
    have hh := (le_div_iff₀ htp).mp hp
    nlinarith [mul_nonneg htp.le hp0]
  have hp1 : p≤1 := by
    have hh : 1/t≤1 := (div_le_one htp).mpr ht
    exact hp.trans hh
  have hr : 2*t*p/sigma≤4 := by
    apply (div_le_iff₀ hsp).mpr
    nlinarith
  linarith

end Item1WeakCubicBudget

run_cmd do
  for target in [``Item1WeakCubicBudget.cubic_certificate, ``Item1WeakCubicBudget.cubic_upper,
    ``Item1WeakCubicBudget.cubic_exponent, ``Item1WeakCubicBudget.cube_root_ids,
    ``Item1WeakCubicBudget.logarithmic_cubic_exponent,
    ``Item1WeakCubicBudget.exponential_cubic_envelope,
    ``Item1WeakCubicBudget.block_sum_budget, ``Item1WeakCubicBudget.final_growth_budget,
    ``Item1WeakCubicBudget.euler_tail_budget] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1WeakCubicBudget.exponential_cubic_envelope
#print axioms Item1WeakCubicBudget.euler_tail_budget
