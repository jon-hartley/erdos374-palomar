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


/-! Scalar geometry for the repaired Euler cutoff.
The cutoff is at t^2, not t. No zeta or phase estimate is used here. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Item1SafeZetaCutoff

def cutoffIndex (t : ℝ) : ℕ := Nat.ceil (2*Real.log t/Real.log 2)

theorem cutoff_bounds (t : ℝ) (ht : 1≤t) (hL : 1≤Real.log t) :
    t^2≤((2^(cutoffIndex t):ℕ):ℝ) ∧
    ((2^(cutoffIndex t):ℕ):ℝ)<2*t^2 ∧
    (cutoffIndex t:ℝ)≤5*Real.log t := by
  have htp : 0<t := by linarith
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h2lo : (1/2:ℝ)≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    linarith
  have hq : 0≤2*Real.log t/Real.log 2 := by positivity
  have hlo : 2*Real.log t/Real.log 2≤(cutoffIndex t:ℝ) := Nat.le_ceil _
  have hhi : (cutoffIndex t:ℝ)<2*Real.log t/Real.log 2+1 :=
    Nat.ceil_lt_add_one hq
  have hlo' : 2*Real.log t≤(cutoffIndex t:ℝ)*Real.log 2 :=
    (div_le_iff₀ h2).mp hlo
  have hhi' : (cutoffIndex t:ℝ)*Real.log 2<2*Real.log t+Real.log 2 := by
    have hh := mul_lt_mul_of_pos_right hhi h2
    field_simp at hh
    nlinarith
  have hQp : (0:ℝ)<(2:ℝ)^cutoffIndex t := by positivity
  have hQl : Real.log ((2:ℝ)^cutoffIndex t)=
      (cutoffIndex t:ℝ)*Real.log 2 := Real.log_pow _ _
  have hQlo : t^2≤(2:ℝ)^cutoffIndex t := by
    apply (Real.log_le_log_iff (by positivity) hQp).mp
    rw [hQl,Real.log_pow]
    norm_num
    exact hlo'
  have hQhi : (2:ℝ)^cutoffIndex t<2*t^2 := by
    apply (Real.log_lt_log_iff hQp (by positivity)).mp
    rw [hQl,Real.log_mul (by norm_num) (pow_ne_zero 2 htp.ne'),Real.log_pow]
    norm_num
    linarith
  have hfrac : 2*Real.log t/Real.log 2≤4*Real.log t := by
    apply (div_le_iff₀ h2).mpr
    nlinarith [mul_nonneg (by linarith : 0≤Real.log 2-1/2)
      (by linarith : 0≤Real.log t)]
  refine ⟨?_,?_,by linarith⟩
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hQlo
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hQhi

theorem block_below_square (t : ℝ) (ht : 1≤t) (hL : 1≤Real.log t)
    (j : ℕ) (hj : j<cutoffIndex t) : ((2^j:ℕ):ℝ)≤t^2 := by
  have hQ := (cutoff_bounds t ht hL).2.1
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
    (show j+1≤cutoffIndex t by omega)
  have hp' : 2*((2^j:ℕ):ℝ)≤((2^(cutoffIndex t):ℕ):ℝ) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,pow_succ,mul_comm] using hp
  linarith

theorem strip_sigma_lower (L sigma : ℝ) (hL : 8≤L)
    (hs : 1-1/L^(2/3:ℝ)≤sigma) : 3/4≤sigma := by
  have h8 : (8:ℝ)^(2/3:ℝ)=4 := by
    calc
      _ = ((2:ℝ)^3)^(2/3:ℝ) := by norm_num
      _ = (2:ℝ)^((3:ℝ)*(2/3)) := (Real.rpow_natCast_mul (by norm_num) 3 (2/3)).symm
      _ = 4 := by norm_num
  have hh : 4≤L^(2/3:ℝ) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤8) hL (by norm_num : (0:ℝ)≤2/3)
    simpa only [h8] using hh
  have hp : 0<L^(2/3:ℝ) := by linarith
  have hi : 1/L^(2/3:ℝ)≤1/4 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

/-- The exact powers in the Euler bound are small with the enlarged cutoff. -/
theorem cutoff_powers (Q : ℕ) (t sigma : ℝ) (ht : 2≤t)
    (hQlo : t^2≤(Q:ℝ)) (hQhi : (Q:ℝ)<2*t^2)
    (hs : 3/4≤sigma) (hs1 : sigma≤1) :
    (Q:ℝ)^(1-sigma)≤t ∧ (Q:ℝ)^(-sigma)≤1/t := by
  have htp : 0<t := by linarith
  have hQp : (0:ℝ)<Q := lt_of_lt_of_le (sq_pos_of_pos htp) hQlo
  have hQ1 : (1:ℝ)≤Q := by nlinarith
  have hQt4 : (Q:ℝ)≤t^4 := by
    have hh : 2*t^2≤t^4 := by
      have hp := mul_nonneg (show 0≤t^2-2 by nlinarith) (sq_nonneg t)
      nlinarith
    exact hQhi.le.trans hh
  constructor
  · calc
      _ ≤ (Q:ℝ)^(1/4:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      _ ≤ (t^4)^(1/4:ℝ) := Real.rpow_le_rpow hQp.le hQt4 (by norm_num)
      _ = t := by rw [←Real.rpow_natCast_mul htp.le 4 (1/4:ℝ)]; norm_num
  · calc
      _ ≤ (t^2)^(-sigma) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos htp) hQlo (by linarith)
      _ = t^((-2)*sigma) := by
        rw [←Real.rpow_natCast_mul htp.le 2 (-sigma)]
        congr 1
        ring
      _ ≤ t^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1/t := by rw [Real.rpow_neg_one, one_div]

end Item1SafeZetaCutoff

run_cmd do
  for n in [``Item1SafeZetaCutoff.cutoff_bounds,
    ``Item1SafeZetaCutoff.block_below_square,
    ``Item1SafeZetaCutoff.strip_sigma_lower,
    ``Item1SafeZetaCutoff.cutoff_powers] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
