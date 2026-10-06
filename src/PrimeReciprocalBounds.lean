module

public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
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
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Prime.Int
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


/-! Unconditional dimension-one upper bounds for reciprocal prime intervals.
The only prime-counting input is Mathlib's proved Chebyshev estimate. -/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory

namespace PrimeReciprocalBounds

def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

theorem sum_primeIndicator (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeIndicator n = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
  simp [primeIndicator]

def openClosedPrimes (a b : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime

theorem reciprocal_abel (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹ =
      b⁻¹ * (Nat.primeCounting ⌊b⌋₊ : ℝ) -
        a⁻¹ * (Nat.primeCounting ⌊a⌋₊ : ℝ) +
          ∫ t in a..b, (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  have hcont : ContinuousOn (fun t : ℝ => -(t^2)⁻¹) (Set.Icc a b) := by
    fun_prop (disch := intro t ht; nlinarith [ht.1])
  have h := sum_mul_eq_sub_sub_integral_mul primeIndicator
    (f := fun t : ℝ => t⁻¹) (by linarith : 0 ≤ a) hab
    (fun t ht => (hasDerivAt_inv (by linarith [ht.1])).differentiableAt)
    (by simpa only [deriv_inv'] using hcont.integrableOn_Icc)
  simp only [sum_primeIndicator, deriv_inv, neg_mul,
    ← intervalIntegral.integral_of_le hab] at h
  simpa [openClosedPrimes, Finset.sum_filter, primeIndicator] using h

theorem count_inv_sq_integrable (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ)) volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc a b) := by
    fun_prop (disch := intro t ht; nlinarith [ht.1])
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa only [sum_primeIndicator] using
    integrableOn_mul_sum_Icc primeIndicator (m := 0) (by linarith : 0 ≤ a)
      hcont.integrableOn_Icc

theorem reciprocal_openClosed_le (a b : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (hc : ∀ t ∈ Set.Icc a b,
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ 4*t / Real.log t) :
    ∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹ ≤
      4 * (Real.log (Real.log b) - Real.log (Real.log a)) + 4 / Real.log a := by
  have hb : 1 < b := ha.trans_le hab
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hlog : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have hn : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht =>
      ne_of_gt (ha0.trans_le ht.1)
    exact (continuousOn_id.inv₀ hn).div (continuousOn_id.log hn)
      (fun t ht => ne_of_gt (Real.log_pos (ha.trans_le ht.1)))
  have hi := intervalIntegral.integral_mono_on hab
    (count_inv_sq_integrable a b ha hab) (hlog.const_mul 4).intervalIntegrable
    (fun t ht => show (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
      4 * (t⁻¹ / Real.log t) from calc
        _ ≤ (t^2)⁻¹ * (4*t / Real.log t) :=
          mul_le_mul_of_nonneg_left (hc t ht) (by positivity)
        _ = _ := by
          have ht0 : t ≠ 0 := by linarith [ht.1]
          field_simp)
  rw [intervalIntegral.integral_const_mul,
    integral_inv_div_log ha hb] at hi
  have hleft : 0 ≤ a⁻¹ * (Nat.primeCounting ⌊a⌋₊ : ℝ) := by positivity
  have hright : b⁻¹ * (Nat.primeCounting ⌊b⌋₊ : ℝ) ≤ 4 / Real.log b := calc
    _ ≤ b⁻¹ * (4*b / Real.log b) :=
      mul_le_mul_of_nonneg_left (hc b ⟨hab, le_rfl⟩) (by positivity)
    _ = _ := by field_simp
  have hinv : 4 / Real.log b ≤ 4 / Real.log a := by
    exact div_le_div_of_nonneg_left (by norm_num) (Real.log_pos ha)
      (Real.log_le_log ha0 hab)
  rw [reciprocal_abel a b ha hab]
  linarith

theorem eventual_primeCounting_bound :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ x : ℝ, W ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 4*x / Real.log x := by
  obtain ⟨W, hW⟩ := eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  refine ⟨max 2 W, le_max_left _ _, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  refine (hW x ((le_max_right _ _).trans hx)).trans ?_
  apply div_le_div_of_nonneg_right _ hlog.le
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  linarith

/-- Including the lower endpoint costs at most `1/log a`.  No upper-endpoint
primality convention or interval rounding is imposed on the finite set. -/
theorem sum_le_openClosed_add (S : Finset ℕ) (a b : ℝ) (ha : 1 < a)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    ∑ p ∈ S, (p : ℝ)⁻¹ ≤
      (∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹) + 1 / Real.log a := by
  have ha0 : 0 ≤ a := by linarith
  have hsub : S ⊆ insert ⌊a⌋₊ (openClosedPrimes a b) := by
    intro p hp
    obtain ⟨hpp, hpa, hpb⟩ := hS p hp
    by_cases he : p = ⌊a⌋₊
    · simp [he]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨?_, Nat.le_floor hpb⟩, hpp⟩
      have hfloor : ⌊a⌋₊ ≤ p := by
        exact_mod_cast (Nat.floor_le ha0).trans hpa
      omega
  have hnot : ⌊a⌋₊ ∉ openClosedPrimes a b := by
    simp [openClosedPrimes]
  have hlog : Real.log a ≤ (⌊a⌋₊ : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < a)
    have h2 := Nat.lt_floor_add_one a
    linarith
  have hi : (⌊a⌋₊ : ℝ)⁻¹ ≤ 1 / Real.log a := by
    simpa only [one_div] using one_div_le_one_div_of_le (Real.log_pos ha) hlog
  calc
    _ ≤ ∑ p ∈ insert ⌊a⌋₊ (openClosedPrimes a b), (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = (⌊a⌋₊ : ℝ)⁻¹ + ∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹ :=
      Finset.sum_insert hnot
    _ ≤ _ := by linarith

/-- A single absolute threshold works for every finite prime set and every pair
of enclosing real endpoints.  This is unconditional: Chebyshev supplies the
prime-counting estimate used in partial summation. -/
theorem eventual_reciprocal_interval_bound :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (a b : ℝ) (S : Finset ℕ), W ≤ a → a ≤ b →
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤
        4 * Real.log (Real.log b / Real.log a) + 5 / Real.log a := by
  obtain ⟨W, hW2, hW⟩ := eventual_primeCounting_bound
  refine ⟨W, hW2, fun a b S ha hab hS => ?_⟩
  have ha1 : 1 < a := by linarith
  have hb1 : 1 < b := ha1.trans_le hab
  have hi := reciprocal_openClosed_le a b ha1 hab
    (fun t ht => hW t (ha.trans ht.1))
  have hs := sum_le_openClosed_add S a b ha1 hS
  rw [Real.log_div (ne_of_gt (Real.log_pos hb1)) (ne_of_gt (Real.log_pos ha1))]
  simp only [div_eq_mul_inv] at hi hs ⊢
  linarith

/-- The convenient common constant `5` version. -/
theorem eventual_reciprocal_interval_bound_five :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (a b : ℝ) (S : Finset ℕ), W ≤ a → a ≤ b →
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤
        5 * (Real.log (Real.log b / Real.log a) + 1 / Real.log a) := by
  obtain ⟨W, hW2, hW⟩ := eventual_reciprocal_interval_bound
  refine ⟨W, hW2, fun a b S ha hab hS => ?_⟩
  have ha1 : 1 < a := by linarith
  have hl : 0 ≤ Real.log (Real.log b / Real.log a) := by
    apply Real.log_nonneg
    exact (one_le_div (Real.log_pos ha1)).2
      (Real.log_le_log (by linarith) hab)
  have := hW a b S ha hab hS
  simp only [div_eq_mul_inv] at this hl ⊢
  linarith

/-- Uniform in the band location and ratio: the threshold is absolute, before
`u`, `a`, `q`, and the actual prime set. -/
theorem eventual_reciprocal_geometric_bound :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (u a q : ℝ) (S : Finset ℕ), W ≤ u → u ≤ a → 1 ≤ q →
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a^q) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤ 4 * Real.log q + 5 / Real.log u := by
  obtain ⟨W, hW2, hW⟩ := eventual_reciprocal_interval_bound
  refine ⟨W, hW2, fun u a q S hu hua hq hS => ?_⟩
  have hu1 : 1 < u := by linarith
  have ha1 : 1 < a := hu1.trans_le hua
  have haa : a ≤ a^q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ha1.le hq
  have hi := hW a (a^q) S (hu.trans hua) haa hS
  rw [Real.log_rpow (by linarith : 0 < a), mul_div_cancel_right₀ _
    (ne_of_gt (Real.log_pos ha1))] at hi
  have hinv : 5 / Real.log a ≤ 5 / Real.log u :=
    div_le_div_of_nonneg_left (by norm_num) (Real.log_pos hu1)
      (Real.log_le_log (by linarith) hua)
  linarith

#print axioms reciprocal_openClosed_le
#print axioms eventual_primeCounting_bound
#print axioms eventual_reciprocal_interval_bound_five
#print axioms eventual_reciprocal_geometric_bound
run_cmd do
  for decl in [``sum_primeIndicator, ``reciprocal_abel, ``count_inv_sq_integrable,
    ``reciprocal_openClosed_le, ``eventual_primeCounting_bound, ``sum_le_openClosed_add,
    ``eventual_reciprocal_interval_bound, ``eventual_reciprocal_interval_bound_five,
    ``eventual_reciprocal_geometric_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end PrimeReciprocalBounds
end

end
