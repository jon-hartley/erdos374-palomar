module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
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


/-! Quantitative signed Fourier tail. The proof is a finite reciprocal-square
telescoping comparison, followed by the positive and negative integer halves. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace PairReciprocalTail

def natTail (K n : ℕ) : ℝ := if K<n then ((n:ℝ)^2)⁻¹ else 0

def reciprocalTail (K : ℕ) (k : ℤ) : ℝ := if (K:ℤ) < |k| then 1/(k:ℝ)^2 else 0

def fourierTail (K : ℕ) (k : ℤ) : ℝ :=
  if (K:ℤ) < |k| then (1/(Real.pi*|(k:ℝ)|))^2 else 0

theorem natTail_nonneg (K n : ℕ) : 0≤natTail K n := by
  unfold natTail
  split_ifs <;> positivity

theorem natTail_sum_le (K : ℕ) (hK : 1≤K) (s : Finset ℕ) :
    ∑n∈s,natTail K n≤1/(K:ℝ) := by
  simp only [natTail,←Finset.sum_filter]
  have hsub : s.filter (fun n => K<n) ⊆ Finset.Ioc K (max K (s.sup id)) := by
    intro n hn
    obtain ⟨hn,hKn⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Ioc.mpr ⟨hKn,(Finset.le_sup (f:=id) hn).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑n∈Finset.Ioc K (max K (s.sup id)),((n:ℝ)^2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro n _ _; positivity)
    _ ≤ (K:ℝ)⁻¹-((max K (s.sup id):ℕ):ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub (by omega) (le_max_left _ _)
    _ ≤ _ := by rw [one_div]; exact sub_le_self _ (by positivity)

theorem summable_natTail (K : ℕ) (hK : 1≤K) : Summable (natTail K) :=
  summable_of_sum_le (natTail_nonneg K) (natTail_sum_le K hK)

theorem tsum_natTail_le (K : ℕ) (hK : 1≤K) : ∑'n,natTail K n≤1/(K:ℝ) :=
  Real.tsum_le_of_sum_le (natTail_nonneg K) (natTail_sum_le K hK)

theorem reciprocalTail_nat (K n : ℕ) : reciprocalTail K n=natTail K n := by
  simp [reciprocalTail,natTail]

theorem reciprocalTail_neg_nat (K n : ℕ) : reciprocalTail K (-(n:ℤ))=natTail K n := by
  simp [reciprocalTail,natTail]

theorem reciprocalTail_nonneg (K : ℕ) (k : ℤ) : 0≤reciprocalTail K k := by
  unfold reciprocalTail
  split_ifs <;> positivity

theorem summable_reciprocalTail (K : ℕ) (hK : 1≤K) : Summable (reciprocalTail K) := by
  apply Summable.of_nat_of_neg
  · simpa only [reciprocalTail_nat] using summable_natTail K hK
  · simpa only [reciprocalTail_neg_nat] using summable_natTail K hK

theorem tsum_reciprocalTail_eq (K : ℕ) (hK : 1≤K) :
    (∑'k:ℤ,reciprocalTail K k)=2*(∑'n:ℕ,natTail K n) := by
  have hn : Summable (fun n:ℕ => reciprocalTail K n) := by
    simpa only [reciprocalTail_nat] using summable_natTail K hK
  have hm : Summable (fun n:ℕ => reciprocalTail K (-(n:ℤ))) := by
    simpa only [reciprocalTail_neg_nat] using summable_natTail K hK
  rw [hn.tsum_of_nat_of_neg hm]
  simp only [reciprocalTail_nat,reciprocalTail_neg_nat]
  simp [reciprocalTail,natTail,two_mul]

theorem tsum_reciprocalTail_le (K : ℕ) (hK : 1≤K) :
    (∑'k:ℤ,reciprocalTail K k)≤2/(K:ℝ) := by
  rw [tsum_reciprocalTail_eq K hK]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (tsum_natTail_le K hK) (by norm_num : (0:ℝ)≤2)

theorem fourierTail_nonneg (K : ℕ) (k : ℤ) : 0≤fourierTail K k := by
  unfold fourierTail
  split_ifs <;> positivity

theorem fourierTail_le_reciprocalTail (K : ℕ) (k : ℤ) :
    fourierTail K k≤reciprocalTail K k := by
  by_cases hk : k=0
  · subst k
    simp [fourierTail,reciprocalTail]
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk
  have hp : 1≤Real.pi := by linarith [Real.two_le_pi]
  unfold fourierTail reciprocalTail
  split_ifs
  · rw [div_pow,one_pow,mul_pow,sq_abs]
    apply one_div_le_one_div_of_le (sq_pos_of_ne_zero hkR)
    exact le_mul_of_one_le_left (sq_nonneg (k:ℝ)) (one_le_pow₀ hp)
  · rfl

theorem summable_tail (K : ℕ) (hK : 1≤K) : Summable (fourierTail K) :=
  (summable_reciprocalTail K hK).of_nonneg_of_le (fourierTail_nonneg K)
    (fourierTail_le_reciprocalTail K)

theorem tsum_tail_le (K : ℕ) (hK : 1≤K) :
    (∑'k:ℤ,fourierTail K k)≤2/(K:ℝ) := by
  exact (Summable.tsum_le_tsum (fourierTail_le_reciprocalTail K)
    (summable_tail K hK) (summable_reciprocalTail K hK)).trans (tsum_reciprocalTail_le K hK)

theorem tsum_tail_le_four (K : ℕ) (hK : 1≤K) :
    (∑'k:ℤ,fourierTail K k)≤4/(K:ℝ) := by
  exact (tsum_tail_le K hK).trans (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg K))

run_cmd do
  for decl in [``natTail_nonneg,``natTail_sum_le,``summable_natTail,``tsum_natTail_le,
      ``reciprocalTail_nat,``reciprocalTail_neg_nat,``reciprocalTail_nonneg,
      ``summable_reciprocalTail,``tsum_reciprocalTail_eq,``tsum_reciprocalTail_le,
      ``fourierTail_nonneg,``fourierTail_le_reciprocalTail,``summable_tail,``tsum_tail_le,
      ``tsum_tail_le_four] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "QUANTITATIVE SIGNED RECIPROCAL-SQUARE FOURIER TAIL PASSED"

end PairReciprocalTail
