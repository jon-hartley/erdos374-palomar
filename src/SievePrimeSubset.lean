module

public import Mathlib.Data.Nat.Squarefree
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
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.DSimpPercent
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


/-! Port of the checked finite constructor from HarmanPrimeSubset169.lean.
This module imports only Mathlib and does not import an old Erdos checkpoint.
Concrete collection of parity-signed selected prime subsets.  Selecting the
subsets by the source stopped sieve recursion remains a separate construction. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators
namespace SievePrimeSubset

def subsetProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

theorem prime_subset_product_injective (s t : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (he : subsetProduct s = subsetProduct t) : s = t := by
  have h := congrArg Nat.primeFactors he
  simpa only [subsetProduct, Nat.primeFactors_prod hs, Nat.primeFactors_prod ht] using h

/-- Actual collection by integer product; each selected subset contributes its parity sign. -/
def selectedCoefficient (A : Finset (Finset ℕ)) (m : ℕ) : ℝ :=
  ∑ s ∈ A.filter (fun s => subsetProduct s = m), (-1 : ℝ)^s.card

theorem selectedCoefficient_eq_sign (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (s : Finset ℕ) (hs : s ∈ A) :
    selectedCoefficient A (subsetProduct s) = (-1 : ℝ)^s.card := by
  unfold selectedCoefficient
  have hsF : s ∈ A.filter (fun t => subsetProduct t = subsetProduct s) :=
    Finset.mem_filter.mpr ⟨hs, rfl⟩
  apply Finset.sum_eq_single_of_mem s hsF
  intro t ht hts
  obtain ⟨htA, he⟩ := Finset.mem_filter.mp ht
  exact (hts (prime_subset_product_injective t s (hA t htA) (hA s hs) he)).elim

theorem selectedCoefficient_eq_zero (A : Finset (Finset ℕ)) (m : ℕ)
    (h : ∀ s ∈ A, subsetProduct s ≠ m) : selectedCoefficient A m = 0 := by
  unfold selectedCoefficient
  have he : A.filter (fun s => subsetProduct s = m) = ∅ :=
    Finset.filter_eq_empty_iff.mpr h
  rw [he, Finset.sum_empty]

theorem selectedCoefficient_abs_le_one (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (m : ℕ) :
    |selectedCoefficient A m| ≤ 1 := by
  by_cases he : ∃ s ∈ A, subsetProduct s = m
  · obtain ⟨s, hs, rfl⟩ := he
    rw [selectedCoefficient_eq_sign A hA s hs]
    simp
  · rw [selectedCoefficient_eq_zero A m (by simpa using he)]
    norm_num

theorem selectedCoefficient_nonzero_representation (A : Finset (Finset ℕ)) (m : ℕ)
    (h : selectedCoefficient A m ≠ 0) : ∃ s ∈ A, subsetProduct s = m := by
  by_contra he
  exact h (selectedCoefficient_eq_zero A m (by simpa using he))

theorem selectedCoefficient_shared_sign (A B : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (hB : ∀ s ∈ B, ∀ p ∈ s, p.Prime)
    (m : ℕ) : selectedCoefficient A m = 0 ∨ selectedCoefficient B m = 0 ∨
      selectedCoefficient A m = selectedCoefficient B m := by
  by_cases ha : selectedCoefficient A m = 0
  · exact Or.inl ha
  by_cases hb : selectedCoefficient B m = 0
  · exact Or.inr (Or.inl hb)
  obtain ⟨s, hs, hsm⟩ := selectedCoefficient_nonzero_representation A m ha
  obtain ⟨t, ht, htm⟩ := selectedCoefficient_nonzero_representation B m hb
  have hst := prime_subset_product_injective s t (hA s hs) (hB t ht) (hsm.trans htm.symm)
  subst t
  subst m
  exact Or.inr (Or.inr ((selectedCoefficient_eq_sign A hA s hs).trans
    (selectedCoefficient_eq_sign B hB s ht).symm))

/-- The level conclusion is obtained from an explicit restriction on the selected subsets. -/
theorem selectedCoefficient_support_level (A : Finset (Finset ℕ)) (D m : ℕ)
    (hlevel : ∀ s ∈ A, subsetProduct s < D) (hm : D ≤ m) :
    selectedCoefficient A m = 0 := by
  apply selectedCoefficient_eq_zero
  intro s hs he
  have := hlevel s hs
  omega

theorem selectedCoefficient_one (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (he : ∅ ∈ A) :
    selectedCoefficient A 1 = 1 := by
  simpa [subsetProduct] using selectedCoefficient_eq_sign A hA ∅ he

theorem selectedCoefficient_support_positive (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (m : ℕ)
    (hm : selectedCoefficient A m ≠ 0) : 0 < m := by
  obtain ⟨s, hs, rfl⟩ := selectedCoefficient_nonzero_representation A m hm
  exact Finset.prod_pos (fun p hp => (hA s hs p hp).pos)

#print axioms selectedCoefficient_shared_sign
#print axioms selectedCoefficient_abs_le_one
run_cmd do
  for target in [``prime_subset_product_injective, ``selectedCoefficient_eq_sign,
      ``selectedCoefficient_eq_zero, ``selectedCoefficient_abs_le_one,
      ``selectedCoefficient_nonzero_representation, ``selectedCoefficient_shared_sign,
      ``selectedCoefficient_support_level, ``selectedCoefficient_one,
      ``selectedCoefficient_support_positive] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
run_cmd Lean.logInfo "SIEVE_PRIME_SUBSET_PASSED; SELECTOR_AND_MAIN_TERM_NOT_ASSUMED"
end SievePrimeSubset
end

end
