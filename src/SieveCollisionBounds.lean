module

public import Mathlib.Analysis.PSeries
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
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
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
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
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


noncomputable section
open scoped BigOperators
open Finset

namespace SieveCollisionBounds

/-- Literal reciprocal mass of a finite pool of natural numbers. -/
def mass (P : Finset ℕ) : ℝ := ∑ p ∈ P, (p : ℝ)⁻¹

/-- Reciprocal mass of ordered pairs, retaining the diagonal. -/
def pairMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P, ((p : ℝ) * (q : ℝ))⁻¹

/-- Reciprocal mass of ordered distinct pairs. -/
def distinctMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p, ((p : ℝ) * (q : ℝ))⁻¹

def diagonalMass (P : Finset ℕ) : ℝ := ∑ p ∈ P, ((p : ℝ)^2)⁻¹

theorem mass_nonneg (P : Finset ℕ) : 0 ≤ mass P := by
  exact sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem diagonalMass_nonneg (P : Finset ℕ) : 0 ≤ diagonalMass P := by
  exact sum_nonneg (fun p _ => inv_nonneg.mpr (sq_nonneg (p : ℝ)))

theorem pairMass_eq_sq (P : Finset ℕ) : pairMass P = mass P ^ 2 := by
  simp only [pairMass, mass, mul_inv, ← mul_sum, ← sum_mul, pow_two]

theorem distinct_add_diagonal (P : Finset ℕ) :
    distinctMass P + diagonalMass P = pairMass P := by
  unfold distinctMass diagonalMass pairMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  simpa only [pow_two] using
    sum_erase_add P (fun q : ℕ => ((p : ℝ) * (q : ℝ))⁻¹) hp

/-- Exact loss from removing repeated primes, with all ordered representations retained. -/
theorem sq_mass_sub_distinct (P : Finset ℕ) :
    mass P ^ 2 - distinctMass P = diagonalMass P := by
  have h := distinct_add_diagonal P
  rw [pairMass_eq_sq] at h
  linarith

/-- A finite pool above a real cutoff has reciprocal-square mass at most
`1/(u-1)`. This all-integer bound needs no prime distribution hypothesis. -/
theorem diagonalMass_le (P : Finset ℕ) (u : ℝ) (hu : 1 < u)
    (hp : ∀ p ∈ P, u ≤ (p : ℝ)) : diagonalMass P ≤ 1 / (u - 1) := by
  let k : ℕ := ⌈u⌉₊ - 1
  let n : ℕ := max k (P.sup id)
  have hc : 2 ≤ ⌈u⌉₊ := Nat.add_one_le_ceil_iff.mpr (by simpa using hu)
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hkn : k ≤ n := le_max_left _ _
  have hsub : P ⊆ Ioc k n := by
    intro p hmem
    have hcp : ⌈u⌉₊ ≤ p := Nat.ceil_le.mpr (hp p hmem)
    have hsup : p ≤ P.sup id := Finset.le_sup (f := id) hmem
    have hpn : p ≤ n := hsup.trans (le_max_right _ _)
    exact mem_Ioc.mpr ⟨by dsimp [k]; omega, hpn⟩
  have hkcast : (k : ℝ) = (⌈u⌉₊ : ℝ) - 1 := by
    dsimp [k]
    rw [Nat.cast_sub (by omega : 1 ≤ ⌈u⌉₊), Nat.cast_one]
  have hku : u - 1 ≤ (k : ℝ) := by rw [hkcast]; linarith [Nat.le_ceil u]
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  calc
    diagonalMass P ≤ ∑ p ∈ Ioc k n, ((p : ℝ)^2)⁻¹ := by
      exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ (k : ℝ)⁻¹ - (n : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hk hkn
    _ ≤ (k : ℝ)⁻¹ := sub_le_self _ (by positivity)
    _ ≤ 1 / (u - 1) := by
      rw [← one_div]
      exact one_div_le_one_div_of_le (by linarith) hku

theorem distinct_discrepancy_bounds (P : Finset ℕ) (u : ℝ) (hu : 1 < u)
    (hp : ∀ p ∈ P, u ≤ (p : ℝ)) :
    0 ≤ mass P ^ 2 - distinctMass P ∧
      mass P ^ 2 - distinctMass P ≤ 1 / (u - 1) := by
  rw [sq_mass_sub_distinct]
  exact ⟨diagonalMass_nonneg P, diagonalMass_le P u hu hp⟩

theorem distinct_discrepancy_abs_le (P : Finset ℕ) (u : ℝ) (hu : 1 < u)
    (hp : ∀ p ∈ P, u ≤ (p : ℝ)) :
    |mass P ^ 2 - distinctMass P| ≤ 1 / (u - 1) := by
  obtain ⟨hn, hb⟩ := distinct_discrepancy_bounds P u hu hp
  rwa [abs_of_nonneg hn]

/-- A separate same-band estimate: it counts every ordered pair in each band,
including unequal primes. The upper bound on each actual band mass is explicit. -/
theorem same_band_pair_mass_le {ι : Type*} (I : Finset ι)
    (band : ι → Finset ℕ) (η : ℝ) (hη : ∀ i ∈ I, mass (band i) ≤ η) :
    (∑ i ∈ I, pairMass (band i)) ≤ η * ∑ i ∈ I, mass (band i) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  rw [pairMass_eq_sq, pow_two]
  exact mul_le_mul_of_nonneg_right (hη i hi) (mass_nonneg (band i))

#print axioms diagonalMass_le
#print axioms distinct_discrepancy_abs_le
run_cmd do
  for decl in [``mass_nonneg, ``diagonalMass_nonneg, ``pairMass_eq_sq,
      ``distinct_add_diagonal, ``sq_mass_sub_distinct, ``diagonalMass_le,
      ``distinct_discrepancy_bounds, ``distinct_discrepancy_abs_le,
      ``same_band_pair_mass_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE COLLISION BOUNDS PASSED; standard axioms only"

end SieveCollisionBounds
end

end
