module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Intervals
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
public import Init.Data.Iterators.Lemmas.Monadic.Basic
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
public import Init.Data.List.Nat.Prod
public import Init.Data.List.Nat.Range
public import Init.Data.List.Nat.Sum
public import Init.Data.List.Nat.TakeDrop
public import Init.Data.List.Pairwise
public import Init.Data.List.Range
public import Init.Data.List.Sublist
public import Init.Data.List.TakeDrop
public import Init.Data.List.Zip
public import Init.Data.Nat.Power2.Lemmas
public import Init.Data.Nat.Simproc
public import Init.Data.Option.Array
public import Init.Data.Option.Function
public import Init.Data.Option.List
public import Init.Data.Prod
public import Init.Data.Range.Polymorphic
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
public import Lean.Elab.Tactic.Induction
public import Lean.Elab.Tactic.RenameInaccessibles
public import Lean.Language.Lean.Util
public import Lean.Linter.MissingDocs
public import Lean.Linter.UnusedVariables
public import Lean.Meta.Constructions.CtorIdx
public import Lean.Meta.Constructions.SparseCasesOn
public import Lean.Meta.HasNotBit
public import Lean.Meta.HaveTelescope
public import Lean.Meta.Match.CaseArraySizes
public import Lean.Meta.Match.CaseValues
public import Lean.Meta.Match.NamedPatterns
public import Lean.Meta.Match.SimpH
public import Lean.Meta.Match.SolveOverlap
public import Lean.Meta.MethodSpecs
public import Lean.Meta.NatInstTesters
public import Lean.Meta.PPBinder
public import Lean.Meta.ProdN
public import Lean.Meta.StringLitProof
public import Lean.Meta.Tactic.ExposeNames
public import Lean.Meta.Tactic.FunIndCollect
public import Lean.PrettyPrinter.Delaborator.DeclWithSig
public import Lean.Runtime
public import Lean.Server.CodeActions
public import Lean.Util.UnusedBinders
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Tactic.Basify.Attr
public import Std.Time.Format
public import Std.Time.Zoned.Database.PosixTz

@[expose] public section


/-! Exact bounded doubling partitions. The lower endpoint is always excluded
and the upper endpoint included. No support member or coefficient is discarded. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace FourPrimePartition

def scale (a j : ℕ) : ℕ := 2^j*a

def block (S : Finset ℕ) (a j : ℕ) : Finset ℕ :=
  S.filter (fun n => scale a j < n ∧ n ≤ 2*scale a j)

def active (S : Finset ℕ) (a k : ℕ) : Finset ℕ :=
  (Finset.range (k+1)).filter (fun j => (block S a j).Nonempty)

@[simp] theorem scale_zero (a : ℕ) : scale a 0 = a := by simp [scale]

theorem scale_succ (a j : ℕ) : scale a (j+1) = 2*scale a j := by
  simp only [scale, pow_succ]
  ring

theorem scale_pos (a j : ℕ) (ha : 1 ≤ a) : 1 ≤ scale a j := by
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))

@[simp] theorem mem_block (S : Finset ℕ) (a j n : ℕ) :
    n ∈ block S a j ↔ n ∈ S ∧ scale a j < n ∧ n ≤ 2*scale a j := by
  simp [block]

theorem block_subset (S : Finset ℕ) (a j : ℕ) : block S a j ⊆ S :=
  Finset.filter_subset _ _

theorem block_in_interval (S : Finset ℕ) (a j : ℕ) :
    block S a j ⊆ Finset.Ioc (scale a j) (2*scale a j) := by
  intro n hn
  exact Finset.mem_Ioc.mpr (mem_block S a j n |>.mp hn).2

theorem block_bounds (S : Finset ℕ) (a j : ℕ) :
    ∀ n ∈ block S a j, scale a j < n ∧ n ≤ 2*scale a j := by
  intro n hn
  exact ((mem_block S a j n).mp hn).2

theorem block_disjoint_of_lt (S : Finset ℕ) (a i j : ℕ) (hij : i < j) :
    Disjoint (block S a i) (block S a j) := by
  have hp : 2*scale a i ≤ scale a j := by
    rw [← scale_succ]
    exact Nat.mul_le_mul_right a
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : i+1 ≤ j))
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  have hi := (mem_block S a i n).mp hni
  have hj := (mem_block S a j n).mp hnj
  omega

theorem blocks_pairwiseDisjoint (S : Finset ℕ) (a : ℕ) :
    Pairwise (fun i j => Disjoint (block S a i) (block S a j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact block_disjoint_of_lt S a i j h
  · exact (block_disjoint_of_lt S a j i h).symm

theorem biUnion_range_blocks (S : Finset ℕ) (a k : ℕ) :
    (Finset.range k).biUnion (block S a) =
      S.filter (fun n => a < n ∧ n ≤ scale a k) := by
  induction k with
  | zero =>
      simp only [Finset.range_zero, Finset.biUnion_empty, scale_zero]
      ext n
      constructor
      · intro hn
        simp at hn
      · intro hn
        have hh := Finset.mem_filter.mp hn
        omega
  | succ k ih =>
      rw [Finset.range_add_one, Finset.biUnion_insert, ih]
      ext n
      have ha : a ≤ scale a k := by
        simpa [scale] using Nat.mul_le_mul_right a
          (one_le_pow₀ (by norm_num : 1 ≤ (2:ℕ)) (n := k))
      have hh : scale a k ≤ 2*scale a k := by omega
      simp only [Finset.mem_union, mem_block, Finset.mem_filter, scale_succ]
      constructor
      · rintro (⟨hs, hlo, hhi⟩ | ⟨hs, hlo, hhi⟩)
        · exact ⟨hs, lt_of_le_of_lt ha hlo, hhi⟩
        · exact ⟨hs, hlo, hhi.trans hh⟩
      · rintro ⟨hs, hlo, hhi⟩
        by_cases hm : n ≤ scale a k
        · exact Or.inr ⟨hs, hlo, hm⟩
        · exact Or.inl ⟨hs, lt_of_not_ge hm, hhi⟩

theorem biUnion_active_eq (S : Finset ℕ) (a k : ℕ)
    (hcover : ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1)) :
    (active S a k).biUnion (block S a) = S := by
  have hfilter : (Finset.range (k+1)).biUnion (block S a) = S := by
    rw [biUnion_range_blocks]
    exact Finset.filter_eq_self.mpr hcover
  calc
    _ = (Finset.range (k+1)).biUnion (block S a) := by
      ext n
      simp only [Finset.mem_biUnion, active, Finset.mem_filter]
      constructor
      · rintro ⟨j, ⟨hj, _⟩, hn⟩
        exact ⟨j, hj, hn⟩
      · rintro ⟨j, hj, hn⟩
        exact ⟨j, ⟨hj, ⟨n, hn⟩⟩, hn⟩
    _ = S := hfilter

theorem active_card_le (S : Finset ℕ) (a k : ℕ) : (active S a k).card ≤ k+1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem active_nonempty_block (S : Finset ℕ) (a k j : ℕ) (hj : j ∈ active S a k) :
    (block S a j).Nonempty := (Finset.mem_filter.mp hj).2

theorem active_empty (a k : ℕ) : active ∅ a k = ∅ := by
  simp [active, block]

/-- The exact coefficient sum is unchanged, for every additive commutative monoid. -/
theorem sum_active_blocks {β : Type*} [AddCommMonoid β]
    (S : Finset ℕ) (a k : ℕ) (f : ℕ → β)
    (hcover : ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1)) :
    (∑ j ∈ active S a k, ∑ n ∈ block S a j, f n) = ∑ n ∈ S, f n := by
  have hd : Set.PairwiseDisjoint (↑(active S a k)) (block S a) := by
    intro i hi j hj hij
    exact blocks_pairwiseDisjoint S a hij
  have hh := Finset.sum_biUnion (f := f) hd
  rw [biUnion_active_eq S a k hcover] at hh
  exact hh.symm

/-- A support of ratio at most 2^k, with every member at least two, fits
in k+1 consecutive global doubling bins. The empty case is constructed too. -/
theorem exists_base (S : Finset ℕ) (k : ℕ)
    (hpos : ∀ n ∈ S, 2 ≤ n)
    (hratio : ∀ m ∈ S, ∀ n ∈ S, n ≤ 2^k*m) :
    ∃ a : ℕ, 1 ≤ a ∧ (∃ e : ℕ, a = 2^e) ∧
      ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1) := by
  classical
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := Finset.min'_mem S hS
    have hm2 : 2 ≤ m := hpos m hm
    let e := Nat.log 2 (m-1)
    let a := 2^e
    have ha : 1 ≤ a := one_le_pow₀ (by norm_num)
    have halow : a ≤ m-1 := Nat.pow_log_le_self 2 (by omega)
    have hmup : m ≤ 2*a := by
      have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (m-1)
      change m-1 < 2^(e+1) at hh
      rw [pow_succ] at hh
      change m ≤ 2*2^e
      omega
    refine ⟨a, ha, ⟨e, rfl⟩, ?_⟩
    intro n hn
    have hmn : m ≤ n := Finset.min'_le S n hn
    refine ⟨by omega, ?_⟩
    calc
      n ≤ 2^k*m := hratio m hm n hn
      _ ≤ 2^k*(2*a) := Nat.mul_le_mul_left _ hmup
      _ = scale a (k+1) := by simp [scale, pow_succ]; ring
  · refine ⟨1, by omega, ⟨0, by simp⟩, ?_⟩
    intro n hn
    exact False.elim (hS ⟨n, hn⟩)

/-- Real support endpoints are permitted; no floor or endpoint convention is lost. -/
theorem exists_base_of_real_span (S : Finset ℕ) (k : ℕ) (L : ℝ)
    (hpos : ∀ n ∈ S, 2 ≤ n)
    (hspan : ∀ n ∈ S, L ≤ (n:ℝ) ∧ (n:ℝ) ≤ (2:ℝ)^k*L) :
    ∃ a : ℕ, 1 ≤ a ∧ (∃ e : ℕ, a = 2^e) ∧
      ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1) := by
  apply exists_base S k hpos
  intro m hm n hn
  have hh := (hspan n hn).2.trans
    (mul_le_mul_of_nonneg_left (hspan m hm).1 (by positivity : 0 ≤ (2:ℝ)^k))
  exact_mod_cast hh

theorem exists_five_bins (S : Finset ℕ) (L : ℝ)
    (hpos : ∀ n ∈ S, 2 ≤ n)
    (hspan : ∀ n ∈ S, L ≤ (n:ℝ) ∧ (n:ℝ) ≤ 16*L) :
    ∃ a : ℕ, 1 ≤ a ∧ (∃ e : ℕ, a = 2^e) ∧
      (active S a 4).card ≤ 5 ∧
      (active S a 4).biUnion (block S a) = S ∧
      ∀ n ∈ S, a < n ∧ n ≤ scale a 5 := by
  obtain ⟨a, ha, he, hcover⟩ := exists_base_of_real_span S 4 L hpos
    (by simpa only [show (2:ℝ)^4=16 by norm_num] using hspan)
  exact ⟨a, ha, he, active_card_le S a 4, biUnion_active_eq S a 4 hcover, hcover⟩

theorem exists_two_bins (S : Finset ℕ) (L : ℝ)
    (hpos : ∀ n ∈ S, 2 ≤ n)
    (hspan : ∀ n ∈ S, L ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*L) :
    ∃ a : ℕ, 1 ≤ a ∧ (∃ e : ℕ, a = 2^e) ∧
      (active S a 1).card ≤ 2 ∧
      (active S a 1).biUnion (block S a) = S ∧
      ∀ n ∈ S, a < n ∧ n ≤ scale a 2 := by
  obtain ⟨a, ha, he, hcover⟩ := exists_base_of_real_span S 1 L hpos (by simpa using hspan)
  exact ⟨a, ha, he, active_card_le S a 1, biUnion_active_eq S a 1 hcover, hcover⟩

#print axioms exists_five_bins
#print axioms sum_active_blocks
run_cmd do
  for target in [``scale_pos, ``block_in_interval, ``block_bounds, ``blocks_pairwiseDisjoint,
      ``biUnion_range_blocks, ``biUnion_active_eq, ``active_card_le,
      ``active_nonempty_block, ``active_empty, ``sum_active_blocks,
      ``exists_base, ``exists_base_of_real_span, ``exists_five_bins, ``exists_two_bins] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FOUR_PRIME_PARTITION_PASSED"

end FourPrimePartition
end

end
