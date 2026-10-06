module

public import Mathlib.Tactic
public import Mathlib.Data.Finset.Powerset
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
public import Mathlib.Tactic.Basify.Attr
public import Std.Time.Format
public import Std.Time.Zoned.Database.PosixTz

@[expose] public section


/-! Actual finite alternating prefix-stop selectors.  The gate is tested only
on an inclusion from the upper state; skipping does not change state. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SievePrefix

def selected (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ) :
    List ℕ → Finset (Finset ℕ)
  | [] => {∅}
  | p :: ps => selected gate upper d ps ∪
      if upper = false ∨ gate d p then
        (selected gate (!upper) (d * p) ps).image (insert p)
      else ∅

def term (b : ℕ → ℝ) (s : Finset ℕ) : ℝ :=
  (-1 : ℝ) ^ s.card * ∏ p ∈ s, b p

def value (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ s ∈ selected gate upper d ps, term b s

theorem selected_subset (gate : ℕ → ℕ → Prop) (upper : Bool) (d : ℕ)
    (ps : List ℕ) (s : Finset ℕ) (hs : s ∈ selected gate upper d ps) :
    s ⊆ ps.toFinset := by
  induction ps generalizing upper d s with
  | nil => simpa [selected] using hs
  | cons p ps ih =>
    simp only [selected, Finset.mem_union] at hs
    rcases hs with hs | hs
    · exact (ih upper d s hs).trans (by simp)
    · split_ifs at hs with hg
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
        simpa only [List.toFinset_cons] using
          Finset.insert_subset_insert p (ih (!upper) (d * p) r hr)
      · simp at hs

theorem term_insert (b : ℕ → ℝ) (p : ℕ) (s : Finset ℕ) (hp : p ∉ s) :
    term b (insert p s) = -(b p * term b s) := by
  simp only [term, Finset.card_insert_of_notMem hp, Finset.prod_insert hp, pow_succ]
  ring

theorem sum_insert_image (A : Finset (Finset ℕ)) (b : ℕ → ℝ) (p : ℕ)
    (hp : ∀ s ∈ A, p ∉ s) :
    (∑ s ∈ A.image (insert p), term b s) = -(b p * ∑ s ∈ A, term b s) := by
  rw [Finset.sum_image]
  · calc
      (∑ s ∈ A, term b (insert p s)) = ∑ s ∈ A, -(b p * term b s) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact term_insert b p s (hp s hs)
      _ = -(b p * ∑ s ∈ A, term b s) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
  · intro s hs r hr heq
    have hh := congrArg (fun t : Finset ℕ => t.erase p) heq
    simpa [hp s hs, hp r hr] using hh

theorem value_cons (gate : ℕ → ℕ → Prop) (upper : Bool) (d p : ℕ)
    (ps : List ℕ) (b : ℕ → ℝ) (hp : p ∉ ps) :
    value gate upper d (p :: ps) b = value gate upper d ps b -
      if upper = false ∨ gate d p then b p * value gate (!upper) (d*p) ps b else 0 := by
  have hnot : ∀ mode d s, s ∈ selected gate mode d ps → p ∉ s := by
    intro mode d s hs hps
    exact hp (List.mem_toFinset.mp (selected_subset gate mode d ps s hs hps))
  unfold value
  rw [selected]
  split_ifs with hg
  · rw [Finset.sum_union]
    · rw [sum_insert_image _ b p (hnot (!upper) (d*p))]
      ring
    · apply Finset.disjoint_left.mpr
      intro s hs hi
      obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hi
      exact hnot upper d s hs (heq ▸ Finset.mem_insert_self p r)
  · simp

theorem value_bounds (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hnd : ps.Nodup) (hb : ∀ p ∈ ps, 0 ≤ b p ∧ b p ≤ 1) :
    value gate false d ps b ≤ ∏ p ∈ ps.toFinset, (1-b p) ∧
      (∏ p ∈ ps.toFinset, (1-b p)) ≤ value gate true d ps b := by
  induction ps generalizing d with
  | nil => simp [value, selected, term]
  | cons p ps ih =>
    obtain ⟨hp, hnd⟩ := List.nodup_cons.mp hnd
    have hbp := hb p (by simp)
    have hbt : ∀ q ∈ ps, 0 ≤ b q ∧ b q ≤ 1 := fun q hq => hb q (by simp [hq])
    have hskip := ih d hnd hbt
    have htake := ih (d*p) hnd hbt
    have hprod : 0 ≤ ∏ q ∈ ps.toFinset, (1-b q) := by
      apply Finset.prod_nonneg
      intro q hq
      exact sub_nonneg.mpr (hbt q (List.mem_toFinset.mp hq)).2
    rw [value_cons gate false d p ps b hp, value_cons gate true d p ps b hp]
    have hpf : p ∉ ps.toFinset := by simpa using hp
    simp only [false_or, Bool.not_false, Bool.not_true,
      true_or, ite_true, Bool.true_eq_false, List.toFinset_cons,
      Finset.prod_insert hpf]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left htake.2 hbp.1]
    · split_ifs with hg
      · nlinarith [mul_le_mul_of_nonneg_left htake.1 hbp.1]
      · nlinarith

theorem value_bounds_finset (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (b : ℕ → ℝ) (hnd : ps.Nodup)
    (hb : ∀ p ∈ ps.toFinset, 0 ≤ b p ∧ b p ≤ 1) :
    value gate false d ps b ≤ ∏ p ∈ ps.toFinset, (1-b p) ∧
      (∏ p ∈ ps.toFinset, (1-b p)) ≤ value gate true d ps b :=
  value_bounds gate d ps b hnd (by simpa using hb)

#print axioms value_bounds
run_cmd do
  for decl in [``selected_subset, ``term_insert, ``sum_insert_image,
      ``value_cons, ``value_bounds, ``value_bounds_finset] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SievePrefix
end

end
