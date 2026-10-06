module

public import Mathlib.Algebra.Order.Floor.BigOperators
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.Data.Int.LeastGreatest
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


/-! Finite residue identities for the covariance of divisor-window counts. -/

open scoped BigOperators

namespace SingletonResidue

/-- The integer count on a unit cell, with arbitrary integral width. -/
def count (a : ℕ) (K : ℤ) (q : ℕ) : ℤ :=
  (q : ℤ) / (a : ℤ) - ((q : ℤ) - K) / (a : ℤ)

theorem sum_count {a : ℕ} (ha : 0 < a) (K : ℤ) :
    ∑ q ∈ Finset.range a, count a K q = K := by
  unfold count
  rw [Finset.sum_sub_distrib]
  have hzero := Int.sum_range_add_ediv 0 ha
  have hneg := Int.sum_range_add_ediv (-K) ha
  simp only [zero_add] at hzero
  have hsub : (∑ q ∈ Finset.range a, ((q : ℤ) - K) / (a : ℤ)) = -K := by
    simpa only [sub_eq_add_neg, add_comm] using hneg
  rw [hzero, hsub]
  omega

theorem count_mod {a : ℕ} (ha : 0 < a) (K : ℤ) (q : ℕ) :
    count a K q = count a K (q % a) := by
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hq : (q : ℤ) = (q / a : ℕ) * (a : ℤ) + (q % a : ℕ) := by
    have hqn : q = q / a * a + q % a := by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod q a).symm
    exact_mod_cast hqn
  unfold count
  conv_lhs => rw [hq]
  rw [show (q / a : ℕ) * (a : ℤ) + (q % a : ℕ) - K =
    (q / a : ℕ) * (a : ℤ) + ((q % a : ℕ) - K) by ring]
  rw [Int.mul_add_ediv_right _ _ ha0, Int.mul_add_ediv_right _ _ ha0]
  omega

/-- Chinese remainder independence, expressed directly with finite natural ranges. -/
theorem sum_range_crt {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (f g : ℕ → ℝ) :
    (∑ q ∈ Finset.range (a * b), f (q % a) * g (q % b)) =
      (∑ i ∈ Finset.range a, f i) * (∑ j ∈ Finset.range b, g j) := by
  have hprod : (∑ p ∈ Finset.range a ×ˢ Finset.range b, f p.1 * g p.2) =
      (∑ i ∈ Finset.range a, f i) * (∑ j ∈ Finset.range b, g j) := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
  rw [← hprod]
  refine Finset.sum_bij (fun q _ => (q % a, q % b)) ?_ ?_ ?_ ?_
  · intro q hq
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ ha),
      Finset.mem_range.mpr (Nat.mod_lt _ hb)⟩
  · intro q hq r hr hqr
    have hqa : q ≡ r [MOD a] := congrArg Prod.fst hqr
    have hqb : q ≡ r [MOD b] := congrArg Prod.snd hqr
    have hmod : q ≡ r [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hqa, hqb⟩
    exact hmod.eq_of_lt_of_lt (Finset.mem_range.mp hq) (Finset.mem_range.mp hr)
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    let q := Nat.chineseRemainder hab p.1 p.2
    refine ⟨q, Finset.mem_range.mpr
      (Nat.chineseRemainder_lt_mul hab _ _ (ne_of_gt ha) (ne_of_gt hb)), ?_⟩
    apply Prod.ext
    · calc
        (q : ℕ) % a = p.1 % a := q.prop.1
        _ = p.1 := Nat.mod_eq_of_lt (Finset.mem_range.mp hp'.1)
    · calc
        (q : ℕ) % b = p.2 % b := q.prop.2
        _ = p.2 := Nat.mod_eq_of_lt (Finset.mem_range.mp hp'.2)
  · intro q hq
    rfl

theorem sum_count_real {a : ℕ} (ha : 0 < a) (K : ℤ) :
    ∑ q ∈ Finset.range a, (count a K q : ℝ) = (K : ℝ) := by
  exact_mod_cast sum_count ha K

/-- The complete residue sum of a centered count. -/
theorem sum_centered {a : ℕ} (ha : 0 < a) (K : ℤ) (h : ℝ) :
    ∑ q ∈ Finset.range a, ((count a K q : ℝ) - h / a) = (K : ℝ) - h := by
  rw [Finset.sum_sub_distrib, sum_count_real ha]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact finite centered covariance for a coprime pair. No analytic premise is used. -/
theorem sum_centered_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (K : ℤ) (h : ℝ) :
    (∑ q ∈ Finset.range (a * b),
      ((count a K q : ℝ) - h / a) * ((count b K q : ℝ) - h / b)) =
        ((K : ℝ) - h) ^ 2 := by
  calc
    _ = ∑ q ∈ Finset.range (a * b),
        ((count a K (q % a) : ℝ) - h / a) *
          ((count b K (q % b) : ℝ) - h / b) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [count_mod ha K q, count_mod hb K q]
    _ = (∑ i ∈ Finset.range a, ((count a K i : ℝ) - h / a)) *
        (∑ j ∈ Finset.range b, ((count b K j : ℝ) - h / b)) :=
      sum_range_crt ha hb hab (fun i => (count a K i : ℝ) - h / a)
        (fun j => (count b K j : ℝ) - h / b)
    _ = ((K : ℝ) - h) ^ 2 := by rw [sum_centered ha, sum_centered hb]; ring

end SingletonResidue

end
