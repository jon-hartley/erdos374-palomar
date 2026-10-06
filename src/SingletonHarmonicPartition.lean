module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
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
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
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


/-! An exact finite partition into blocks of length at most `L`.
The last, possibly shorter, block is part of every identity below. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SingletonHarmonicPartition

def blockCount (X L : ℝ) : ℕ := ⌈X / L⌉₊

def point (t X L : ℝ) (j : ℕ) : ℝ := t + min ((j : ℝ) * L) X

theorem point_zero (t X L : ℝ) (hX : 0 ≤ X) : point t X L 0 = t := by
  simp [point, min_eq_left hX]

theorem point_lower (t X L : ℝ) (hX : 0 ≤ X) (hL : 0 ≤ L) (j : ℕ) :
    t ≤ point t X L j := by
  unfold point
  exact le_add_of_nonneg_right (le_min (mul_nonneg (Nat.cast_nonneg j) hL) hX)

theorem point_upper (t X L : ℝ) (j : ℕ) : point t X L j ≤ t + X := by
  exact add_le_add le_rfl (min_le_right _ _)

theorem point_mono (t X L : ℝ) (hL : 0 ≤ L) : Monotone (point t X L) := by
  intro i j hij
  unfold point
  exact add_le_add le_rfl
    (min_le_min_right X (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hL))

theorem block_length_nonneg (t X L : ℝ) (hL : 0 ≤ L) (j : ℕ) :
    0 ≤ point t X L (j + 1) - point t X L j := by
  exact sub_nonneg.mpr (point_mono t X L hL (Nat.le_succ j))

theorem block_length_le (t X L : ℝ) (hL : 0 ≤ L) (j : ℕ) :
    point t X L (j + 1) - point t X L j ≤ L := by
  unfold point
  simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  by_cases hj : (j : ℝ) * L ≤ X
  · rw [min_eq_left hj]
    linarith [min_le_left ((j : ℝ) * L + L) X]
  · rw [min_eq_right (le_of_not_ge hj)]
    linarith [min_le_right ((j : ℝ) * L + L) X]

theorem point_final (t X L : ℝ) (hL : 0 < L) :
    point t X L (blockCount X L) = t + X := by
  have h : X ≤ (blockCount X L : ℝ) * L :=
    (div_le_iff₀ hL).mp (Nat.le_ceil (X / L))
  exact congrArg (fun u : ℝ => t + u) (min_eq_right h)

theorem blockCount_pos (X L : ℝ) (hX : 0 < X) (hL : 0 < L) :
    0 < blockCount X L := by
  exact Nat.one_le_ceil_iff.mpr (div_pos hX hL)

theorem blockCount_le_ratio_add_one (X L : ℝ) (hX : 0 ≤ X) (hL : 0 < L) :
    (blockCount X L : ℝ) ≤ X / L + 1 := by
  exact (Nat.ceil_lt_add_one (div_nonneg hX hL.le)).le

theorem blockCount_le_two_ratio (X L : ℝ) (hL : 0 < L) (hLX : L ≤ X) :
    (blockCount X L : ℝ) ≤ 2 * (X / L) := by
  have hr : 1 ≤ X / L := (le_div_iff₀ hL).mpr (by simpa using hLX)
  have h := blockCount_le_ratio_add_one X L (hL.le.trans hLX) hL
  linarith

theorem sum_block_lengths (t X L : ℝ) (hX : 0 ≤ X) (hL : 0 < L) :
    (∑ j ∈ Finset.range (blockCount X L),
      (point t X L (j + 1) - point t X L j)) = X := by
  have htel : ∀ J : ℕ, (∑ j ∈ Finset.range J,
      (point t X L (j + 1) - point t X L j)) = point t X L J - point t X L 0 := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  rw [htel, point_final t X L hL, point_zero t X L hX]
  ring

theorem block_integrable (f : ℝ → ℝ) (t X L : ℝ) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hf : IntervalIntegrable f volume t (t + X)) (j : ℕ) :
    IntervalIntegrable f volume (point t X L j) (point t X L (j + 1)) := by
  apply hf.mono_set
  apply Set.uIcc_subset_uIcc
  all_goals
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hX)]
    exact ⟨point_lower t X L hX hL _, point_upper t X L _⟩

theorem sum_block_integrals (f : ℝ → ℝ) (t X L : ℝ) (hX : 0 ≤ X) (hL : 0 < L)
    (hf : IntervalIntegrable f volume t (t + X)) :
    (∑ j ∈ Finset.range (blockCount X L),
      ∫ x in point t X L j..point t X L (j + 1), f x) = ∫ x in t..t + X, f x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := point t X L) (n := blockCount X L)
    (fun j _ => block_integrable f t X L hX hL.le hf j)
  simpa only [point_zero t X L hX, point_final t X L hL] using h

/-- The boundary allowance `C` is paid once for every block, including the last. -/
theorem integral_le_of_blocks (f : ℝ → ℝ) (t X L A C : ℝ) (hX : 0 ≤ X) (hL : 0 < L)
    (hf : IntervalIntegrable f volume t (t + X))
    (hb : ∀ j < blockCount X L,
      (∫ x in point t X L j..point t X L (j + 1), f x) ≤
        A * (point t X L (j + 1) - point t X L j) + C) :
    (∫ x in t..t + X, f x) ≤ A * X + (blockCount X L : ℝ) * C := by
  rw [← sum_block_integrals f t X L hX hL hf]
  calc
    _ ≤ ∑ j ∈ Finset.range (blockCount X L),
        (A * (point t X L (j + 1) - point t X L j) + C) :=
      Finset.sum_le_sum fun j hj => hb j (Finset.mem_range.mp hj)
    _ = A * X + (blockCount X L : ℝ) * C := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_block_lengths t X L hX hL]
      simp

end SingletonHarmonicPartition
