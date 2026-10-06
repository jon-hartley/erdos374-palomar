module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
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
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
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


/-! Finite exponential-polynomial mean squares with explicit off-diagonal
bounds. These are unconditional analytic lemmas, not exceptional-set axioms. -/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Erdos374.PairSpacingKernel

def exponentialKernel (ω t : ℝ) : ℂ :=
  Complex.exp ((Complex.I * (ω : ℂ)) * (t : ℂ))

def exponentialSum {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ξ : ι → ℝ) (t : ℝ) : ℂ := ∑ n ∈ s, a n * exponentialKernel (ξ n) t

theorem continuous_kernel (ω : ℝ) : Continuous (exponentialKernel ω) := by
  unfold exponentialKernel
  fun_prop

theorem norm_kernel (ω t : ℝ) : ‖exponentialKernel ω t‖ = 1 := by
  simp [exponentialKernel, Complex.norm_exp]

theorem kernel_zero (t : ℝ) : exponentialKernel 0 t = 1 := by
  simp [exponentialKernel]

theorem kernel_mul_conj (ω ν t : ℝ) :
    exponentialKernel ω t * conj (exponentialKernel ν t) =
      exponentialKernel (ω - ν) t := by
  unfold exponentialKernel
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

theorem integral_kernel (ω A B : ℝ) (hω : ω ≠ 0) :
    (∫ t in A..B, exponentialKernel ω t) =
      (exponentialKernel ω B - exponentialKernel ω A) /
        (Complex.I * (ω : ℂ)) := by
  exact integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hω))

theorem norm_integral_kernel_le (ω A B : ℝ) (hω : ω ≠ 0) :
    ‖∫ t in A..B, exponentialKernel ω t‖ ≤ 2 / |ω| := by
  rw [integral_kernel ω A B hω, norm_div]
  have hnum : ‖exponentialKernel ω B - exponentialKernel ω A‖ ≤ 2 := by
    simpa only [norm_kernel, one_add_one_eq_two] using
      norm_sub_le (exponentialKernel ω B) (exponentialKernel ω A)
  simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using
    div_le_div_of_nonneg_right hnum (norm_nonneg (Complex.I * (ω : ℂ)))

theorem continuous_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ξ : ι → ℝ) :
    Continuous (exponentialSum s a ξ) := by
  unfold exponentialSum
  exact continuous_finsetSum s (fun n _ => continuous_const.mul (continuous_kernel _))

theorem norm_square_expansion {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) :
    ((‖exponentialSum s a ξ t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) * exponentialKernel (ξ m - ξ n) t := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [exponentialSum, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [← kernel_mul_conj]
  ring

theorem mean_square_expansion {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ) :
    ((∫ t in A..B, ‖exponentialSum s a ξ t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel (ξ m - ξ n) t := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [norm_square_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro n hn
      exact (continuous_const.mul (continuous_kernel _)).intervalIntegrable _ _
  · intro m hm
    exact (continuous_finsetSum s fun n _ =>
      continuous_const.mul (continuous_kernel _)).intervalIntegrable _ _

theorem mean_square_diagonal {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ) :
    ((∫ t in A..B, ‖exponentialSum s a ξ t‖ ^ 2 : ℝ) : ℂ) -
        ((B - A) * ∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) =
      ∑ m ∈ s, ∑ n ∈ s.erase m, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel (ξ m - ξ n) t := by
  rw [mean_square_expansion]
  have hsplit :
      (∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) *
        ∫ t in A..B, exponentialKernel (ξ m - ξ n) t) =
      ((B - A) * ∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) +
        ∑ m ∈ s, ∑ n ∈ s.erase m, a m * conj (a n) *
          ∫ t in A..B, exponentialKernel (ξ m - ξ n) t := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.add_sum_erase s
      (fun n => a m * conj (a n) * ∫ t in A..B, exponentialKernel (ξ m - ξ n) t) hm]
    congr 1
    simp [kernel_zero, Complex.mul_conj', Complex.real_smul, mul_comm]
  rw [hsplit]
  ring

theorem mean_square_error_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (A B : ℝ)
    (hξ : Set.InjOn ξ (s : Set ι)) :
    |(∫ t in A..B, ‖exponentialSum s a ξ t‖ ^ 2) -
      (B - A) * ∑ n ∈ s, ‖a n‖ ^ 2| ≤
      ∑ m ∈ s, ∑ n ∈ s.erase m, 2 * ‖a m‖ * ‖a n‖ / |ξ m - ξ n| := by
  have hdiag := mean_square_diagonal s a ξ A B
  have hnorm := congrArg norm hdiag
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [hnorm]
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro m hm
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro n hn
  have hnm := Finset.mem_erase.mp hn
  have hne : ξ m - ξ n ≠ 0 := sub_ne_zero.mpr fun h =>
    hnm.1 (hξ hnm.2 hm h.symm)
  have hbound := mul_le_mul_of_nonneg_left (norm_integral_kernel_le (ξ m - ξ n) A B hne)
    (mul_nonneg (norm_nonneg (a m)) (norm_nonneg (a n)))
  simp only [norm_mul, RCLike.norm_conj]
  calc
    _ ≤ ‖a m‖ * ‖a n‖ * (2 / |ξ m - ξ n|) := hbound
    _ = _ := by ring

end Erdos374.PairSpacingKernel
end

#print axioms Erdos374.PairSpacingKernel.mean_square_error_le

run_cmd do
  let targets : List Lean.Name := [
    ``Erdos374.PairSpacingKernel.exponentialKernel,
    ``Erdos374.PairSpacingKernel.exponentialSum,
    ``Erdos374.PairSpacingKernel.continuous_kernel,
    ``Erdos374.PairSpacingKernel.norm_kernel,
    ``Erdos374.PairSpacingKernel.kernel_zero,
    ``Erdos374.PairSpacingKernel.kernel_mul_conj,
    ``Erdos374.PairSpacingKernel.integral_kernel,
    ``Erdos374.PairSpacingKernel.norm_integral_kernel_le,
    ``Erdos374.PairSpacingKernel.continuous_sum,
    ``Erdos374.PairSpacingKernel.norm_square_expansion,
    ``Erdos374.PairSpacingKernel.mean_square_expansion,
    ``Erdos374.PairSpacingKernel.mean_square_diagonal,
    ``Erdos374.PairSpacingKernel.mean_square_error_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#eval "HARMAN ANALYTIC : finite mean-square expansion and kernel bounds checked"

end
