module

public import Mathlib.NumberTheory.LSeries.Dirichlet
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
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Data.List.Enum
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Integral.Layercake
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


/-!
The three-mode Euler positivity inequality for the ACTUAL zeta logarithmic
 derivative. All infinite series are used in Re(s)>1. No zero-free region
left of one, polynomial cap, or assumed positivity statement is an input.
The positive-integer L-series conversion is adapted from the retained
Item1RampDirichlet; it is reproduced here to avoid importing its Mellin chain.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Complex
open scoped BigOperators
namespace Item1EulerZeroDetector

def F (s : ℂ) : ℂ := -deriv riemannZeta s / riemannZeta s

def term (s : ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt (n+1) : ℂ) *
    Complex.exp (-s * (Real.log (n+1:ℕ) : ℂ))

def realTerm (σ t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n+1) *
    Real.exp (-σ * Real.log (n+1:ℕ)) * Real.cos (t * Real.log (n+1:ℕ))

theorem cpow_positive_exp (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x:ℂ)^s = Complex.exp (s*(Real.log x:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
  rw [←Complex.ofReal_log hx.le]
  congr 1
  ring

theorem lseries_term_exp (s : ℂ) (n : ℕ) :
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ)) s (n+1) =
      term s n := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  simp only [LSeries.term,show n+1 ≠ 0 by omega,if_false]
  have hpow := cpow_positive_exp ((n+1:ℕ):ℝ) hn s
  simp only [Complex.ofReal_natCast] at hpow
  rw [hpow,div_eq_mul_inv,←Complex.exp_neg]
  unfold term
  congr 2
  ring

/-- Absolute convergence and the genuine logarithmic-derivative series. -/
theorem hasSum_F (s : ℂ) (hs : 1 < s.re) : HasSum (term s) (F s) := by
  have hi : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hi1 : Summable (term s) := by
    simpa only [lseries_term_exp] using (summable_nat_add_iff 1).2 hi
  have hzero := hi.tsum_eq_zero_add
  have ht0 : LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) s 0 = 0 := by
    simp [LSeries.term]
  rw [ht0,zero_add] at hzero
  have hζ := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change (∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ)) s n) = F s at hζ
  rw [hzero] at hζ
  have he : (∑' n, term s n) = F s := by simpa only [lseries_term_exp] using hζ
  simpa only [he] using hi1.hasSum

theorem term_re (σ t : ℝ) (n : ℕ) :
    (term ((σ:ℂ)+(t:ℂ)*Complex.I) n).re = realTerm σ t n := by
  have hr : (-((σ:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n+1:ℕ):ℂ)).re =
      -σ*Real.log (n+1:ℕ) := by simp
  have hm : (-((σ:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n+1:ℕ):ℂ)).im =
      -(t*Real.log (n+1:ℕ)) := by simp
  simp only [term,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.exp_re,hr,hm,Real.cos_neg,realTerm]
  ring

theorem hasSum_real_F (σ t : ℝ) (hσ : 1 < σ) :
    HasSum (realTerm σ t) (F ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by
  have hh := Complex.hasSum_re (hasSum_F ((σ:ℂ)+(t:ℂ)*Complex.I) (by simpa using hσ))
  simpa only [term_re] using hh

/-- The exact nonnegative trigonometric polynomial, not a numerical sample. -/
theorem trig_identity (θ : ℝ) :
    3+4*Real.cos θ+Real.cos (2*θ) = 2*(1+Real.cos θ)^2 := by
  rw [Real.cos_two_mul]
  ring

theorem three_terms (σ t : ℝ) (n : ℕ) :
    3*realTerm σ 0 n + 4*realTerm σ t n + realTerm σ (2*t) n =
      2*ArithmeticFunction.vonMangoldt (n+1)*Real.exp (-σ*Real.log (n+1:ℕ))*
        (1+Real.cos (t*Real.log (n+1:ℕ)))^2 := by
  unfold realTerm
  simp only [zero_mul,Real.cos_zero,mul_one]
  rw [show (2*t)*Real.log (n+1:ℕ) = 2*(t*Real.log (n+1:ℕ)) by ring,
    Real.cos_two_mul]
  ring

/-- The arithmetic positivity inequality, with only the Re(s)>1 guard. -/
theorem three_mode_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3*(F (σ:ℂ)).re + 4*(F ((σ:ℂ)+(t:ℂ)*Complex.I)).re +
      (F ((σ:ℂ)+((2*t:ℝ):ℂ)*Complex.I)).re := by
  have h0 := hasSum_real_F σ 0 hσ
  have h1 := hasSum_real_F σ t hσ
  have h2 := hasSum_real_F σ (2*t) hσ
  have hsum := ((HasSum.mul_left (3:ℝ) h0).add
    (HasSum.mul_left (4:ℝ) h1)).add h2
  have hn : 0 ≤ ∑' n : ℕ,
      (3*realTerm σ 0 n+4*realTerm σ t n+realTerm σ (2*t) n) := by
    apply tsum_nonneg
    intro n
    rw [three_terms]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
        ArithmeticFunction.vonMangoldt_nonneg) (Real.exp_pos _).le)
      (sq_nonneg _)
  rw [hsum.tsum_eq] at hn
  simpa using hn

#print axioms three_mode_nonneg
run_cmd do
  let targets : List Lean.Name := [
    ``cpow_positive_exp, ``lseries_term_exp, ``hasSum_F, ``term_re,
    ``hasSum_real_F, ``trig_identity, ``three_terms, ``three_mode_nonneg]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Item1EulerZeroDetector
