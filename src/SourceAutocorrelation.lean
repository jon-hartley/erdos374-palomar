module

public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.JacobianOneDim
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
v9. Parseval for an integrable bounded function continuous almost everywhere.
STATUS: UNCOMPILED PROOF DRAFT. The sharp function need not be continuous.
Inversion is applied to its autocorrelation. The Fourier-square integrability
premise is qualitative regularity, not a small-energy or physical-mean bound.
The actual-source instantiation is a separate module.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate FourierTransform Topology
namespace SourceAutocorrelation

def reflected (g : ℝ → ℂ) (u : ℝ) : ℂ := conj (g (-u))

def correlation (g : ℝ → ℂ) : ℝ → ℂ :=
  MeasureTheory.convolution g (reflected g) (ContinuousLinearMap.mul ℂ ℂ) volume

theorem correlation_integral (g : ℝ → ℂ) (x : ℝ) :
    correlation g x = ∫ u : ℝ, g u * conj (g (u-x)) := by
  simp only [correlation, MeasureTheory.convolution_mul, reflected, neg_sub]

theorem reflected_measurable (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (reflected g) := by
  exact Complex.continuous_conj.measurable.comp (hg.comp measurable_neg)

theorem reflected_integrable (g : ℝ → ℂ) (hg : Measurable g)
    (hi : Integrable g) : Integrable (reflected g) := by
  apply hi.comp_neg.norm.mono' (reflected_measurable g hg).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    simp only [reflected, Complex.norm_conj]
    exact le_rfl)

theorem correlation_integrable (g : ℝ → ℂ) (hg : Measurable g)
    (hi : Integrable g) : Integrable (correlation g) := by
  exact MeasureTheory.Integrable.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hi (reflected_integrable g hg hi)

/-- The value at zero is proved independently of Fourier inversion. -/
theorem correlation_zero (g : ℝ → ℂ) :
    correlation g 0 = ((∫ u : ℝ, ‖g u‖^2) : ℂ) := by
  rw [correlation_integral]
  simp only [sub_zero]
  apply integral_congr_ae
  filter_upwards with u
  rw [← Complex.mul_conj']

/-- Boundedness plus L1 gives genuine L2 integrability. -/
theorem square_integrable (g : ℝ → ℂ) (B : ℝ) (hg : Measurable g)
    (hi : Integrable g) (_hB : 0 ≤ B) (hb : ∀ u, ‖g u‖ ≤ B) :
    Integrable (fun u => ‖g u‖^2) := by
  apply (hi.norm.const_mul B).mono' (hg.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_right (hb u) (norm_nonneg (g u))]

/-- Dominated convergence at zero does not ask for continuity at the jumps.
The dominating function B*|g| is integrable before Parseval is used. -/
theorem correlation_continuousAt_zero (g : ℝ → ℂ) (B : ℝ)
    (hg : Measurable g) (hi : Integrable g) (_hB : 0 ≤ B)
    (hb : ∀ u, ‖g u‖ ≤ B) (hc : ∀ᵐ u : ℝ, ContinuousAt g u) :
    ContinuousAt (correlation g) 0 := by
  let F : ℝ → ℝ → ℂ := fun x u => g u * conj (g (u-x))
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (F x) := by
    intro x
    exact (hg.mul (Complex.continuous_conj.measurable.comp
      (hg.comp (measurable_id.sub_const x)))).aestronglyMeasurable
  have hbound : ∀ x : ℝ, ∀ᵐ u : ℝ, ‖F x u‖ ≤ B*‖g u‖ := by
    intro x
    filter_upwards with u
    simp only [F, norm_mul, Complex.norm_conj]
    nlinarith [mul_le_mul_of_nonneg_left (hb (u-x)) (norm_nonneg (g u))]
  have hlim : ∀ᵐ u : ℝ, Tendsto (fun x => F x u) (𝓝 0) (𝓝 (F 0 u)) := by
    filter_upwards [hc] with u hu
    have ht : Tendsto (fun x : ℝ => u-x) (𝓝 0) (𝓝 u) := by
      have hc0 : ContinuousAt (fun x : ℝ => u-x) 0 :=
        (continuous_const.sub continuous_id).continuousAt
      simpa only [sub_zero] using hc0.tendsto
    simp only [F, sub_zero]
    exact tendsto_const_nhds.mul (Complex.continuous_conj.continuousAt.tendsto.comp
      (hu.tendsto.comp ht))
  have hh := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => B*‖g u‖) (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall hbound) (hi.norm.const_mul B) hlim
  have heq : correlation g = fun x : ℝ => ∫ u : ℝ, F x u := by
    funext x
    exact correlation_integral g x
  change Tendsto (correlation g) (𝓝 0) (𝓝 (correlation g 0))
  rw [heq]
  exact hh

/-- Conjugate reflection, with Mathlib's ordinary Fourier convention. -/
theorem fourier_reflected (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (reflected g) ξ = conj (𝓕 g ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  -- Use the actual standard Fourier integrand; no sign convention is implicit.
  change (∫ u : ℝ, Complex.exp (((-2*Real.pi*u*ξ:ℝ):ℂ)*Complex.I) * reflected g u) = _
  rw [← integral_neg_eq_self
    (fun u : ℝ => Complex.exp (((-2*Real.pi*u*ξ:ℝ):ℂ)*Complex.I)*reflected g u)]
  apply integral_congr_ae
  filter_upwards with u
  simp only [reflected, neg_neg, smul_eq_mul, map_mul, ← Complex.exp_conj,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

theorem fourier_correlation (g : ℝ → ℂ) (hg : Measurable g)
    (hi : Integrable g) (ξ : ℝ) :
    𝓕 (correlation g) ξ = ((‖𝓕 g ξ‖^2:ℝ):ℂ) := by
  rw [correlation, Real.fourier_mul_convolution_eq hi (reflected_integrable g hg hi),
    fourier_reflected, Complex.ofReal_pow, ← Complex.mul_conj']

/-- Standard-frequency Parseval, proved by ordinary L1 inversion of the
continuous-at-zero autocorrelation, not assumed as an extra analytic input. -/
theorem parseval (g : ℝ → ℂ) (B : ℝ) (hg : Measurable g)
    (hi : Integrable g) (hB : 0 ≤ B) (hb : ∀ u, ‖g u‖ ≤ B)
    (hc : ∀ᵐ u : ℝ, ContinuousAt g u)
    (hF : Integrable (fun ξ : ℝ => ‖𝓕 g ξ‖^2)) :
    (∫ u : ℝ, ‖g u‖^2) = ∫ ξ : ℝ, ‖𝓕 g ξ‖^2 := by
  have hAi := correlation_integrable g hg hi
  have hAF : Integrable (𝓕 (correlation g)) := by
    have he : 𝓕 (correlation g) = fun ξ : ℝ => ((‖𝓕 g ξ‖^2:ℝ):ℂ) := by
      funext ξ
      exact fourier_correlation g hg hi ξ
    rw [he]
    exact hF.ofReal
  have hinv := hAi.fourierInv_fourier_eq hAF
    (correlation_continuousAt_zero g B hg hi hB hb hc)
  have hzero : 𝓕⁻ (𝓕 (correlation g)) (0:ℝ) =
      ∫ ξ : ℝ, 𝓕 (correlation g) ξ := by
    rw [Real.fourierInv_eq']
    simp
  rw [hzero, correlation_zero] at hinv
  simp_rw [fourier_correlation g hg hi] at hinv
  simp only [← Complex.ofReal_pow, integral_complex_ofReal] at hinv
  exact Complex.ofReal_injective hinv.symm

#print axioms parseval
run_cmd do
  for n in [``correlation_integral, ``reflected_measurable, ``reflected_integrable,
      ``correlation_integrable, ``correlation_zero, ``square_integrable,
      ``correlation_continuousAt_zero, ``fourier_reflected,
      ``fourier_correlation, ``parseval] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V9 AUTOCORRELATION PARSEVAL: VALID ONLY AFTER ACTUAL COMPILATION"
end SourceAutocorrelation
