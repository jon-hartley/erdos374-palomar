module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
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
A quantitative logarithmic-derivative lemma on
an actual zero-free disk. The logarithm is constructed from a primitive of
f'/f, not postulated and not identified with the principal logarithm.
No statement here proves a zero-free region for zeta.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Set Metric Complex
namespace Item1ZeroFreeDisk

def logDerivative (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv f z / f z

theorem logDerivative_differentiableOn (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hn : ∀ z ∈ ball c R, f z ≠ 0) :
    DifferentiableOn ℂ (logDerivative f) (ball c R) := by
  exact (hf.deriv isOpen_ball).div hf hn

/-- A normalized holomorphic logarithm constructed by integrating f'/f.
The conclusion retains the derivative identity and the exact exponential
identity; there is no branch choice assumption in its arguments. -/
theorem normalized_logarithm (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hn : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g c = 0 ∧ ∀ z ∈ ball c R,
      HasDerivAt g (logDerivative f z) z ∧
      f z = Complex.exp (g z) * f c := by
  obtain ⟨g,hgc,hg⟩ :=
    (logDerivative_differentiableOn f c R hf hn).isExactOn_ball.with_val_at c 0
  have hc : c ∈ ball c R := by simpa using hR
  let q : ℂ → ℂ := fun z => Complex.exp (-g z) * f z
  have hq (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt q 0 z := by
    have hdf := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h := ((hg z hz).neg.cexp).mul hdf
    have he : (Complex.exp (-g z) * (-logDerivative f z)) * f z +
        Complex.exp (-g z) * deriv f z = 0 := by
      dsimp [logDerivative]
      field_simp [hn z hz]
      <;> ring
    change HasDerivAt q
      ((Complex.exp (-g z) * (-logDerivative f z)) * f z +
        Complex.exp (-g z) * deriv f z) z at h
    rw [he] at h
    exact h
  have hqd : DifferentiableOn ℂ q (ball c R) :=
    fun z hz => (hq z hz).differentiableAt.differentiableWithinAt
  have hq0 : EqOn (deriv q) 0 (ball c R) := fun z hz => (hq z hz).deriv
  have hqc (z : ℂ) (hz : z ∈ ball c R) : q z = f c := by
    have he := isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c R).isPreconnected hqd hq0 hz hc
    simpa [q,hgc] using he
  refine ⟨g,hgc,?_⟩
  intro z hz
  refine ⟨hg z hz,?_⟩
  calc
    f z = (Complex.exp (g z) * Complex.exp (-g z)) * f z := by
      rw [← Complex.exp_add]; simp
    _ = Complex.exp (g z) * q z := by dsimp [q]; ring
    _ = Complex.exp (g z) * f c := by rw [hqc z hz]

/-- Borel--Caratheodory after translation to the actual disk center. -/
theorem translated_borel (g : ℂ → ℂ) (c z : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball c R)) (hgc : g c = 0)
    (hre : ∀ w ∈ ball c R, (g w).re ≤ M) (hz : ‖z-c‖ < R) :
    ‖g z‖ ≤ 2*M*‖z-c‖/(R-‖z-c‖) := by
  let G : ℂ → ℂ := fun w => g (c+w)
  have hm (w : ℂ) (hw : w ∈ ball (0:ℂ) R) : c+w ∈ ball c R := by
    simpa [mem_ball,dist_eq_norm] using hw
  have hd : DifferentiableOn ℂ G (ball 0 R) := by
    intro w hw
    exact ((hg.differentiableAt (isOpen_ball.mem_nhds (hm w hw))).comp w
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
  have hb := Complex.borelCaratheodory_zero hM hd
    (fun w hw => hre _ (hm w hw)) hR
    (show z-c ∈ ball (0:ℂ) R by simpa [mem_ball,dist_eq_norm] using hz)
    (show G 0=0 by simpa [G] using hgc)
  simpa [G] using hb

/-- If the outer disk has radius 1+2d, the target radius 1+d leaves a
strict d-margin. No norm bound for a logarithmic derivative is assumed. -/
theorem logarithmic_derivative_disk (f : ℂ → ℂ) (c z : ℂ) (d M : ℝ)
    (hd : 0 < d) (hd1 : d ≤ 1/4) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball c (1+2*d)))
    (hn : ∀ w ∈ ball c (1+2*d), f w ≠ 0)
    (hb : ∀ w ∈ ball c (1+2*d), ‖f w‖ ≤ Real.exp M * ‖f c‖)
    (hz : ‖z-c‖ ≤ 1+d) :
    ‖deriv f z / f z‖ ≤ 16*M/d^2 := by
  have hR : 0 < 1+2*d := by linarith
  have hc : c ∈ ball c (1+2*d) := by simpa using hR
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hn c hc)
  obtain ⟨g,hgc,hg⟩ := normalized_logarithm f c (1+2*d) hR hf hn
  have hgd : DifferentiableOn ℂ g (ball c (1+2*d)) :=
    fun w hw => (hg w hw).1.differentiableAt.differentiableWithinAt
  have hre (w : ℂ) (hw : w ∈ ball c (1+2*d)) : (g w).re ≤ M := by
    have he := congrArg norm (hg w hw).2
    rw [norm_mul,Complex.norm_exp] at he
    have hle : Real.exp ((g w).re) * ‖f c‖ ≤ Real.exp M * ‖f c‖ := by
      rw [←he]; exact hb w hw
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_right hle hfc)
  have hsmall (w : ℂ) (hw : w ∈ closedBall z (d/2)) :
      ‖w-c‖ ≤ 1+3*d/2 := by
    have hh : ‖w-z‖ ≤ d/2 := by simpa [mem_closedBall,dist_eq_norm] using hw
    have ht : ‖w-c‖ ≤ ‖w-z‖+‖z-c‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (w-z) (z-c)
    linarith
  have hsub : closedBall z (d/2) ⊆ ball c (1+2*d) := by
    intro w hw
    change dist w c < 1+2*d
    rw [dist_eq_norm]
    linarith [hsmall w hw]
  have hboundary (w : ℂ) (hw : w ∈ sphere z (d/2)) : ‖g w‖ ≤ 8*M/d := by
    have hwc : w ∈ closedBall z (d/2) := sphere_subset_closedBall hw
    have hr := hsmall w hwc
    have hri : ‖w-c‖ < 1+2*d := by linarith
    have hden : 0 < 1+2*d-‖w-c‖ := by linarith
    have hr2 : ‖w-c‖ ≤ 2 := by linarith
    have hgrowth := translated_borel g c w (1+2*d) M hR hM hgd hgc hre hri
    apply hgrowth.trans
    apply (div_le_div_iff₀ hden hd).mpr
    calc
      (2*M*‖w-c‖)*d ≤ ((2*M)*2)*d :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr2 (by positivity)) hd.le
      _ = (4*M)*d := by ring
      _ ≤ (8*M)*(1+2*d-‖w-c‖) := by
        have hgap : d/2 ≤ 1+2*d-‖w-c‖ := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hgap (by positivity : 0≤8*M)]
  have hdg : DiffContOnCl ℂ g (ball z (d/2)) := by
    apply DiffContOnCl.mk_ball
    · exact hgd.mono (ball_subset_closedBall.trans hsub)
    · exact (hgd.mono hsub).continuousOn
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (show 0<d/2 by positivity) hdg hboundary
  have hzbig : z ∈ ball c (1+2*d) := by
    rw [mem_ball,dist_eq_norm]; linarith
  rw [(hg z hzbig).1.deriv] at hder
  dsimp [logDerivative] at hder
  convert hder using 1 <;> field_simp <;> ring

end Item1ZeroFreeDisk

run_cmd do
  for target in [``Item1ZeroFreeDisk.logDerivative_differentiableOn,
    ``Item1ZeroFreeDisk.normalized_logarithm, ``Item1ZeroFreeDisk.translated_borel,
    ``Item1ZeroFreeDisk.logarithmic_derivative_disk] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1ZeroFreeDisk.normalized_logarithm
#print axioms Item1ZeroFreeDisk.logarithmic_derivative_disk
