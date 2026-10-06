module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
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
public import Mathlib.Analysis.Complex.HalfPlane
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


/-! The only arithmetic proposition introduced here is literal
nonvanishing of riemannZeta. It is NOT proved in this package. The disk
inclusions below are elementary and retain a strict boundary margin. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Set Metric Complex
namespace Item1ZetaDiskGeometry

def BarePositiveZeroFree (b T₀ : ℝ) : Prop :=
  ∀ σ y : ℝ, T₀ ≤ y →
    1-b/(Real.log y)^(3/4:ℝ) ≤ σ → σ ≤ 4 →
    riemannZeta ((σ:ℂ)+(y:ℂ)*Complex.I) ≠ 0

def center (y : ℝ) : ℂ := 2+(y:ℂ)*Complex.I
def depth (b y : ℝ) : ℝ := b/(8*(Real.log y)^(3/4:ℝ))

theorem depth_guards (b y : ℝ) (hb : 0<b) (hb1 : b≤1/2)
    (hlog : 1≤Real.log y) : 0<depth b y ∧ depth b y≤1/4 := by
  have hp : 0<(Real.log y)^(3/4:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have h1 : 1≤(Real.log y)^(3/4:ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hlog
      (by norm_num : (0:ℝ)≤3/4)
  constructor
  · exact div_pos hb (by positivity)
  · unfold depth
    apply (div_le_iff₀ (by positivity : 0<8*(Real.log y)^(3/4:ℝ))).mpr
    linarith

theorem disk_coordinates (y d : ℝ) (hy : 4≤y) (hd : d≤1/4)
    (w : ℂ) (hw : w∈ball (center y) (1+2*d)) :
    1-2*d<w.re ∧ w.re<4 ∧ y/2<w.im ∧ w.im<2*y := by
  have hn : ‖w-center y‖<1+2*d := by simpa [mem_ball,dist_eq_norm] using hw
  have hre := (abs_re_le_norm (w-center y)).trans_lt hn
  have him := (abs_im_le_norm (w-center y)).trans_lt hn
  norm_num [center] at hre him
  have hr := abs_lt.mp hre
  have hi := abs_lt.mp him
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem target_inner (b y σ : ℝ) (hσ : 1-depth b y≤σ) (hσ1 : σ≤2) :
    ‖((σ:ℂ)+(y:ℂ)*Complex.I)-center y‖≤1+depth b y := by
  have he : ((σ:ℂ)+(y:ℂ)*Complex.I)-center y = ((σ-2:ℝ):ℂ) := by
    unfold center; push_cast; ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
  linarith

/-- The outer disk fits in the hypothesized zero-free region, not just the
smaller target strip. Nearby heights are explicitly compared. -/
theorem disk_nonvanishing (b T₀ y : ℝ) (hb : 0<b) (hb1 : b≤1/2)
    (hT : 4≤T₀) (hy : 4≤y) (hyT : 2*T₀≤y) (hlog : 1≤Real.log y)
    (hzero : BarePositiveZeroFree b T₀) :
    ∀ w∈ball (center y) (1+2*depth b y), riemannZeta w≠0 := by
  intro w hw
  obtain ⟨hd,hd1⟩ := depth_guards b y hb hb1 hlog
  obtain ⟨hrlo,hrhi,hylo,hyhi⟩ := disk_coordinates y (depth b y) hy hd1 w hw
  have hwT : T₀≤w.im := by linarith
  have hwp : 0<w.im := by linarith
  have hL : 0<Real.log y := by linarith
  have hLw : 0<Real.log w.im := Real.log_pos (by linarith)
  have hlogs : Real.log w.im≤2*Real.log y := by
    calc
      Real.log w.im ≤ Real.log (2*y) := Real.log_le_log hwp hyhi.le
      _ = Real.log 2+Real.log y := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2*Real.log y := by
        have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ)≤y)
        linarith
  have hP : 0<(Real.log y)^(3/4:ℝ) := Real.rpow_pos_of_pos hL _
  have hPw : 0<(Real.log w.im)^(3/4:ℝ) := Real.rpow_pos_of_pos hLw _
  have hpower : (Real.log w.im)^(3/4:ℝ)≤2*(Real.log y)^(3/4:ℝ) := by
    calc
      _ ≤ (2*Real.log y)^(3/4:ℝ) :=
        Real.rpow_le_rpow hLw.le hlogs (by norm_num)
      _ = (2:ℝ)^(3/4:ℝ)*(Real.log y)^(3/4:ℝ) :=
        Real.mul_rpow (by norm_num) hL.le
      _ ≤ 2*(Real.log y)^(3/4:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hP.le
        exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hmargin : 2*depth b y ≤ b/(Real.log w.im)^(3/4:ℝ) := by
    apply (le_div_iff₀ hPw).mpr
    calc
      (2*depth b y)*(Real.log w.im)^(3/4:ℝ)
          ≤ (2*depth b y)*(2*(Real.log y)^(3/4:ℝ)) :=
            mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = b/2 := by unfold depth; field_simp; ring
      _ ≤ b := by linarith
  have hz := hzero w.re w.im hwT (by linarith) hrhi.le
  simpa only [Complex.re_add_im] using hz

theorem zeta_differentiable_disk (y d : ℝ) (hy : 4≤y) (hd : d≤1/4) :
    DifferentiableOn ℂ riemannZeta (ball (center y) (1+2*d)) := by
  intro w hw
  have hi := (disk_coordinates y d hy hd w hw).2.2.1
  apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro he
  have him := congrArg Complex.im he
  norm_num at him
  linarith

/-- The deliberately loose disk derivative loss is still far below log^9. -/
theorem depth_budget (b y : ℝ) (hb : 0<b) (hL : 1≤Real.log y) :
    16*(3*Real.log y)/(depth b y)^2 ≤ (3072/b^2)*(Real.log y)^9 := by
  have hLp : 0<Real.log y := by linarith
  have hp : 0<(Real.log y)^(3/4:ℝ) := Real.rpow_pos_of_pos hLp _
  have he : ((Real.log y)^(3/4:ℝ))^2 = (Real.log y)^(3/2:ℝ) := by
    rw [←Real.rpow_mul_natCast hLp.le (3/4:ℝ) 2]
    norm_num
  have he' : Real.log y*(Real.log y)^(3/2:ℝ) = (Real.log y)^(5/2:ℝ) := by
    calc
      _ = (Real.log y)^(1:ℝ)*(Real.log y)^(3/2:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hLp]; norm_num
  have hid : 16*(3*Real.log y)/(depth b y)^2 =
      (3072/b^2)*(Real.log y)^(5/2:ℝ) := by
    unfold depth
    field_simp
    rw [he]
    nlinarith [he']
  rw [hid]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  convert
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (5/2:ℝ)≤(9:ℝ))
    using 1 <;> norm_num

end Item1ZetaDiskGeometry

run_cmd do
  for target in [``Item1ZetaDiskGeometry.depth_guards,
    ``Item1ZetaDiskGeometry.disk_coordinates,
    ``Item1ZetaDiskGeometry.target_inner,
    ``Item1ZetaDiskGeometry.disk_nonvanishing,
    ``Item1ZetaDiskGeometry.zeta_differentiable_disk,
    ``Item1ZetaDiskGeometry.depth_budget] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1ZetaDiskGeometry.disk_nonvanishing
#print axioms Item1ZetaDiskGeometry.depth_budget
