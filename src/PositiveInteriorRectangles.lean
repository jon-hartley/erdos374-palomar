module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Set.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
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


/-! Exact finite geometry for the larger positive three-prime region.
The 253 rectangles use the corrected constraint 2*u+3*v <= 399/200.
This certificate does not identify a dyadic prime sum or an arithmetic count.
The factor (999/1000)^2 is retained explicitly as a scalar factor only. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
namespace PositiveInteriorRectangles

def start : ℝ := 447/1400
def finish : ℝ := 499/1000
def step : ℝ := (finish-start)/256
def left (i : ℕ) : ℝ := start+((i:ℝ)+3)*step
def right (i : ℕ) : ℝ := start+((i:ℝ)+4)*step
def lower (i : ℕ) : ℝ := 27/35-left i
def upper (i : ℕ) : ℝ := (399/200-2*right i)/3

def interior (u v : ℝ) : Prop :=
  9/35 ≤ u ∧ u ≤ 499/1000 ∧ 27/35 ≤ u+v ∧ 2*u+3*v ≤ 399/200

def rectangle (i : ℕ) : Set (ℝ × ℝ) :=
  Set.Ioc (left i) (right i) ×ˢ Set.Icc (lower i) (upper i)

def area (i : ℕ) : ℝ := (right i-left i)*(upper i-lower i)
def totalArea : ℝ := ∑ i ∈ Finset.range 253, area i
def coefficient : ℝ := 27*totalArea*(999/1000:ℝ)^2
def kernel (u v : ℝ) : ℝ := 1/(u*v*(1-u-v))

theorem step_pos : 0 < step := by norm_num [step, start, finish]

theorem width_eq (i : ℕ) : right i-left i=step := by
  unfold right left
  ring

theorem height_eq (i : ℕ) : upper i-lower i=((i:ℝ)+1)*step/3 := by
  norm_num [upper, lower, right, left, step, start, finish]
  ring

theorem endpoints_ordered (i : ℕ) : left i < right i ∧ lower i < upper i := by
  have h1 := width_eq i
  have h2 := height_eq i
  have hp := step_pos
  have hn : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  constructor
  · linarith
  · have hm : 0 < ((i:ℝ)+1)*step/3 := by positivity
    linarith

theorem endpoint_bounds (i : ℕ) (hi : i < 253) :
    start ≤ left i ∧ right i ≤ finish := by
  have hn : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have hle : (i:ℝ) ≤ 252 := by exact_mod_cast (show i ≤ 252 by omega)
  have hlo := mul_nonneg (show (0:ℝ) ≤ (i:ℝ)+3 by linarith) step_pos.le
  have hhi := mul_le_mul_of_nonneg_right (show (i:ℝ)+4 ≤ 256 by linarith)
    step_pos.le
  have he : start+256*step=finish := by unfold step; ring
  constructor
  · unfold left
    linarith
  · unfold right
    linarith

theorem closed_rectangle_subset (i : ℕ) (hi : i < 253) (u v : ℝ)
    (hu : u ∈ Set.Icc (left i) (right i))
    (hv : v ∈ Set.Icc (lower i) (upper i)) : interior u v := by
  have hb := endpoint_bounds i hi
  obtain ⟨hul, hur⟩ := hu
  obtain ⟨hvl, hvr⟩ := hv
  unfold lower at hvl
  unfold upper at hvr
  unfold start finish at hb
  unfold interior
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rectangle_subset (i : ℕ) (hi : i < 253) (p : ℝ × ℝ)
    (hp : p ∈ rectangle i) : interior p.1 p.2 :=
  closed_rectangle_subset i hi p.1 p.2 ⟨hp.1.1.le, hp.1.2⟩ hp.2

theorem right_le_left (i j : ℕ) (hij : i < j) : right i ≤ left j := by
  have he : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (Nat.add_one_le_iff.mpr hij)
  have hm := mul_le_mul_of_nonneg_right he step_pos.le
  unfold right left
  nlinarith

theorem index_unique (i j : ℕ) (u : ℝ)
    (hi : u ∈ Set.Ioc (left i) (right i))
    (hj : u ∈ Set.Ioc (left j) (right j)) : i=j := by
  rcases lt_trichotomy i j with h | h | h
  · have hh := right_le_left i j h
    linarith [hi.2, hj.1]
  · exact h
  · have hh := right_le_left j i h
    linarith [hj.2, hi.1]

theorem rectangles_disjoint (i j : ℕ) (hij : i ≠ j) :
    Disjoint (rectangle i) (rectangle j) := by
  rw [Set.disjoint_left]
  intro p hi hj
  exact hij (index_unique i j p.1 hi.1 hj.1)

theorem component_bounds (u v : ℝ) (h : interior u v) :
    1/4 ≤ u ∧ 1/4 ≤ v ∧ 1/6 ≤ 1-u-v := by
  rcases h with ⟨h1,h2,h3,h4⟩
  exact ⟨by linarith, by linarith, by linarith⟩

theorem denominator_bounds (u v : ℝ) (h : interior u v) :
    1/100 ≤ u*v*(1-u-v) ∧ u*v*(1-u-v) ≤ 1/27 := by
  obtain ⟨hu,hv,hw⟩ := component_bounds u v h
  have hu0 : 0 ≤ u := by linarith
  have huv : (1/4:ℝ)*(1/4) ≤ u*v :=
    mul_le_mul hu hv (by norm_num) (by linarith)
  have hp := mul_le_mul huv hw (by norm_num : (0:ℝ) ≤ 1/6)
    (by nlinarith : 0 ≤ u*v)
  have hsq := mul_nonneg hu0 (sq_nonneg (v-(1-u-v)))
  have hcube := mul_nonneg (by linarith : 0 ≤ 4/3-u) (sq_nonneg (u-1/3))
  constructor <;> nlinarith

theorem kernel_lower (u v : ℝ) (h : interior u v) : 27 ≤ kernel u v := by
  obtain ⟨hl,hu⟩ := denominator_bounds u v h
  unfold kernel
  apply (le_div_iff₀ (by linarith : 0 < u*v*(1-u-v))).mpr
  linarith

theorem kernel_on_rectangle (i : ℕ) (hi : i < 253) (p : ℝ × ℝ)
    (hp : p ∈ rectangle i) : 27 ≤ kernel p.1 p.2 :=
  kernel_lower _ _ (rectangle_subset i hi p hp)

theorem sum_successor (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i:ℝ)+1))=(N:ℝ)*((N:ℝ)+1)/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem area_eq (i : ℕ) : area i=(step^2/3)*((i:ℝ)+1) := by
  unfold area
  rw [width_eq, height_eq]
  ring

theorem total_area_exact : totalArea=(12712340971/2408448000000:ℝ) := by
  unfold totalArea
  simp_rw [area_eq]
  rw [← Finset.mul_sum, sum_successor]
  norm_num [step, finish, start]

theorem coefficient_exact :
    coefficient=(114182361012590739/802816000000000000:ℝ) := by
  rw [coefficient, total_area_exact]
  norm_num

theorem coefficient_gt_seven_fiftieths : (7/50:ℝ) < coefficient := by
  rw [coefficient_exact]
  norm_num

theorem coefficient_margin :
    coefficient-7/50=(1788121012590739/802816000000000000:ℝ) := by
  rw [coefficient_exact]
  norm_num

run_cmd do
  for decl in [``step_pos, ``width_eq, ``height_eq, ``endpoints_ordered,
      ``endpoint_bounds, ``closed_rectangle_subset, ``rectangle_subset,
      ``right_le_left, ``index_unique, ``rectangles_disjoint, ``component_bounds,
      ``denominator_bounds, ``kernel_lower, ``kernel_on_rectangle,
      ``sum_successor, ``area_eq, ``total_area_exact, ``coefficient_exact,
      ``coefficient_gt_seven_fiftieths, ``coefficient_margin] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "253 POSITIVE INTERIOR RECTANGLES: EXACT AREA AND SCALAR COEFFICIENT; NO ARITHMETIC TRANSFER"
end PositiveInteriorRectangles
end

end
