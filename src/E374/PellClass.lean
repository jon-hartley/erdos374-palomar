module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.GCD
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
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.RingTheory.PrincipalIdealDomain
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


/-!
# An elementary count for `e₁ u² − e₂ v² = d`

For `e₁, e₂, d ≥ 1`,
  `#{u ∈ [1, X] : ∃ v, e₁ u² − e₂ v² = d} ≤ d² · (log₂(2 √e₁ X) + 1)`.

Proof (classical "classes of solutions"). Put `α(u,v) = √e₁ u + √e₂ v`.
If two solutions have `u ≡ u'`, `v ≡ v' (mod d)`, then `P = e₁uu' − e₂vv'` and
`Q = vu' − uv'` are divisible by `d`, `(P/d)² − e₁e₂ (Q/d)² = 1`, and
`α(u,v) / α(u',v') = P/d + √(e₁e₂) · Q/d`. A norm-one element `x + y√(e₁e₂) > 1`
with `x, y ∈ ℤ` has `x, y ≥ 1`, hence is `≥ 2`. So within a residue class the values
`α` are pairwise at ratio `≥ 2`, and therefore have distinct `⌊log₂ α⌋`. Since
`1 ≤ α ≤ 2√e₁ X`, each class contributes at most `log₂(2√e₁X) + 1` solutions, and there
are at most `d²` classes.

This replaces Tao's Lemma 2.10 in the small-kernel count: there `d ≤ H = X^η` with
`η` arbitrarily small, so `d² log X ≪ X^ε` suffices.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
open Finset

namespace Erdos374.D35

/-- A norm-one element `x + y s` with `s ≥ 1`, `x, y ∈ ℤ`, lying in `[1, 2)` equals `1`. -/
theorem norm_one_unit_eq_one {x y : ℤ} {s ρ : ℝ} (hs : 1 ≤ s) (hρ : ρ = x + s * y)
    (hnorm : (x : ℝ) ^ 2 - s ^ 2 * (y : ℝ) ^ 2 = 1) (h1 : 1 ≤ ρ) (h2 : ρ < 2) : ρ = 1 := by
  by_contra hne
  have hgt : 1 < ρ := lt_of_le_of_ne h1 (Ne.symm hne)
  set τ : ℝ := x - s * y with hτ
  have hρτ : ρ * τ = 1 := by rw [hρ, hτ]; nlinarith [hnorm]
  have hρ0 : 0 < ρ := by linarith
  have hτ0 : 0 < τ := by
    by_contra h; push_neg at h
    have : ρ * τ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ0.le h
    linarith
  have hτ1 : τ < 1 := by
    by_contra h; push_neg at h
    have : 1 < ρ * τ := by nlinarith
    linarith
  -- x = (ρ + τ)/2 > 0, s y = (ρ − τ)/2 > 0
  have hx : (0 : ℝ) < x := by
    have : (x : ℝ) = (ρ + τ) / 2 := by rw [hρ, hτ]; ring
    rw [this]; linarith
  have hy : (0 : ℝ) < s * y := by
    have : s * (y : ℝ) = (ρ - τ) / 2 := by rw [hρ, hτ]; ring
    rw [this]; linarith
  have hy' : (0 : ℝ) < y := by
    by_contra h; push_neg at h
    have : s * (y : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    linarith
  have hx1 : (1 : ℝ) ≤ x := by
    have : (0 : ℤ) < x := by exact_mod_cast hx
    exact_mod_cast this
  have hy1 : (1 : ℝ) ≤ y := by
    have : (0 : ℤ) < y := by exact_mod_cast hy'
    exact_mod_cast this
  have : (2 : ℝ) ≤ ρ := by
    rw [hρ]; nlinarith
  linarith

/-- Two solutions in the same residue class mod `d` whose `α`-values satisfy
`α' ≤ α < 2 α'` have equal `α`. -/
theorem alpha_eq_of_class {e1 e2 d u v u' v' : ℕ} (he1 : 1 ≤ e1) (he2 : 1 ≤ e2) (hd : 1 ≤ d)
    (h : (e1 : ℤ) * (u : ℤ) ^ 2 - d = e2 * (v : ℤ) ^ 2)
    (h' : (e1 : ℤ) * (u' : ℤ) ^ 2 - d = e2 * (v' : ℤ) ^ 2)
    (hu : u % d = u' % d) (hv : v % d = v' % d)
    (hle : Real.sqrt e1 * u' + Real.sqrt e2 * v' ≤ Real.sqrt e1 * u + Real.sqrt e2 * v)
    (hlt : Real.sqrt e1 * u + Real.sqrt e2 * v < 2 * (Real.sqrt e1 * u' + Real.sqrt e2 * v')) :
    Real.sqrt e1 * u + Real.sqrt e2 * v = Real.sqrt e1 * u' + Real.sqrt e2 * v' := by
  -- integer divisibility
  have huz : (u : ℤ) ≡ u' [ZMOD d] := by
    rw [Int.ModEq]; exact_mod_cast hu
  have hvz : (v : ℤ) ≡ v' [ZMOD d] := by
    rw [Int.ModEq]; exact_mod_cast hv
  have hPd : (d : ℤ) ∣ (e1 : ℤ) * u * u' - e2 * v * v' := by
    have h1 : (e1 : ℤ) * u * u' - e2 * v * v' ≡ e1 * u * u - e2 * v * v [ZMOD d] :=
      Int.ModEq.sub (Int.ModEq.mul_left _ huz.symm) (Int.ModEq.mul_left _ hvz.symm)
    have h2 : (e1 : ℤ) * u * u - e2 * v * v = d := by linear_combination h
    rw [h2] at h1
    have h3 := Int.ModEq.dvd h1
    have h4 : (e1 : ℤ) * u * u' - e2 * v * v' =
        d - (d - ((e1 : ℤ) * u * u' - e2 * v * v')) := by ring
    rw [h4]; exact dvd_sub (dvd_refl _) h3
  have hQd : (d : ℤ) ∣ (v : ℤ) * u' - u * v' := by
    have h1 : (v : ℤ) * u' - u * v' ≡ v * u - u * v [ZMOD d] :=
      Int.ModEq.sub (Int.ModEq.mul_left _ huz.symm) (Int.ModEq.mul_left _ hvz.symm)
    have h2 : (v : ℤ) * u - u * v = 0 := by ring
    rw [h2] at h1
    have h3 := Int.ModEq.dvd h1
    rw [← dvd_neg]; convert h3 using 1; ring
  obtain ⟨X, hX⟩ := hPd
  obtain ⟨Y, hY⟩ := hQd
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hnormZ : X ^ 2 - (e1 : ℤ) * e2 * Y ^ 2 = 1 := by
    have hid : ((e1 : ℤ) * u * u' - e2 * v * v') ^ 2 - (e1 : ℤ) * e2 * ((v : ℤ) * u' - u * v') ^ 2 =
        (d : ℤ) * d := by
      linear_combination ((e1 : ℤ) * (u' : ℤ) ^ 2 - e2 * (v' : ℤ) ^ 2) * h + (d : ℤ) * h'
    rw [hX, hY] at hid
    have : (d : ℤ) * d * (X ^ 2 - (e1 : ℤ) * e2 * Y ^ 2) = (d : ℤ) * d * 1 := by
      linear_combination hid
    exact mul_left_cancel₀ (mul_ne_zero hdz hdz) this
  -- real part
  set s1 := Real.sqrt e1 with hs1
  set s2 := Real.sqrt e2 with hs2
  have he1R : (1 : ℝ) ≤ e1 := by exact_mod_cast he1
  have he2R : (1 : ℝ) ≤ e2 := by exact_mod_cast he2
  have hs1sq : s1 ^ 2 = e1 := Real.sq_sqrt (by linarith)
  have hs2sq : s2 ^ 2 = e2 := Real.sq_sqrt (by linarith)
  have hs1g : 1 ≤ s1 := by rw [hs1]; exact Real.one_le_sqrt.mpr he1R
  have hs2g : 1 ≤ s2 := by rw [hs2]; exact Real.one_le_sqrt.mpr he2R
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : (e1 : ℝ) * (u : ℝ) ^ 2 - d = e2 * (v : ℝ) ^ 2 := by exact_mod_cast h
  have hR' : (e1 : ℝ) * (u' : ℝ) ^ 2 - d = e2 * (v' : ℝ) ^ 2 := by exact_mod_cast h'
  have hXR : (e1 : ℝ) * u * u' - e2 * v * v' = d * X := by exact_mod_cast hX
  have hYR : (v : ℝ) * u' - u * v' = d * Y := by exact_mod_cast hY
  have hnormR : (X : ℝ) ^ 2 - (e1 : ℝ) * e2 * (Y : ℝ) ^ 2 = 1 := by exact_mod_cast hnormZ
  set α := s1 * u + s2 * v with hα
  set α' := s1 * u' + s2 * v' with hα'
  set β' := s1 * u' - s2 * v' with hβ'
  have hαβ' : α' * β' = d := by
    rw [hα', hβ']
    have : (s1 * u' + s2 * v') * (s1 * u' - s2 * v') = s1 ^ 2 * u' ^ 2 - s2 ^ 2 * v' ^ 2 := by ring
    rw [this, hs1sq, hs2sq]; linarith
  set s := s1 * s2 with hs
  have hsg : 1 ≤ s := by rw [hs]; nlinarith
  have hssq : s ^ 2 = e1 * e2 := by rw [hs, mul_pow, hs1sq, hs2sq]
  set ρ : ℝ := X + s * Y with hρ
  have hαρ : α * β' = d * ρ := by
    rw [hα, hβ', hρ]
    have : (s1 * u + s2 * v) * (s1 * u' - s2 * v') =
        s1 ^ 2 * u * u' - s2 ^ 2 * v * v' + s1 * s2 * (v * u' - u * v') := by ring
    rw [this, hs1sq, hs2sq, hYR, hXR, ← hs]; ring
  have hα'0 : 0 < α' := by
    have h0 : 0 ≤ α' := by rw [hα']; positivity
    rcases h0.lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, zero_mul] at hαβ'; linarith
  have hβ'0 : β' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hαβ'; linarith
  have hαeq : α = ρ * α' := by
    have : α * β' = (ρ * α') * β' := by rw [hαρ, mul_assoc, hαβ']; ring
    exact mul_right_cancel₀ hβ'0 this
  have hρ1 : 1 ≤ ρ := by
    by_contra hc; push_neg at hc
    have : ρ * α' < 1 * α' := mul_lt_mul_of_pos_right hc hα'0
    linarith
  have hρ2 : ρ < 2 := by
    by_contra hc; push_neg at hc
    have : 2 * α' ≤ ρ * α' := mul_le_mul_of_nonneg_right hc hα'0.le
    linarith
  have hρone := norm_one_unit_eq_one (x := X) (y := Y) hsg hρ
    (by rw [hssq]; linarith [hnormR]) hρ1 hρ2
  rw [hαeq, hρone, one_mul]

/-- Same class and same dyadic level `⌊log₂ α⌋` force the same `u`. -/
theorem u_eq_of_class {e1 e2 d u v u' v' : ℕ} (he1 : 1 ≤ e1) (he2 : 1 ≤ e2) (hd : 1 ≤ d)
    (h : (e1 : ℤ) * (u : ℤ) ^ 2 - d = e2 * (v : ℤ) ^ 2)
    (h' : (e1 : ℤ) * (u' : ℤ) ^ 2 - d = e2 * (v' : ℤ) ^ 2)
    (hu : u % d = u' % d) (hv : v % d = v' % d)
    (hlev : ⌊Real.logb 2 (Real.sqrt e1 * u + Real.sqrt e2 * v)⌋₊ =
      ⌊Real.logb 2 (Real.sqrt e1 * u' + Real.sqrt e2 * v')⌋₊) :
    u = u' := by
  have he1R : (1 : ℝ) ≤ e1 := by exact_mod_cast he1
  have he2R : (1 : ℝ) ≤ e2 := by exact_mod_cast he2
  have hs1g : 1 ≤ Real.sqrt e1 := Real.one_le_sqrt.mpr he1R
  have hs2g : 1 ≤ Real.sqrt e2 := Real.one_le_sqrt.mpr he2R
  -- u, u' ≥ 1
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0] at h; push_cast at h
      have : (0 : ℤ) ≤ e2 * (v : ℤ) ^ 2 := by positivity
      omega
    · exact h0
  have hu1' : 1 ≤ u' := by
    rcases Nat.eq_zero_or_pos u' with h0 | h0
    · rw [h0] at h'; push_cast at h'
      have : (0 : ℤ) ≤ e2 * (v' : ℤ) ^ 2 := by positivity
      omega
    · exact h0
  set α := Real.sqrt e1 * u + Real.sqrt e2 * v with hα
  set α' := Real.sqrt e1 * u' + Real.sqrt e2 * v' with hα'
  have hα1 : 1 ≤ α := by
    have : (1 : ℝ) ≤ u := by exact_mod_cast hu1
    have : (0 : ℝ) ≤ Real.sqrt e2 * v := by positivity
    rw [hα]; nlinarith
  have hα1' : 1 ≤ α' := by
    have : (1 : ℝ) ≤ u' := by exact_mod_cast hu1'
    have : (0 : ℝ) ≤ Real.sqrt e2 * v' := by positivity
    rw [hα']; nlinarith
  -- dyadic window
  have hb : (1 : ℝ) < 2 := by norm_num
  have window : ∀ a : ℝ, 1 ≤ a →
      (2 : ℝ) ^ (⌊Real.logb 2 a⌋₊ : ℝ) ≤ a ∧ a < 2 * (2 : ℝ) ^ (⌊Real.logb 2 a⌋₊ : ℝ) := by
    intro a ha
    have ha0 : 0 < a := by linarith
    have hl0 : 0 ≤ Real.logb 2 a := Real.logb_nonneg hb ha
    constructor
    · exact (Real.le_logb_iff_rpow_le hb ha0).mp (Nat.floor_le hl0)
    · have h2 := (Real.logb_lt_iff_lt_rpow hb ha0).mp (Nat.lt_floor_add_one (Real.logb 2 a))
      rwa [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm] at h2
  obtain ⟨w1, w2⟩ := window α hα1
  obtain ⟨w1', w2'⟩ := window α' hα1'
  rw [hlev] at w1 w2
  have heq : α = α' := by
    rcases le_total α' α with hle | hle
    · exact alpha_eq_of_class he1 he2 hd h h' hu hv hle (by linarith)
    · exact (alpha_eq_of_class he1 he2 hd h' h hu.symm hv.symm hle (by linarith)).symm
  -- recover `u` from `α`
  have hs1sq : Real.sqrt e1 ^ 2 = e1 := Real.sq_sqrt (by linarith)
  have hs2sq : Real.sqrt e2 ^ 2 = e2 := Real.sq_sqrt (by linarith)
  have hR : (e1 : ℝ) * (u : ℝ) ^ 2 - d = e2 * (v : ℝ) ^ 2 := by exact_mod_cast h
  have hR' : (e1 : ℝ) * (u' : ℝ) ^ 2 - d = e2 * (v' : ℝ) ^ 2 := by exact_mod_cast h'
  have hab : α * (Real.sqrt e1 * u - Real.sqrt e2 * v) = d := by
    rw [hα]
    have : (Real.sqrt e1 * u + Real.sqrt e2 * v) * (Real.sqrt e1 * u - Real.sqrt e2 * v) =
        Real.sqrt e1 ^ 2 * u ^ 2 - Real.sqrt e2 ^ 2 * v ^ 2 := by ring
    rw [this, hs1sq, hs2sq]; linarith
  have hab' : α' * (Real.sqrt e1 * u' - Real.sqrt e2 * v') = d := by
    rw [hα']
    have : (Real.sqrt e1 * u' + Real.sqrt e2 * v') * (Real.sqrt e1 * u' - Real.sqrt e2 * v') =
        Real.sqrt e1 ^ 2 * u' ^ 2 - Real.sqrt e2 ^ 2 * v' ^ 2 := by ring
    rw [this, hs1sq, hs2sq]; linarith
  have hα0 : α ≠ 0 := by linarith
  have hβ : Real.sqrt e1 * u - Real.sqrt e2 * v = Real.sqrt e1 * u' - Real.sqrt e2 * v' := by
    rw [← heq] at hab'
    exact mul_left_cancel₀ hα0 (hab.trans hab'.symm)
  have hsum : Real.sqrt e1 * u + Real.sqrt e2 * v = Real.sqrt e1 * u' + Real.sqrt e2 * v' := heq
  have h2 : Real.sqrt e1 * (u : ℝ) = Real.sqrt e1 * u' := by linarith
  have hs0 : Real.sqrt e1 ≠ 0 := by linarith
  have : (u : ℝ) = u' := mul_left_cancel₀ hs0 h2
  exact_mod_cast this

open Classical in
/-- **Elementary Pell count.** -/
theorem pell_count_le {X e1 e2 d : ℕ} (he1 : 1 ≤ e1) (he2 : 1 ≤ e2) (hd : 1 ≤ d) :
    ((((Finset.Icc 1 X).filter
        (fun u : ℕ => ∃ v : ℕ, (e1 : ℤ) * (u : ℤ) ^ 2 - d = e2 * (v : ℤ) ^ 2)).card : ℕ) : ℝ) ≤
      (d : ℝ) ^ 2 * (Real.logb 2 (2 * Real.sqrt e1 * X) + 1) := by
  set S := (Finset.Icc 1 X).filter
    (fun u : ℕ => ∃ v : ℕ, (e1 : ℤ) * (u : ℤ) ^ 2 - d = e2 * (v : ℤ) ^ 2) with hS
  rcases Nat.eq_zero_or_pos X with hX0 | hX0
  · have : S = ∅ := by
      rw [hS, hX0]; rfl
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]
    rw [hX0]; simp
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX0
  have he1R : (1 : ℝ) ≤ e1 := by exact_mod_cast he1
  have he2R : (1 : ℝ) ≤ e2 := by exact_mod_cast he2
  have hs1g : 1 ≤ Real.sqrt e1 := Real.one_le_sqrt.mpr he1R
  have hs2g : 1 ≤ Real.sqrt e2 := Real.one_le_sqrt.mpr he2R
  set B : ℝ := 2 * Real.sqrt e1 * X with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  set K := ⌊Real.logb 2 B⌋₊ with hK
  let vOf : ℕ → ℕ := fun u =>
    if hu : ∃ v : ℕ, (e1 : ℤ) * (u : ℤ) ^ 2 - d = e2 * (v : ℤ) ^ 2 then hu.choose else 0
  have hvOf : ∀ u ∈ S, (e1 : ℤ) * (u : ℤ) ^ 2 - d = e2 * (vOf u : ℤ) ^ 2 := by
    intro u hu
    rw [hS, Finset.mem_filter] at hu
    simp only [vOf, dif_pos hu.2]
    exact hu.2.choose_spec
  let g : ℕ → ℕ × ℕ × ℕ := fun u =>
    (u % d, vOf u % d, ⌊Real.logb 2 (Real.sqrt e1 * u + Real.sqrt e2 * (vOf u))⌋₊)
  have hinj : Set.InjOn g (S : Set ℕ) := by
    intro u hu u' hu' hg
    simp only [g, Prod.mk.injEq] at hg
    exact u_eq_of_class he1 he2 hd (hvOf u hu) (hvOf u' hu') hg.1 hg.2.1 hg.2.2
  have himg : S.image g ⊆ Finset.range d ×ˢ Finset.range d ×ˢ Finset.range (K + 1) := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have huS := hu
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨⟨hu1, huX⟩, _⟩ := hu
    have hv := hvOf u huS
    simp only [g, Finset.mem_product, Finset.mem_range]
    refine ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), ?_⟩
    -- the level is at most `K`
    have hR : (e1 : ℝ) * (u : ℝ) ^ 2 - d = e2 * ((vOf u : ℕ) : ℝ) ^ 2 := by exact_mod_cast hv
    have hs1sq : Real.sqrt e1 ^ 2 = e1 := Real.sq_sqrt (by linarith)
    have hs2sq : Real.sqrt e2 ^ 2 = e2 := Real.sq_sqrt (by linarith)
    have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hvu : Real.sqrt e2 * (vOf u : ℝ) ≤ Real.sqrt e1 * u := by
      have h1 : (Real.sqrt e2 * (vOf u : ℝ)) ^ 2 ≤ (Real.sqrt e1 * u) ^ 2 := by
        rw [mul_pow, mul_pow, hs1sq, hs2sq]; linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h1
    have huXR : (u : ℝ) ≤ X := by exact_mod_cast huX
    have hu1R : (1 : ℝ) ≤ u := by exact_mod_cast hu1
    have hαB : Real.sqrt e1 * u + Real.sqrt e2 * (vOf u) ≤ B := by
      rw [hB]; nlinarith
    have hα1 : 1 ≤ Real.sqrt e1 * u + Real.sqrt e2 * (vOf u) := by
      have : (0 : ℝ) ≤ Real.sqrt e2 * (vOf u) := by positivity
      nlinarith
    have hmono : Real.logb 2 (Real.sqrt e1 * u + Real.sqrt e2 * (vOf u)) ≤ Real.logb 2 B :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hαB
    have := Nat.floor_mono hmono
    rw [← hK] at this
    omega
  have hcard : S.card ≤ d * (d * (K + 1)) := by
    rw [← Finset.card_image_of_injOn hinj]
    calc (S.image g).card ≤ (Finset.range d ×ˢ Finset.range d ×ˢ Finset.range (K + 1)).card :=
          Finset.card_le_card himg
      _ = d * (d * (K + 1)) := by simp [Finset.card_product]
  have hKle : (K : ℝ) ≤ Real.logb 2 B :=
    Nat.floor_le (Real.logb_nonneg (by norm_num) hB1)
  calc (S.card : ℝ) ≤ ((d * (d * (K + 1)) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (d : ℝ) ^ 2 * ((K : ℝ) + 1) := by push_cast; ring
    _ ≤ (d : ℝ) ^ 2 * (Real.logb 2 B + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

end Erdos374.D35

end

end
