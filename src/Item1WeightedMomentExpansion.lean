module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.BigOperators
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
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.DSimpPercent
public import Mathlib.Tactic.InferParam
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


/-! Exact finite weighted even-moment expansion and a correlation bound.
The weights have norm at most one; the phase values need no norm hypothesis.
All statements include exponent zero and empty finite index sets. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Item1WeightedMomentExpansion

theorem norm_even_pow_complex (v : ℂ) (s : ℕ) :
    ((‖v‖ ^ (2 * s) : ℝ) : ℂ) = v ^ s * conj (v ^ s) := by
  simp only [Complex.mul_conj', norm_pow, Complex.ofReal_pow, ← pow_mul,
    Nat.mul_comm s 2]

/-- The weighted power expansion keeps every ordered tuple. -/
theorem weighted_sum_pow {κ η : Type*} [Fintype κ] (s : ℕ)
    (ε : κ → ℂ) (z : κ → η → ℂ) (c : η) :
    (∑ b, ε b * z b c) ^ s =
      ∑ p : Fin s → κ, (∏ l, ε (p l)) * (∏ l, z (p l) c) := by
  classical
  rw [Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]

/-- Exact expansion with the tuple weights outside each coefficient sum. -/
theorem weighted_moment_expansion {κ η : Type*} [Fintype κ]
    (D : Finset η) (s : ℕ) (ε : κ → ℂ) (z : κ → η → ℂ) :
    ((∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s) : ℝ) : ℂ) =
      ∑ p : Fin s → κ, ∑ q : Fin s → κ,
        ((∏ l, ε (p l)) * conj (∏ l, ε (q l))) *
          (∑ c ∈ D, (∏ l, z (p l) c) * conj (∏ l, z (q l) c)) := by
  classical
  simp only [Complex.ofReal_sum, norm_even_pow_complex, weighted_sum_pow,
    map_sum, map_mul, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem tuple_weight_norm_le {κ : Type*} (s : ℕ) (ε : κ → ℂ)
    (hε : ∀ b, ‖ε b‖ ≤ 1) (p : Fin s → κ) :
    ‖∏ l, ε (p l)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun l _ => norm_nonneg (ε (p l))) (fun l _ => hε (p l))

/-- Triangle inequality removes bounded tuple weights after exact expansion.
No norm, injectivity, or positivity hypothesis is imposed on the phase values. -/
theorem weighted_moment_le_correlations {κ η : Type*} [Fintype κ]
    (D : Finset η) (s : ℕ) (ε : κ → ℂ) (z : κ → η → ℂ)
    (hε : ∀ b, ‖ε b‖ ≤ 1) :
    (∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s)) ≤
      ∑ p : Fin s → κ, ∑ q : Fin s → κ,
        ‖∑ c ∈ D, (∏ l, z (p l) c) * conj (∏ l, z (q l) c)‖ := by
  classical
  let E (p : Fin s → κ) : ℂ := ∏ l, ε (p l)
  let C (p q : Fin s → κ) : ℂ :=
    ∑ c ∈ D, (∏ l, z (p l) c) * conj (∏ l, z (q l) c)
  have hE (p : Fin s → κ) : ‖E p‖ ≤ 1 := tuple_weight_norm_le s ε hε p
  have hEE (p q : Fin s → κ) : ‖E p * conj (E q)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (hE p) (hE q) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hnonneg : 0 ≤ ∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s) :=
    Finset.sum_nonneg (fun c _ => pow_nonneg (norm_nonneg _) _)
  calc
    (∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s)) =
        ‖((∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∑ p : Fin s → κ, ∑ q : Fin s → κ, (E p * conj (E q)) * C p q‖ :=
      congrArg norm (weighted_moment_expansion D s ε z)
    _ ≤ ∑ p : Fin s → κ, ‖∑ q : Fin s → κ, (E p * conj (E q)) * C p q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p : Fin s → κ, ∑ q : Fin s → κ, ‖C p q‖ := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        ‖∑ q : Fin s → κ, (E p * conj (E q)) * C p q‖ ≤
            ∑ q : Fin s → κ, ‖(E p * conj (E q)) * C p q‖ := norm_sum_le _ _
        _ ≤ ∑ q : Fin s → κ, ‖C p q‖ := by
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hEE p q) (norm_nonneg _)).trans_eq (one_mul _)

end Item1WeightedMomentExpansion

run_cmd do
  for target in [``Item1WeightedMomentExpansion.norm_even_pow_complex,
      ``Item1WeightedMomentExpansion.weighted_sum_pow,
      ``Item1WeightedMomentExpansion.weighted_moment_expansion,
      ``Item1WeightedMomentExpansion.tuple_weight_norm_le,
      ``Item1WeightedMomentExpansion.weighted_moment_le_correlations] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "WEIGHTED MOMENT EXPANSION: 5 standard-axiom theorem guards passed."
