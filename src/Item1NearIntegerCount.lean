module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max
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


/-! Elementary counting of integer multiples close to integers.
The estimate is Ford's (5.6) with a natural radius, including radius zero.
No rational approximation or polynomial mean-value bound is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators Classical

namespace Item1NearIntegerCount

/-- A finite integer set in a real interval has at most length plus one points. -/
theorem card_le_real_interval_length (s : Finset ℤ) (a b : ℝ) (hab : a ≤ b)
    (hs : ∀ n ∈ s, a ≤ (n:ℝ) ∧ (n:ℝ) ≤ b) :
    (s.card:ℝ) ≤ b-a+1 := by
  by_cases hn : s.Nonempty
  · have hlo := (hs (s.min' hn) (s.min'_mem hn)).1
    have hhi := (hs (s.max' hn) (s.max'_mem hn)).2
    have hle := s.min'_le_max' hn
    have hsub : s ⊆ Finset.Icc (s.min' hn) (s.max' hn) := by
      intro n hn'
      exact Finset.mem_Icc.mpr ⟨s.min'_le n hn', s.le_max' n hn'⟩
    have hc : (s.card:ℝ) ≤ ((Finset.Icc (s.min' hn) (s.max' hn)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hcard : ((Finset.Icc (s.min' hn) (s.max' hn)).card:ℝ) =
        (s.max' hn:ℝ)+1-(s.min' hn:ℝ) := by
      exact_mod_cast Int.card_Icc_of_le (s.min' hn) (s.max' hn)
        (show s.min' hn ≤ s.max' hn + 1 by omega)
    rw [hcard] at hc
    linarith
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

/-- A fixed target integer receives at most 2*delta/gamma+1 multiples. -/
theorem card_mul_close (s : Finset ℤ) (γ δ m : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hs : ∀ d ∈ s, |(d:ℝ)*γ-m| < δ) :
    (s.card:ℝ) ≤ 2*δ/γ+1 := by
  have hh := card_le_real_interval_length s ((m-δ)/γ) ((m+δ)/γ)
    (div_le_div_of_nonneg_right (by linarith) hγ.le) (by
      intro d hd
      have h := abs_lt.mp (hs d hd)
      constructor
      · exact (div_le_iff₀ hγ).mpr (by linarith)
      · exact (le_div_iff₀ hγ).mpr (by linarith))
  convert hh using 1
  ring

/-- The finite set counted by the near-integer estimate. -/
def nearIntegerSet (K : ℕ) (γ δ : ℝ) : Finset ℤ :=
  (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter
    (fun d => |(d:ℝ)*γ-(round ((d:ℝ)*γ):ℝ)| < δ)

/-- For delta below 1/2, group the multiples by their nearest integer. -/
theorem near_integer_count_small (K : ℕ) (γ δ : ℝ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hhalf : δ < 1/2) :
    ((nearIntegerSet K γ δ).card:ℝ) ≤
      4*(K:ℝ)*δ+2*(K:ℝ)*γ+4*δ/γ+2 := by
  let S := nearIntegerSet K γ δ
  let f : ℤ → ℤ := fun d => round ((d:ℝ)*γ)
  have hK : 0 ≤ (K:ℝ) := Nat.cast_nonneg K
  have hbox (d : ℤ) (hd : d ∈ S) : -(K:ℝ) ≤ (d:ℝ) ∧ (d:ℝ) ≤ K := by
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact_mod_cast h
  have hnear (d : ℤ) (hd : d ∈ S) : |(d:ℝ)*γ-(f d:ℝ)| < δ :=
    (Finset.mem_filter.mp hd).2
  have hfiber (m : ℤ) : ((S.filter (fun d => f d = m)).card:ℝ) ≤ 2*δ/γ+1 := by
    apply card_mul_close _ γ δ (m:ℝ) hγ hδ
    intro d hd
    have hh := Finset.mem_filter.mp hd
    simpa only [hh.2] using hnear d hh.1
  have himage : ((S.image f).card:ℝ) ≤ 2*(K:ℝ)*γ+2 := by
    have hh := card_le_real_interval_length (S.image f)
      (-(K:ℝ)*γ-δ) ((K:ℝ)*γ+δ) (by nlinarith) (by
        intro m hm
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
        have hb := hbox d hd
        have hn := abs_lt.mp (hnear d hd)
        have hl := mul_le_mul_of_nonneg_right hb.1 hγ.le
        have hu := mul_le_mul_of_nonneg_right hb.2 hγ.le
        constructor <;> linarith)
    linarith
  have hcard : (S.card:ℝ) =
      ∑ m ∈ S.image f, ((S.filter (fun d => f d = m)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f S
  change (S.card:ℝ) ≤ _
  rw [hcard]
  calc
    _ ≤ ∑ _m ∈ S.image f, (2*δ/γ+1) :=
      Finset.sum_le_sum (fun m _ => hfiber m)
    _ = ((S.image f).card:ℝ)*(2*δ/γ+1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*(K:ℝ)*γ+2)*(2*δ/γ+1) :=
      mul_le_mul_of_nonneg_right himage (by positivity)
    _ = _ := by field_simp; ring

/-- Ford's elementary near-integer count, with no restriction on delta. -/
theorem near_integer_count (K : ℕ) (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) :
    ((nearIntegerSet K γ δ).card:ℝ) ≤
      4*(K:ℝ)*δ+2*(K:ℝ)*γ+4*δ/γ+2 := by
  by_cases hhalf : δ < 1/2
  · exact near_integer_count_small K γ δ hγ hδ hhalf
  · have hδhalf : 1/2 ≤ δ := le_of_not_gt hhalf
    have hK : 0 ≤ (K:ℝ) := Nat.cast_nonneg K
    have hc := card_le_real_interval_length (nearIntegerSet K γ δ)
      (-(K:ℝ)) (K:ℝ) (by linarith) (by
        intro d hd
        have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
        exact_mod_cast h)
    have hkg : 0 ≤ (K:ℝ)*γ := mul_nonneg hK hγ.le
    have hdg : 0 ≤ 4*δ/γ := by positivity
    have hkd : 2*(K:ℝ) ≤ 4*(K:ℝ)*δ := by nlinarith
    linarith

end Item1NearIntegerCount

run_cmd do
  for target in [``Item1NearIntegerCount.card_le_real_interval_length,
      ``Item1NearIntegerCount.card_mul_close,
      ``Item1NearIntegerCount.near_integer_count_small,
      ``Item1NearIntegerCount.near_integer_count] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "NEAR INTEGER COUNT: 4 standard-axiom theorem guards passed."
