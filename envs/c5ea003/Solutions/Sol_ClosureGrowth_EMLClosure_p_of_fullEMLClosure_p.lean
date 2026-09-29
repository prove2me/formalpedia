-- Prove2me | solution 1 for ClosureGrowth.EMLClosure_p_of_fullEMLClosure_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:34:23.079982+00:00
-- url     : https://prove2.me/submissions/730a2523-7b05-47f9-9754-53ccc111f36d

-- Sol generated from Bridges/EntropyClosureSeparation.lean
import Mathlib
import Definitions.Def_Bridges_EntropyClosureSeparation

/-!
# Entropy-Rate Separation via Closure Growth Dynamics

This file formalizes the mathematical core of **closure-growth separation**: the principle
that two monotone set transformers (modeling proof-search policies) can be distinguished
by a finite witness whenever their iterated closures diverge at any stage.

## Main results

### Abstract closure iteration theory
- `closureIter`: iteration of a set transformer via `Nat.iterate`
- `closureIter_zero`, `closureIter_succ_apply`: standard recursion lemmas
- `closureIter_mono`: monotonicity propagates through iteration
- `closureIter_stabilizes`: idempotent closure operators stabilize in one step

### Witness extraction
- `finite_witness_of_stage_separation`: any stage where `F^[n] S ⊈ G^[n] S` yields
  a concrete element witnessing the separation
- `finite_witness_of_eventual_growth_gap`: eventual strict inclusion implies a
  finite separating witness

### Fixed-point invariance
- `closure_fixed_points_are_iterative_invariants`: fixed points of a closure operator
  are invariant under all iterates

### EML instantiation
- `fullEMLClosure'_extensive`: seed sets embed into their full EML closure
- `fullEMLClosure'_setMono`: full EML closure is monotone in the seed set
- `fullEMLClosure'_isClosureOp`: full EML closure is a closure operator
- `fullEMLClosure'_iter_stabilizes`: iterates of full EML closure stabilize

## Motivation

In neural proof mining, a **proof policy** induces a set transformer on the space of
proof states: given a set of reachable states, the policy expands it by one step of
search. The **closure filtration** `F^[0] S ⊆ F^[1] S ⊆ ⋯` captures the cumulative
reach of the policy from seed set `S`.

Two policies `F` and `G` are **separable** if their filtrations diverge: some state is
reachable by `F` but not by `G` (or vice versa) within finitely many steps. The
**finite witness theorem** (`finite_witness_of_stage_separation`) extracts a concrete
certificate of this divergence — the exact mathematical object needed for
counterexample-guided training and benchmark generation.

The split between **preclosure** dynamics (monotone + extensive, where growth happens)
and **closure** saturation (idempotent, where growth halts) is the formal kernel of
"thermodynamic proof complexity": entropy lives in the transient filtration, while
semantic invariants live in the idempotent hull.
-/

open Set Function

noncomputable section

open ClosureGrowth

/-! ## Definitions: Set Monotonicity, Closure, and Preclosure -/





/-! ## Iterated Closure -/




/-! ## Monotonicity of Iterates -/


/-! ## Extensivity of Iterates -/




/-! ## Stabilization for Closure Operators -/


/-! ## Stagewise Reachability and Witness Extraction -/



/-! ## Eventual Growth Gap and Separation -/



/-! ## Fixed-Point Invariance -/




/-! ## EML Closure Infrastructure

We reproduce the core EML definitions here for self-containedness, then
connect them to the abstract closure theory. The EML (Exponential-Minus-Log)
operation generates a closure on `Set ℝ` modeling compositional proof-state
transformations.
-/






/-- `EMLClosure'` is monotone in depth. -/
theorem EMLClosure'_depth_mono (S : Set ℝ) (n : ℕ) :
    EMLClosure' n S ⊆ EMLClosure' (n + 1) S :=
  fun _ hx => Or.inl hx

/-- Depth monotonicity: if `m ≤ n` then `EMLClosure' m S ⊆ EMLClosure' n S`. -/
theorem EMLClosure'_depth_le {S : Set ℝ} {m n : ℕ} (h : m ≤ n) :
    EMLClosure' m S ⊆ EMLClosure' n S := by
  induction h with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans (EMLClosure'_depth_mono S _)




/-
Key lemma: elements of `EMLClosure' n (fullEMLClosure' S)` are in `fullEMLClosure' S`.
    This is the core of the idempotence proof.
-/







open ClosureGrowth in
theorem solution(S : Set ℝ) (n : ℕ) :
    EMLClosure' n (fullEMLClosure' S) ⊆ fullEMLClosure' S := by
  induction' n with n ih;
  · exact fun ⦃a⦄ a_1 => a_1;
  · simp_all +decide [ EMLClosure', Set.subset_def ];
    rintro x ( hx | ⟨ a, ha, b, hb, rfl ⟩ ) <;> [ exact ih x hx; exact Set.mem_iUnion.mpr ?_ ];
    obtain ⟨ m₁, hm₁ ⟩ := Set.mem_iUnion.mp ( ih a ha );
    obtain ⟨ m₂, hm₂ ⟩ := Set.mem_iUnion.mp ( ih b hb );
    -- Let $M = \max(m₁, m₂)$. Then $a$ and $b$ are in $EMLClosure' M S$.
    set M := max m₁ m₂ with hM
    have hM₁ : a ∈ EMLClosure' M S := by
      exact EMLClosure'_depth_le ( le_max_left _ _ ) hm₁
    have hM₂ : b ∈ EMLClosure' M S := by
      exact EMLClosure'_depth_le ( le_max_right m₁ m₂ ) hm₂;
    exact Set.mem_iUnion.mpr ⟨ M + 1, by exact Set.mem_union_right _ ⟨ a, hM₁, b, hM₂, rfl ⟩ ⟩
