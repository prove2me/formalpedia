-- Prove2me | solution 1 for ProofShape.reflectionFree_finite_depth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:12:35.292847+00:00
-- url     : https://prove2.me/submissions/ecbfff95-83cc-4b7b-ae03-e7ef435ed9a6

-- Sol generated from MachineLearning/OrdinalResearchGovernance.lean
import Mathlib
import Definitions.Def_MachineLearning_OrdinalResearchGovernance
/-
# Ordinal Research Governance: Depth Guarantees via Proof-Theoretic Analysis

This module develops a formal theory of **ordinally certified automated discovery**,
where ordinal-valued depth functionals on research artifacts control non-triviality
and support automated triage of shallow cycles.

## Architecture

We define two complementary depth models:

1. **AetherOutput model**: A finite syntactic object with height, branching, novelty atoms,
   and dependencies. The ordinal depth is `height + branching`, giving a computable
   governance layer.

2. **ProofShape model**: An inductive type of proof constructors (axiom, compose, iterate,
   reflect) with genuinely transfinite ordinal depth via `ω`-exponentiation at reflection.
   This creates a phase transition between finitary and transfinite derivations.

## Main Results

* `depth_above_threshold_nontrivial` — Outputs above threshold ordinal are non-trivial.
* `innovationRank_le_ordinalDepth` — Innovation rank is dominated by ordinal depth.
* `cycleDepth_lt_iff_allBelow` — Cycle depth characterizes element-wise bounds.
* `shallow_cycle_rejected` — Shallow cycles have all outputs below threshold.
* `shallow_but_nontrivial_needs_escalation` — Mixed cycles require escalation.
* `psDepth_reflect_gt_finite` — Reflection strictly dominates finite iteration.
* `proofShape_nontrivial_of_depth_gt_one` — Deep proof shapes certify non-triviality.
* `reflectionFree_finite_depth` — Reflection-free shapes live below ω.
-/


open Ordinal Finset

/-! ## Part I: AetherOutput Model — Finite Syntactic Research Objects -/









/-! ### Theorem 1: Threshold Depth Implies Non-Triviality -/

/-
Shallow outputs have ordinal depth at most 2.
-/

/-
**Theorem 1**: If an output's ordinal depth exceeds the shallow threshold,
    then it is research-nontrivial.
-/

/-
**Theorem 1 (Abstract)**: For any threshold τ, if all trivial outputs
    have depth ≤ τ, then any output with depth > τ is non-trivial.
    This is the abstract form: the threshold separates trivial from non-trivial.
-/

/-! ### Theorem 2: Innovation Bounded by Depth -/

/-
Innovation rank is bounded by ordinal depth when counts are bounded
    by height and branching respectively.
-/

/-! ## Part II: Research Cycles and Governance Policy -/






/-! ### Theorem 3: Cycle Depth Characterization -/

/-
**Theorem 3**: Cycle depth below threshold iff all outputs below threshold.
    Requires the threshold to be positive (since `Finset.sup` of empty set is ⊥ = 0).
-/

/-
Shallow cycles have all outputs below threshold.
-/

/-! ### Theorem 4: Escalation Policy -/

/-
**Theorem 4**: A shallow cycle with a non-trivial output needs escalation.
-/

/-
**Policy Completeness**: Every shallow cycle is either purely trivial or needs escalation.
-/

/-! ## Part III: ProofShape Model — Transfinite Depth Semantics -/


open ProofShape




/-
Composition strictly increases depth (left component).
-/

/-
Composition strictly increases depth (right component).
-/

/-
**Key Theorem**: Reflection of a shape with positive depth produces depth ≥ ω,
    which exceeds any finite ordinal. This is the phase transition.
-/

/-
Reflection of a non-trivial shape has depth ≥ ω.
-/


/-
Reflection-free proof shapes have finite (< ω) depth.
-/

/-
Reflect constructor always produces positive depth.
-/


/-! ## Part IV: Bridge Theorems -/

/-
Bridge theorem: Finset.sup characterization for ordinal depth.
-/

/-
Monotonicity: adding branching increases depth.
-/

/-
Monotonicity: adding height increases depth.
-/

/-! ## Part V: Decidable Governance -/


/-
The boolean decision agrees with the ordinal predicate.
-/

/-! ## Part VI: Depth Strict Monotonicity -/


open ProofShape in
theorem solution:
    ∀ p : ProofShape, ¬ hasReflect p → p.psDepth < omega0 := by
  intro p hp;
  exact Ordinal.lt_omega0.2 ( by
    induction' p using ProofShape.recOn with p hp ih;
    · exact ⟨ 0, rfl ⟩;
    · -- By definition of `hasReflect`, if `¬(p.compose hp✝).hasReflect`, then `¬p.hasReflect` and `¬hp✝.hasReflect`.
      have h_not_reflect : ¬p.hasReflect ∧ ¬‹ProofShape›.hasReflect := by
        exact not_or.mp hp;
      obtain ⟨ n, hn ⟩ := ih h_not_reflect.1; obtain ⟨ m, hm ⟩ := ‹¬_ → ∃ n : ℕ, _› h_not_reflect.2; use Max.max n m + 1; simp +decide [ *, ProofShape.psDepth ] ;
      cases max_choice n m <;> simp +decide [ * ];
      · exact le_of_max_le_left ( by aesop );
      · grind;
    · rename_i n a ih;
      obtain ⟨ k, hk ⟩ := ih ( by cases a <;> tauto );
      exact ⟨ k + n, by erw [ show ( ProofShape.iterate n a ).psDepth = a.psDepth + n from rfl ] ; simp +decide [ hk ] ⟩;
    · exact False.elim <| hp <| by tauto; )
