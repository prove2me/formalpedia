-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_Supplement_iterated_accounting
-- name    : WitnessIsolation.AffineCollapse.Supplement.iterated_accounting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:54:47.872266+00:00
-- url     : https://prove2.me/theorems/443ac774-3910-4caf-ab8c-d4190dce51cf
-- title:
--   Lemma 7.1 — Iterated accounting
-- statement:
--   Let $I$ be a pruning transformation with witness-length guarantee $p$, and let $A\ge1$, $B\ge2$ be the exponents of Corollary 6.1 (recurrence (6.2): $S(s,v)\le(s+2)^A(1+S((s+2)^B,t))$ for $v$ above a threshold, $2\le t\le v$ with $p(tv)\ge(2+\zeta)/(t+1)$, and $s\ge v$). There is a constant $K$ such that the following holds. Fix $\zeta>0$ and a threshold $N$ for Corollary 6.1. Let $v=v_0>v_1>\dots>v_h$ be integers, $v_h\ge1$, such that for each $i<h$, $v_i\ge N$, $v_{i+1}\ge2$ and (6.1) holds with $v=v_i$ and $t=v_{i+1}$, i.e. $p(v_{i+1}v_i)\ge(2+\zeta)/(v_{i+1}+1)$. Then for all $s\ge v$,
--   $$S(s,v)\le (s+2)^{K B^h}\,2^{v_h}.\tag{7.1}$$
--   The constant $K$ is independent of $h$ and of the sequence (and also of $p$, $\zeta$ and $N$).
--
--   This is the bookkeeping that lets the recurrence be iterated along schedules whose length grows with $v$, as in Theorems 1.5 and 7.3.
--
--   **Formalization Note** The existence of $A,B$ and of thresholds is the predicate `RecurrenceExponents`; a threshold is `IsRecurrenceThreshold`. $S$ is the published `satComplexity` in $\mathbb N\cup\{\infty\}$, compared with a natural number.
--
--   Differences from the source:
--   - encoding: v_i exceeds the threshold of Corollary 6.1 → v_i ≥ N for every N that is a threshold of Corollary 6.1 for the exponents A, B (IsRecurrenceThreshold), with A, B given as recurrence exponents; reason: Corollary 6.1 asserts existence of A, B and of a threshold; the lemma is stated for any such threshold
--   - encoding: integers v₀ > ⋯ > v_h, with the standing 1 ≤ v and Corollary 6.1’s 2 ≤ t → a natural-number sequence with v_{i+1} < v_i, 2 ≤ v_{i+1} for i < h, and 1 ≤ v_h; reason: these are the ranges in which Corollary 6.1 and (2.2) are stated
--   - generalization: O(B^h) with a constant independent of h and the sequence, for fixed ζ → K·B^h with one natural K chosen before p, ζ, the threshold, h, the sequence and s; reason: the proof uses only A, B and the constants of (2.2), so K does not depend on ζ or p; for fixed ζ this is the source claim
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 13, PDF p. 14, Lemma 7.1 and its proof

import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_bounds

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- Lemma 7.1 (Iterated accounting), printed p. 13 / PDF p. 14. `A,B` are recurrence
exponents of Corollary 6.1 for `I`; the constant `K` of `O(B^h)` precedes `p`, `ζ`, the
threshold, the depth `h`, the schedule `v₀ > ⋯ > v_h` and `s`. Each step `i < h` has `v_i`
above a threshold of Corollary 6.1 and (6.1) with `v = v_i`, `t = v_{i+1}`. -/
theorem iterated_accounting (I : PruningFamily) (hI : IsPruner I) :
    ∃ A B K : ℕ, RecurrenceExponents I A B ∧ 1 ≤ K ∧
      ∀ p : ℕ → ℝ, HasGuarantee I p → ∀ ζ : ℝ, 0 < ζ →
      ∀ N : ℕ, IsRecurrenceThreshold A B p ζ N →
        ∀ h : ℕ, ∀ v : ℕ → ℕ, 1 ≤ v h →
          (∀ i : ℕ, i < h → N ≤ v i ∧ 2 ≤ v (i+1) ∧ v (i+1) < v i ∧
            (2+ζ)/((v (i+1):ℝ)+1) ≤ p (v (i+1) * v i)) →
          ∀ s : ℕ, v 0 ≤ s →
            satComplexity s (v 0) ≤ ((s+2)^(K*B^h) * 2^(v h) : ℕ) := by sorry

end WitnessIsolation.AffineCollapse.Supplement
