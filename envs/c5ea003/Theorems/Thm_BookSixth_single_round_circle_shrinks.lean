-- Prove2me | Theorems.Thm_BookSixth_single_round_circle_shrinks
-- name    : BookSixth.single_round_circle_shrinks
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T02:06:28.340884+00:00
-- url     : https://prove2.me/theorems/a9f69c09-e1b0-4777-b3e9-f6fe0816a533
-- title:
--   Chapter 15: one round circle is shrunk by a global similarity
-- statement:
--   Let $C$ be a round circle in $\mathbb{R}^3$, with centre $c$. For each $t$ in the subtype $\{t : \mathbb{R} \mid 0 \le t \wedge t < 1\}$, i.e. the half-open interval $[0,1)$, there is a homeomorphism $K_t$ of $\mathbb{R}^3$, given by the global similarity $K_t(x) = (1-t)\,x + t\,c$, such that $K_0$ is the identity and $K_t(C)$ is again a round circle. So a single round circle can be shrunk continuously, and stays round throughout. This is the $n=0$ base case of the motion obligations in `BookSixth.perfect_circles_pairwise_unlinked_motion`. The parameter range is the half-open interval $[0,1)$: the scale $1-t$ vanishes at $t=1$, where the map collapses to the constant $c$, which is fatal not merely to being a homeomorphism but to the joint continuity of the inverse. No clearance hypothesis is needed, because the motion is a global similarity of all of $\mathbb{R}^3$: it maps the whole configuration to a scaled copy, so disjointness and unlinking are preserved automatically. This child establishes the motion only; the parent's endpoint obligation, reaching the fixed `standardCircle i`, is not addressed here and remains open.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; the single-circle shrinking motion, using the accepted global-similarity roundness lemma.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness
open scoped BigOperators
open BookSixth

theorem BookSixth.single_round_circle_shrinks (C : Set Space3) (hC : RoundCircle C) :
    ∃ K : {t : ℝ // 0 ≤ t ∧ t < 1} → Space3 ≃ₜ Space3,
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => K p.1 p.2) ∧
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K ⟨0, le_rfl, by norm_num⟩ x = x) ∧
      (∀ t : {t : ℝ // 0 ≤ t ∧ t < 1}, RoundCircle ((K t) '' C)) := by sorry
