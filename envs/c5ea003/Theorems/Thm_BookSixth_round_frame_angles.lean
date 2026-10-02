-- Prove2me | Theorems.Thm_BookSixth_round_frame_angles
-- name    : BookSixth.round_frame_angles
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T09:28:05.660628+00:00
-- url     : https://prove2.me/theorems/fa692abc-d8ae-4d71-8c08-c3c86c902669
-- title:
--   Chapter 15: three angles aligning a round circle's orthonormal frame with the coordinate axes
-- statement:
--   Given an orthonormal pair of directions $u, v \in \mathbb{R}^3$ — the two directions that span a round circle — there exist three real angles $\theta_1, \theta_2, \theta_3$ that align that frame with the coordinate axes.
--
--   The first two angles carry $u$ onto the first unit vector. Writing
--   $a = \cos\theta_1 u_0 - \sin\theta_1 u_1$ for the surviving coordinate of $u$, the condition $\sin\theta_1 u_0 + \cos\theta_1 u_1 = 0$ with $\cos\theta_1 u_0 - \sin\theta_1 u_1 \ge 0$ fixes the first angle up to the sign of the square root, and the same two-step construction applied to $(a, u_2)$ fixes $\theta_2$, giving
--   \[ \cos\theta_2 (\cos\theta_1 u_0 - \sin\theta_1 u_1) - \sin\theta_2 u_2 = 1. \]
--   The third angle is chosen in the same way for $v$. Finally, the orthogonality $\sum_i u_i v_i = 0$ propagates along the chain of rotations and forces
--   \[ \cos\theta_2 (\cos\theta_1 v_0 - \sin\theta_1 v_1) - \sin\theta_2 v_2 = 0, \]
--   so that the leading coordinate of the rotated $v$ vanishes.
--
--   This is the geometric content of standardising a single round circle: three coordinate-plane rotations take the circle's own orthonormal frame to the standard frame, so a uniform rescaling followed by those rotations lands the circle exactly on a separated standard unit circle. It is the step that upgrades the pointwise standardisation of one round circle to the claim that every time map of the standardising isotopy is a similarity, and thereby gives roundness at every time. This supplies the roundness-at-every-time form of Chapter 15, Theorem 1 of Aigner and Ziegler, *Proofs from THE BOOK*, Sixth Edition (2018), p. 130.
--
--   Formalization note. The hypotheses are the three coordinate identities $\sum_i u_i^2 = 1$, $\sum_i v_i^2 = 1$, $\sum_i u_i v_i = 0$, which are exactly the orthonormality conditions occurring in the definition of a round circle. The existential is discharged by applying, three times, the angle lemma of the proved theorem `BookSixth.pointwise_isotopy_wrappers`, which supplies both the vanishing identity and the nonnegativity identity that selects the correct sign. The two residual equalities are recovered by tracking the squared norm and the inner product along the chain: each norm identity and each inner-product identity is a `linear_combination` with the corresponding $\cos^2 + \sin^2 = 1$ instance, and a squared residual is turned into the residual itself by factoring the difference of squares and using the nonnegativity supplied by the angle lemma.
-- source:
--   The frame derivation of the accepted proof of `BookSixth.round_circle_single_standardize` (theorem id 57b4c109-19d1-44b6-9291-0b9ef979db2c), restated as a self-contained statement about an orthonormal pair. The three angles come from the angle lemma of the proved theorem `BookSixth.pointwise_isotopy_wrappers` (theorem id 33c10d39-2e98-4515-8d9e-44a91198f0a7): theta_1 kills the first two coordinates of u, theta_2 kills what is left of u in the second plane, and theta_3 kills what is left of v. Each angle lemma supplies both a vanishing identity and a nonnegativity identity, the latter selecting the correct sign of the square root. The two equalities at the end follow by tracking the squared norm and the inner product along the chain of rotations. The norm identities p1, p2, p3 and the inner-product identities q1, q2 are each discharged by `linear_combination` with the corresponding `Real.cos_sq_add_sin_sq`; h2 and h3 are then recovered from their squares by `rcases mul_eq_zero.1` together with the nonnegativity supplied by the angle lemma, and the vanishing leading coordinate is the linear combination of the two inner-product identities with the original orthogonality hypothesis. Needed as an importable dependency of `BookSixth.standardizing_time_maps_are_similarities` (theorem id 70d16099-287a-4360-bf09-e01ddf38bc25), whose hypothesis in turn is needed by the proved theorem `BookSixth.roundness_of_rigid_similarity_isotopy` (theorem id 7aa580d7-75a7-4bc5-894b-b3c71bbce246) for Chapter 15, Theorem 1.

import Mathlib
import Definitions.Def_BookSixth

theorem BookSixth.round_frame_angles :
    ∀ (u v : Fin 3 → ℝ),
      (∑ i, u i * u i) = 1 → (∑ i, v i * v i) = 1 → (∑ i, u i * v i) = 0 →
      ∃ θ1 θ2 θ3 : ℝ,
        Real.sin θ1 * u 0 + Real.cos θ1 * u 1 = 0 ∧
        0 ≤ Real.cos θ1 * u 0 - Real.sin θ1 * u 1 ∧
        Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2 = 0 ∧
        0 ≤ Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 ∧
        Real.sin θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) +
            Real.cos θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
              + Real.cos θ2 * v 2) = 0 ∧
        0 ≤ Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) -
            Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
              + Real.cos θ2 * v 2) ∧
        Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 = 1 ∧
        Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2 = 0 := by sorry
