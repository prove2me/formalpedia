-- Prove2me | Theorems.Thm_BookSixth_round_frame_v_unit
-- name    : BookSixth.round_frame_v_unit
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T09:39:01.532687+00:00
-- url     : https://prove2.me/theorems/90c2e37d-f2b1-45d7-89ad-32a9090b37b5
-- title:
--   Chapter 15: the rotated direction v of a round circle lands exactly on the second unit vector
-- statement:
--   Let $u, v \in \mathbb{R}^3$ and $\theta_1, \theta_2, \theta_3 \in \mathbb{R}$ satisfy the three vanishing and three sign conditions of the frame alignment, together with the two conclusions that $u$ is carried to the first unit vector and that the leading coordinate of $v$ is killed. If $\sum_i v_i^2 = 1$, then the surviving coordinate of the rotated $v$ is exactly one:
--   \[ \cos\theta_3 (\sin\theta_1 v_0 + \cos\theta_1 v_1) - \sin\theta_3 (\sin\theta_2 (\cos\theta_1 v_0 - \sin\theta_1 v_1) + \cos\theta_2 v_2) = 1. \]
--
--   The angle lemma that produces $\theta_1, \theta_2, \theta_3$ only guarantees that this residual is nonnegative: it manufactures the angle from a complex argument and so has access to the sign but not to the magnitude. The magnitude is a separate fact, and it is the norm rather than the inner product. Tracking $\|v\|^2 = 1$ along the three rotations shows that the residual and its companion enter the third rotation as an orthonormal pair, so their squares sum to the square of the norm of the rotated $v$ in the last two coordinates. Since the third coordinate has already been killed, that sum is $1$, and each term is therefore $\pm 1$; nonnegativity selects $+1$.
--
--   This closes the frame derivation. The rotated $v$ is then exactly the second unit vector, so a uniform positive rescaling followed by the three rotations lands the round circle on a standard unit circle of the shape $\{(3k + \cos t, \sin t, 0)\}$. Without this step the rotated $v$ is only known to point in the right plane, and the standardising isotopy would not reach its prescribed endpoint.
--
--   Formalization note. The two norm identities along the first two rotations and the identity along the third are each a `linear_combination` with the corresponding $\cos^2 + \sin^2 = 1$ instance, combined with the unit-norm hypothesis and the two vanishing conditions that remove the off-diagonal terms. The squared residual is converted to the residual by factoring the difference of squares, applying `mul_eq_zero`, and using the nonnegativity supplied by the sign condition in the hypothesis.
-- source:
--   The final step (the `hρ3` clause) of the frame derivation in the accepted proof of `BookSixth.round_circle_single_standardize` (theorem id 57b4c109-19d1-44b6-9291-0b9ef979db2c). It is separated from the rest of that derivation because it is the one step that needs the unit-norm hypothesis on `v` rather than merely the vanishing and sign conditions, so it is not a consequence of the angle lemma alone. The published child `BookSixth.round_frame_angles` (theorem id fa692abc-d8ae-4d71-8c08-c3c86c902669) supplies the chain of vanishing, sign and residual conditions that this statement consumes as hypotheses. Together the two children give the complete frame alignment, which `BookSixth.standardizing_time_maps_are_similarities` (theorem id 70d16099-287a-4360-bf09-e01ddf38bc25) needs in order to land the round circle on `standardCircle k`, and whose hypothesis in turn feeds the proved `BookSixth.roundness_of_rigid_similarity_isotopy` (theorem id 7aa580d7-75a7-4bc5-894b-b3c71bbce246) for Chapter 15, Theorem 1.

import Mathlib
import Definitions.Def_BookSixth

theorem BookSixth.round_frame_v_unit :
    ∀ (u v : Fin 3 → ℝ) (θ1 θ2 θ3 : ℝ),
      (∑ i, v i * v i) = 1 →
      (Real.sin θ1 * u 0 + Real.cos θ1 * u 1 = 0 ∧
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
        Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2 = 0) →
      Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2) = 1 := by sorry
