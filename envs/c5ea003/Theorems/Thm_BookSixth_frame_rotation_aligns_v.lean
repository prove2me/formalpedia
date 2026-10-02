-- Prove2me | Theorems.Thm_BookSixth_frame_rotation_aligns_v
-- name    : BookSixth.frame_rotation_aligns_v
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T11:11:47.276201+00:00
-- url     : https://prove2.me/theorems/d5d81d3a-ebc8-43ad-b9ce-6334e8fd6b9e
-- title:
--   Chapter 15: the threefold rotation carries the second frame vector onto the 2-axis
-- statement:
--   Let $u, v : \mathbb{R}^3 \to \mathbb{R}$ be an orthonormal pair, and let $\theta_1, \theta_2, \theta_3$ be the frame angles from `BookSixth.round_frame_angles`, with $\cos\theta_2 (\cos\theta_1 v_0 - \sin\theta_1 v_1) - \sin\theta_2 v_2 = 0$ and the unit-norm consequence $\cos\theta_3 (\sin\theta_1 v_0 + \cos\theta_1 v_1) - \sin\theta_3 (\sin\theta_2 (\cos\theta_1 v_0 - \sin\theta_1 v_1) + \cos\theta_2 v_2) = 1$. Then the threefold rotation $A = R_{12}(t\theta_3) R_{02}(t\theta_2) R_{01}(t\theta_1)$, at $t = 1$, sends $v$ to the second standard basis vector $![0, 1, 0]$. The third coordinate is forced by squared-norm preservation: the Proved `BookSixth.threefold_rotation_preserves_inner_product`, instantiated with $x = y = v$, gives $\sum_i (Av)_i^2 = 1$, so once the first two coordinates are pinned the third has square zero. Together with the companion statement for $u$ this shows the standardising isotopy lands exactly on a standard circle, as required by Theorem 1 of Aigner--Ziegler, *Proofs from THE BOOK*, Sixth Edition (2018), p. 130. https://doi.org/10.1007/978-3-662-57265-8_15
-- source:
--   Frame-alignment component of the standardising isotopy for Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The three coordinate-plane rotations are the ones built in the Proved targets `BookSixth.round_frame_angles` and `BookSixth.round_frame_v_unit`; the required endpoint image is the geometric obligation left open by those angle-existence statements, and it is a dependency of the Open target `BookSixth.standardizing_time_maps_are_similarities` (70d16099-287a-4360-bf09-e01ddf38bc25).

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
import Theorems.Thm_BookSixth_threefold_rotation_preserves_inner_product
open scoped BigOperators
open BookSixth

theorem BookSixth.frame_rotation_aligns_v (θ1 θ2 θ3 : ℝ) (v : Fin 3 → ℝ) (hv : (∑ i, v i * v i) = 1)
    (hρ3 : Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
        + Real.cos θ2 * v 2) = 1)
    (hd0 : Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
      - Real.sin θ2 * v 2 = 0) :
    rotTriple 1 θ1 θ2 θ3 v = ![0, 1, 0] := by sorry
