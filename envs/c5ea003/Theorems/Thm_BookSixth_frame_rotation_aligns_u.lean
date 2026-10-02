-- Prove2me | Theorems.Thm_BookSixth_frame_rotation_aligns_u
-- name    : BookSixth.frame_rotation_aligns_u
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T11:11:18.833639+00:00
-- url     : https://prove2.me/theorems/70e18014-fcf3-44b9-95b7-b3ffd756d187
-- title:
--   Chapter 15: the threefold rotation carries the first frame vector onto the 1-axis
-- statement:
--   Let $u, v : \mathbb{R}^3 \to \mathbb{R}$ be an orthonormal pair, and suppose $\theta_1, \theta_2, \theta_3$ are the frame angles supplied by `BookSixth.round_frame_angles`, so that the first two coordinate-plane rotations annihilate the $01$-part of $u$ and then the remaining part, leaving $\cos\theta_2 (\cos\theta_1 u_0 - \sin\theta_1 u_1) - \sin\theta_2 u_2 = 1$. Then the threefold rotation $A = R_{12}(t\theta_3) R_{02}(t\theta_2) R_{01}(t\theta_1)$, evaluated at $t = 1$, sends $u$ to the first standard basis vector $![1, 0, 0]$. This is the geometric content needed to standardise a round circle: the rotations are chosen precisely so that they send the circle's orthonormal frame onto the standard frame, which is why the standardising isotopy of Theorem 1 of Aigner--Ziegler, *Proofs from THE BOOK*, Sixth Edition (2018), p. 130, lands on a standard circle rather than on an arbitrary orthogonal image of one. Without this, the endpoint of the isotopy is not a standard circle. https://doi.org/10.1007/978-3-662-57265-8_15
-- source:
--   Frame-alignment component of the standardising isotopy for Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The three coordinate-plane rotations are the ones built in the Proved targets `BookSixth.round_frame_angles` and `BookSixth.round_frame_v_unit`; the required endpoint image is the geometric obligation left open by those angle-existence statements, and it is a dependency of the Open target `BookSixth.standardizing_time_maps_are_similarities` (70d16099-287a-4360-bf09-e01ddf38bc25).

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
open scoped BigOperators
open BookSixth

theorem BookSixth.frame_rotation_aligns_u (θ1 θ2 θ3 : ℝ) (u : Fin 3 → ℝ)
    (h1a : Real.sin θ1 * u 0 + Real.cos θ1 * u 1 = 0)
    (h2a : Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2 = 0)
    (hρ2 : Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 = 1) :
    rotTriple 1 θ1 θ2 θ3 u = ![1, 0, 0] := by sorry
