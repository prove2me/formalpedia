-- Prove2me | Theorems.Thm_BookSixth_rotation_12_preserves_roundness
-- name    : BookSixth.rotation_12_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T17:09:55.169439+00:00
-- url     : https://prove2.me/theorems/f890bc0d-54b1-4686-a4d6-d785f5ecf93c
-- title:
--   Chapter 15 primitive: rotation in the 1-2 plane preserves round circles
-- statement:
--   Let $C$ be a genuine round circle in $\mathbb{R}^3$. Rotate $\mathbb{R}^3$ in the plane spanned by the second and third coordinate axes, acting as the planar rotation $\begin{pmatrix}\cos\theta & -\sin\theta\\ \sin\theta & \cos\theta\end{pmatrix}$ on coordinates $1$ and $2$ and fixing coordinate $0$. Then the image of $C$ is again a genuine round circle, with centre $R c$, orthonormal frame $R u, R v$ and the same radius. This is the third coordinate-plane rotation; together with the $0$-$1$ and $0$-$2$ rotations it generates every element of $SO(3)$ by the standard three-angle decomposition.
-- source:
--   Elementary interface consequence of the canonical sixth-edition definitions b1fcef2b-61fb-4326-bde6-cb6070d37c77. A coordinate-plane rotation is an orthogonal map, so it transports the three defining orthonormal equations of `RoundCircle` from $\cos^2\theta + \sin^2\theta = 1$. Companion to `BookSixth.rotation_01_preserves_roundness` and `BookSixth.rotation_02_preserves_roundness`; the three together reproduce the `iso_rot01`, `iso_rot02`, `iso_rot12` stages of the accepted `BookSixth.round_circle_single_standardize` proof.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.rotation_12_preserves_roundness (C : Set Space3) (θ : ℝ)
    (hC : RoundCircle C) :
    RoundCircle
      ((fun x : Space3 => ![x 0, Real.cos θ * x 1 - Real.sin θ * x 2,
          Real.sin θ * x 1 + Real.cos θ * x 2]) '' C) := by sorry
