-- Prove2me | Theorems.Thm_BookSixth_rotation_02_preserves_roundness
-- name    : BookSixth.rotation_02_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T17:09:50.455003+00:00
-- url     : https://prove2.me/theorems/4478bed1-0d6e-4012-9891-30b067f6f731
-- title:
--   Chapter 15 primitive: rotation in the 0-2 plane preserves round circles
-- statement:
--   Let $C$ be a genuine round circle in $\mathbb{R}^3$. Rotate $\mathbb{R}^3$ in the plane spanned by the first and third coordinate axes, acting as the planar rotation $\begin{pmatrix}\cos\theta & -\sin\theta\\ \sin\theta & \cos\theta\end{pmatrix}$ on coordinates $0$ and $2$ and fixing coordinate $1$. Then the image of $C$ is again a genuine round circle, with centre $R c$, orthonormal frame $R u, R v$ and the same radius. This is the second of the three coordinate-plane rotations needed to align an arbitrary orthonormal frame with the standard one.
-- source:
--   Elementary interface consequence of the canonical sixth-edition definitions b1fcef2b-61fb-4326-bde6-cb6070d37c77. A coordinate-plane rotation is an orthogonal map, so it transports the three defining orthonormal equations of `RoundCircle` from $\cos^2\theta + \sin^2\theta = 1$. Companion to `BookSixth.rotation_01_preserves_roundness`; together with it this supplies the two rotations used by the accepted `BookSixth.round_circle_single_standardize` proof.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.rotation_02_preserves_roundness (C : Set Space3) (θ : ℝ)
    (hC : RoundCircle C) :
    RoundCircle
      ((fun x : Space3 => ![Real.cos θ * x 0 - Real.sin θ * x 2, x 1,
          Real.sin θ * x 0 + Real.cos θ * x 2]) '' C) := by sorry
