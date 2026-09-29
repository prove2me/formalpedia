-- Prove2me | Theorems.Thm_rudelson_selection_eq21_self_bounding_bridge
-- name    : rudelson_selection_eq21_self_bounding_bridge
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-23T23:38:39.200262+00:00
-- url     : https://prove2.me/theorems/7c0ebe26-6438-4477-a5e9-92308a80c729
-- statement:
--   Self-bounding bridge from Rudelson 1999 (J. Funct. Anal. 164), proof of Theorem 1, equation (2.1). If $0\le D$, $0\le A$ and $D\le A\sqrt{D+1}$, then $D\le A + A\sqrt{D}$. The key inequality is $\sqrt{D+1}\le 1+\sqrt{D}$ (square both nonnegative sides). This is exactly the $D\le A(D+1)^{1/2}\le A+A\sqrt D$ step on p.4 of Rudelson's proof.
-- source:
--   Rudelson, Random vectors in the isotropic position, J. Funct. Anal. 164 (1999) 60-72, proof of Theorem 1, eq (2.1), p.4.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

theorem rudelson_selection_eq21_self_bounding_bridge
    (D A : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hrec : D ≤ A * Real.sqrt (D + 1)) :
    D ≤ A + A * Real.sqrt D := by sorry
