-- Prove2me | Theorems.Thm_quad_coeff_ne_zero
-- name    : quad_coeff_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:46:26.62325+00:00
-- url     : https://prove2.me/theorems/ddb56956-469d-45fa-a012-4d6d1ec006b0
-- title:
--   quad coeff ne zero: quad coeff ne zero
-- statement:
--   Key step in Theorem 3: for a nonsquare n, w₄²/n − w₂² = 0 forces w₂ = w₄ = 0.
--
--   Source: https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean#L36-L48
-- source:
--   https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean#L36-L48

import Mathlib
import Definitions.Def_LisonekSaltConic
set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]

theorem quad_coeff_ne_zero (n w2 w4 : ZMod p) (hn : ¬ IsSquare n)
    (hw : (w2, w4) ≠ (0, 0)) : w4^2 * n⁻¹ - w2^2 ≠ 0 := by sorry
