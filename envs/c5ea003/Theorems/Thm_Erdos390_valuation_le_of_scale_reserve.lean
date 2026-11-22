-- Prove2me | Theorems.Thm_Erdos390_valuation_le_of_scale_reserve
-- name    : Erdos390.valuation_le_of_scale_reserve
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-06T05:51:12.174731+00:00
-- url     : https://prove2.me/theorems/d9b42006-28a7-4c50-bf41-ec5162810733
-- title:
--   Theorem 10.3 — Valuation comparison via scale reserve bounds
-- statement:
--   **Theorem 10.3 (Valuation Comparison via Scale Reserve Bounds)**
--
--   Let $v_D, v_P \in \mathbb{N}$ and $c_{\mathrm{anchor}}, c_{\mathrm{tail}}, \mathrm{scale} \in \mathbb{R}$.
--   Suppose:
--   1. $\mathrm{scale} \ge 0$,
--   2. $v_D \le c_{\mathrm{anchor}} \cdot \mathrm{scale}$,
--   3. $c_{\mathrm{tail}} \cdot \mathrm{scale} \le v_P$,
--   4. $c_{\mathrm{anchor}} \le c_{\mathrm{tail}}$.
--
--   Then $v_D \le v_P$.
--
--   This directly transfers asymptotic density reserve inequalities into literal $p$-adic valuation dominances for all bounded prime factors in Erdős Problem 390.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdős Problem 390, Section 10, CentralAnchorReserveAlgebra.lean (GitHub 61325b1)

import Mathlib

namespace Erdos390

/-- Given non-negative scale `scale ≥ 0`, upper bound `vD ≤ cAnchor * scale`, lower bound
`cTail * scale ≤ vP`, and coefficient order `cAnchor ≤ cTail`, we have `vD ≤ vP`. -/
theorem valuation_le_of_scale_reserve
    {vD vP : ℕ} {cAnchor cTail scale : ℝ}
    (hscale : 0 ≤ scale)
    (hD : (vD : ℝ) ≤ cAnchor * scale)
    (hP : cTail * scale ≤ (vP : ℝ))
    (hcoeff : cAnchor ≤ cTail) :
    vD ≤ vP := by sorry

end Erdos390
