-- Prove2me | Theorems.Thm_WittenAdSHolography_confDim_isLargerRoot
-- name    : WittenAdSHolography.confDim_isLargerRoot
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:33:43.906298+00:00
-- url     : https://prove2.me/theorems/e96017ea-7170-4879-9d3f-6e3969761e53
-- title:
--   Eqs. (2.43)–(2.44): $\Delta=\frac12(d+\sqrt{d^2+4m^2})$ is the larger root of $\Delta(\Delta-d)=m^2$
-- statement:
--   Let $d\ge0$ and $m^2\in\mathbb R$ with $m^2\ge-d^2/4$ (so the quadratic has real roots). Then
--   $$\Delta=\tfrac12\big(d+\sqrt{d^2+4m^2}\big)$$
--   satisfies $\Delta(\Delta-d)=m^2$, and every real $r$ with $r(r-d)=m^2$ satisfies $r\le\Delta$.
--
--   This is the mass–dimension relation of the AdS/CFT dictionary.
-- source:
--   E. Witten, Anti de Sitter Space and Holography, Adv. Theor. Math. Phys. 2 (1998) 253-291, arXiv:hep-th/9802150v2, https://arxiv.org/abs/hep-th/9802150, p. 21, eqs. (2.43)-(2.44)

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology

theorem WittenAdSHolography.confDim_isLargerRoot (d : ℕ) (msq : ℝ) (hm : -((d : ℝ) ^ 2) / 4 ≤ msq) :
    confDim d msq * (confDim d msq - d) = msq ∧
      ∀ r : ℝ, r * (r - d) = msq → r ≤ confDim d msq := by sorry
