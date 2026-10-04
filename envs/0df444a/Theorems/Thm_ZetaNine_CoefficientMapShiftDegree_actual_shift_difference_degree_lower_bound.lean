-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_degree_lower_bound
-- name    : ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T22:26:30.605857+00:00
-- url     : https://prove2.me/theorems/e2ff238b-b15f-4892-8a65-1350390813ae
-- title:
--   Actual shift difference degree lower bound in the nonresonant domain
-- statement:
--   Let $n\ge1$ and let nonzero $H\in\mathbb Q[X]$ satisfy $d=\operatorname{natdeg}H\le7n-3$. Then $d+10\le\operatorname{natdeg}D_n(H)$. The exact coefficient is proved nonzero from these original inequalities. No parity or monicity premise is added. The bound matters: $n=1,H=X^5$ lies outside it and has vanishing coefficient of $X^{15}$ although $D_1(X^5)(1)=-1152$.
-- source:
--   Zeta(9) actual polynomial shift operator: missions/zeta9/research/coefficient-map-shift-degree-2026-10-04.md. Frozen source SHA256 96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953. The relationship to the rational telescoper is proved separately; it is not an input to these polynomial endpoints. Original declaration lines 119–122.

import Definitions.Def_ZetaNine_CoefficientMapShiftDegree

set_option autoImplicit false
open Polynomial
open ZetaNine ZetaNine.CoefficientMapShiftDegree

theorem ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hH : H ≠ 0) (hdeg : H.natDegree ≤ 7 * n - 3) :
    H.natDegree + 10 ≤ (shiftDifference n H).natDegree:= by sorry
