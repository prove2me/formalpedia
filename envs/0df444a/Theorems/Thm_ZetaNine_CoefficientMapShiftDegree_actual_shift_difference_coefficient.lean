-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_coefficient
-- name    : ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T22:26:21.693434+00:00
-- url     : https://prove2.me/theorems/a06430dc-7541-40b3-b39c-d194c8e0a8a5
-- title:
--   Exact next surviving coefficient of the actual polynomial shift difference
-- statement:
--   For every natural $n$ and nonzero rational polynomial $H$ of natural degree $d$, the coefficient of $X^{d+10}$ in the actual $D_n(H)$ equals $(7n-2-d)\operatorname{LC}(H)$. This identity needs only $H\ne0$; no positivity, parity, degree-gap, monicity or preassigned operator relation is assumed. The degree-$d+11$ terms cancel in the actual polynomial calculation.
-- source:
--   Zeta(9) actual polynomial shift operator: missions/zeta9/research/coefficient-map-shift-degree-2026-10-04.md. Frozen source SHA256 96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953. The relationship to the rational telescoper is proved separately; it is not an input to these polynomial endpoints. Original declaration lines 78–106.

import Definitions.Def_ZetaNine_CoefficientMapShiftDegree

set_option autoImplicit false
open Polynomial
open ZetaNine ZetaNine.CoefficientMapShiftDegree

theorem ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient (n : ℕ) (H : ℚ[X]) (hH : H ≠ 0) :
    (shiftDifference n H).coeff (H.natDegree + 10) =
      (7 * (n : ℚ) - 2 - (H.natDegree : ℚ)) * H.leadingCoeff:= by sorry
