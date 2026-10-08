-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapMatrix_actualFMatrix_det_ne_zero
-- name    : ZetaNine.CoefficientMapMatrix.actualFMatrix_det_ne_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T13:44:21.003985+00:00
-- url     : https://prove2.me/theorems/3e15df20-1023-4b72-95ab-1ad07c34b3e5
-- title:
--   The actual monomial-row matrix has nonzero determinant
-- statement:
--   For every even n>=2 the actual monomial-row, formal-output-column F matrix has nonzero rational determinant. Its invertibility is derived from the original aggregate kernel and bijection proofs; no determinant or invertibility premise is assumed.
-- source:
--   Actual frozen native CoefficientMapMatrix source SHA256 a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99

import Definitions.Def_ZetaNine_CoefficientMapMatrix

set_option autoImplicit false
open scoped BigOperators Matrix
open Polynomial ZetaNine ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapKernelBridge

theorem ZetaNine.CoefficientMapMatrix.actualFMatrix_det_ne_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    (actualFMatrix n).det ≠ 0:= by sorry
