-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapConnection_connectionLinearMap_bijective
-- name    : ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T11:46:57.570996+00:00
-- url     : https://prove2.me/theorems/711fc0b7-42af-4494-8765-c95a3aa449c6
-- title:
--   The genuine fifteen-coordinate connection map is bijective
-- statement:
--   For every n>=1, the genuine rational linear map from the five P coefficients and ten q coefficients to the fifteen even t coefficients of D_n P(u_n)+H_n(q) is bijective. Reflection recovers the whole polynomial. These even t coordinates are triangularly equivalent to the paper u coordinates; identical matrix entries are not asserted.
-- source:
--   Actual original D/H connection system; frozen source SHA256 098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8.

import Definitions.Def_ZetaNine_CoefficientMapConnection

set_option autoImplicit false
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection

theorem ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (connectionLinearMap n):= by sorry
