-- Prove2me | Theorems.Thm_poly_decomposition
-- name    : poly_decomposition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:24:39.281924+00:00
-- url     : https://prove2.me/theorems/d6c3cb87-d936-4a1a-b7ec-dd16c8222120
-- title:
--   poly decomposition: poly decomposition
-- statement:
--   P(X) = sum_j P_j(X^m) X^j
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L224-L248
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L224-L248

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem poly_decomposition {F : Type*} [Semiring F] (P : Polynomial F) (m : ℕ) (hm : m > 0) :
    P = ∑ j : Fin m, (poly_component P m j).comp (Polynomial.X ^ m) * Polynomial.X ^ (j : ℕ) := by sorry
