-- Prove2me | Theorems.Thm_poly_decompose_degree_le
-- name    : poly_decompose_degree_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:17:19.411442+00:00
-- url     : https://prove2.me/theorems/5af4f0cb-7c4a-41bf-a93a-d0d285343217
-- title:
--   poly decompose degree le: poly decompose degree le
-- statement:
--   The degree of each component pᵢ is at most (deg p) / m.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L170-L178
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L170-L178

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]

theorem poly_decompose_degree_le (m : ℕ) (hm : m > 0) (p : Polynomial F) (i : Fin m) :
    (poly_decompose m p i).natDegree ≤ p.natDegree / m := by sorry
