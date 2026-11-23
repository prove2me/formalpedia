-- Prove2me | Theorems.Thm_folded_poly_degree_le
-- name    : folded_poly_degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:18:00.426156+00:00
-- url     : https://prove2.me/theorems/b9510dae-865c-4d47-9e3c-5a385c972be8
-- title:
--   folded poly degree le: folded poly degree le
-- statement:
--   The degree of the folded polynomial is at most (deg p) / m.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L246-L249
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L246-L249

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]

theorem folded_poly_degree_le (m : ℕ) (hm : m > 0) (p : Polynomial F) (alpha : F) :
    (folded_poly m p alpha).natDegree ≤ p.natDegree / m := by sorry
