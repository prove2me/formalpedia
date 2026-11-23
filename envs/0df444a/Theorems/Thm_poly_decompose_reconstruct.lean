-- Prove2me | Theorems.Thm_poly_decompose_reconstruct
-- name    : poly_decompose_reconstruct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:17:23.017804+00:00
-- url     : https://prove2.me/theorems/7cd46878-fef7-4749-a84c-56460ec51e2f
-- title:
--   poly decompose reconstruct: poly decompose reconstruct
-- statement:
--   The reconstruction: p(X) = Σᵢ (poly_decompose m p i)(X^m) · X^i
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L184-L218
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L184-L218

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]

theorem poly_decompose_reconstruct (m : ℕ) (hm : m > 0) (p : Polynomial F) :
    p = ∑ i : Fin m, (poly_decompose m p i).comp (Polynomial.X ^ m) * Polynomial.X ^ (i : ℕ) := by sorry
