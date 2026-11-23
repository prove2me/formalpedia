-- Prove2me | Theorems.Thm_reconstruct_func_in_code
-- name    : reconstruct_func_in_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:58:35.011545+00:00
-- url     : https://prove2.me/theorems/f8760a7a-d6a8-4f61-9815-bc5ade01fca6
-- title:
--   reconstruct func in code: reconstruct func in code
-- statement:
--   The reconstruct func in code construction uses the reconstruct func in code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1049-L1062
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1049-L1062

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem reconstruct_func_in_code {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) (d : ℕ)
    (u : Fin m → F → F)
    (hu : ∀ i, (pow_domain D m : Set F).restrict (u i) ∈ reedSolomon (pow_domain D m) (d / m)) :
    (D : Set F).restrict (reconstruct_func m u) ∈ reedSolomon D d := by sorry
