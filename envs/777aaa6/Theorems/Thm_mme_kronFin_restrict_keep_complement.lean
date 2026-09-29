-- Prove2me | Theorems.Thm_mme_kronFin_restrict_keep_complement
-- name    : mme_kronFin_restrict_keep_complement
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:51:39.560254+00:00
-- url     : https://prove2.me/theorems/5b2359b4-1d69-4a23-9e41-1b6766c8a658
-- title:
--   Selected tensor restrictions retain complementary factors
-- statement:
--   A finite product of selected restrictions factors into the extracted product and every unselected original tensor. Unselected extracted entries are scalar units, so no complementary factor is discarded. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_kronFin_mono_restrict
import Theorems.Thm_mme_toQ_kronFin
open MME MME.TensorObj BigOperators
universe u

theorem mme_kronFin_restrict_keep_complement
    {K : Type u} [Field K] {d n : ℕ}
    (selected : Fin n → Prop) [DecidablePred selected]
    (P T : Fin n → TensorObj K d)
    (hselected : ∀ j, selected j → Restrict (P j) (T j))
    (hunit : ∀ j, ¬ selected j → Isomorphic (P j) oneObj) :
    Restrict
      (kron (kronFin n P)
        (kronFin n (fun j => if selected j then oneObj else T j)))
      (kronFin n T) := by sorry
