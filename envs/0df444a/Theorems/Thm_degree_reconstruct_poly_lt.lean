-- Prove2me | Theorems.Thm_degree_reconstruct_poly_lt
-- name    : degree_reconstruct_poly_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:05:17.787122+00:00
-- url     : https://prove2.me/theorems/09a066c1-0640-42f6-b652-1e86766ca388
-- title:
--   degree reconstruct poly lt: degree reconstruct poly lt
-- statement:
--   Degree bound for reconstructed polynomial
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L991-L1005
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L991-L1005

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem degree_reconstruct_poly_lt {F : Type*} [Field F] [DecidableEq F] (m : ℕ) (d : ℕ)
    (p : Fin m → Polynomial F) (h : ∀ i, (p i).degree < d / m) :
    (poly_from_components m p).degree < d := by sorry
