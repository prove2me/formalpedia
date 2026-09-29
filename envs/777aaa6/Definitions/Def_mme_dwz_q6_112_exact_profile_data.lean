-- Prove2me | Definitions.Def_mme_dwz_q6_112_exact_profile_data
-- name    : mme_dwz_q6_112_exact_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T13:43:39.175496+00:00
-- url     : https://prove2.me/theorems/2a6163af-a4a7-4d95-863d-09d5249fee02
-- title:
--   DWZ q=6 enhanced-112 coupled-to-canonical grade translation
-- statement:
--   Records the exact coordinate translation from the enhanced coupled 112 constituent used in the q=6 primary-hash extraction to the canonical CW-square 112 block. Coupled Z grades 0, 1, and 2 correspond respectively to canonical left fine grades 2, 0, and 1. This is data only; the associated exact Table-2 histogram is proved separately.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6(d), Section 6.3, and Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_CW_q6_primary_hash_family

/-- Translate the three Z grades of the enhanced coupled 112 constituent to the left fine grades of the canonical CW-square 112 block. -/
def mme_dwz_q6_coupled_Z_leftGrade : Fin 3 → Fin 3 := ![2, 0, 1]


