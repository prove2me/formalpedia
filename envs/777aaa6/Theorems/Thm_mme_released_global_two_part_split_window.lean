-- Prove2me | Theorems.Thm_mme_released_global_two_part_split_window
-- name    : mme_released_global_two_part_split_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T20:30:27.125093+00:00
-- url     : https://prove2.me/theorems/3d1878b8-2962-4d1b-a7af-7d9d333ef441
-- title:
--   Two-part split: boundary part plus hashed part gives the released joint window
-- statement:
--   Split the blocks of the released global candidate into two parts: the boundary part, holding every
--   block whose cell has a zero grade in some physical mode, and the hashed part, holding all the others.
--
--   This says that the two parts together put the whole word in the released joint window: if the
--   boundary part carries exactly the prescribed grades and exactly the released per-cell histograms
--   (`QZero`), and the hashed part carries the prescribed grades with per-cell frequencies within `eps`
--   of the released profile (`QPos`), then the assembled word satisfies the window condition of every
--   orientation.
--
--   The point of the split is that the boundary part admits an exact dimension count, while only the
--   hashed part needs the approximate, entropy-carrying treatment.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_global_two_part_split_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_two_part_split_window (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ) (heps : ∀ o, 0 ≤ eps o) (i : Fin 3)
    (x : FineWord (4 * (6 * blocks k)))
    (h0 : QZero k a i (fun r ↦ x (partPositions k a ⟨0, r⟩)))
    (h1 : QPos k a eps i (fun r ↦ x (partPositions k a ⟨1, r⟩))) :
    jointWindow k hk a eps i x := by sorry
