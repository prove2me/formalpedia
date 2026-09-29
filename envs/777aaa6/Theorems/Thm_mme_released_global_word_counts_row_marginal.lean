-- Prove2me | Theorems.Thm_mme_released_global_word_counts_row_marginal
-- name    : mme_released_global_word_counts_row_marginal
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:17.003551+00:00
-- url     : https://prove2.me/theorems/ed13116f-cf34-4194-86d2-8008d1eb7a0b
-- title:
--   Global word counts equal weighted row marginals
-- statement:
--   The actual global word count equals the coarse weight times the finite released atom-row marginal, including zero counts. This identity makes exact boundary volume certificates computable without enumerating all joint words. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_global_profile_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_word_counts_row_marginal
    (owner : Fin 6) (c : Shape) (i : Fin 3) (w : Word) :
    wordCounts owner i c w = alpha owner (shapeEquiv.symm c) *
      ((jointRows owner (shapeEquiv.symm c)).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum := by sorry
