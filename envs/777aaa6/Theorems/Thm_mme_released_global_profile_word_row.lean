-- Prove2me | Theorems.Thm_mme_released_global_profile_word_row
-- name    : mme_released_global_profile_word_row
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:34:58.068169+00:00
-- url     : https://prove2.me/theorems/a194c228-b760-45e5-8bab-63aecfe16267
-- title:
--   Normalized word masses equal rational atom-row marginals
-- statement:
--   The actual normalized global word mass equals its exact rational finite atom-row marginal, including zero masses. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_word_counts_row_marginal
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_profile_word_row
    (owner : Fin 6) (i : Fin 3) (s : Fin 45) (w : Word) :
    (profile owner).2 i ⟨0, shapeEquiv s⟩ w =
      (((alpha owner s * ((jointRows owner s).map
        (fun a => if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 : ℚ) := by sorry
