-- Prove2me | Theorems.Thm_mme_dwz_q6_121_211_component_even_length
-- name    : mme_dwz_q6_121_211_component_even_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:53:46.601853+00:00
-- url     : https://prove2.me/theorems/62f806ea-bb5b-4b7e-975a-b446bee734ed
-- title:
--   The paired 121/211 Table-2 rows have an exact even length
-- statement:
--   The exact integral component count for each of the two paired Table-2 rows 121 and 211 is 2073445800000000. Therefore, at every natural scale m, its powered length is exactly twice 1036722900000000m. This supplies the two equal source halves used in the paired coupled-address construction.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Section 6.3, released Table-2 parameters.

import Mathlib.Tactic
import Definitions.Def_mme_dwz_table2_integer_counts

open MME

set_option autoImplicit false

theorem mme_dwz_q6_121_211_component_even_length
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ) :
    MME.DWZTable2Counts.component s * m =
      2 * (1036722900000000 * m) := by
  sorry
