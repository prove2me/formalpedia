-- Prove2me | Theorems.Thm_mme_dwz_fourth_log_lookup_sound
-- name    : mme_dwz_fourth_log_lookup_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T05:47:33.691226+00:00
-- url     : https://prove2.me/theorems/6e8facf7-6612-4365-ad68-2d96658c0b65
-- title:
--   Pointwise soundness of the fourth-power logarithm scale table
-- statement:
--   Every entry of the published logarithm scale table that can be looked up by index has a positive
--   argument, and its stored automatically scaled bounds bracket the natural logarithm of that
--   argument.
--
--   This turns the table-wide validity certificate into the pointwise form the entropy arithmetic
--   needs when it resolves a single logarithm lookup.
--
--   ```lean
--   ∀ {index : Nat} {entry : Prod Rat Nat} (hlookup : entries[index]? = some entry),
--     0 < entry.1 ∧
--       (MME.autoScaledLogLower entry.1 entry.2 6 : Real) ≤ Real.log (entry.1 : Real) ∧
--         Real.log (entry.1 : Real) ≤ (MME.autoScaledLogUpper entry.1 entry.2 6 : Real)
--   ```
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Theorems.Thm_mme_dwz_fourth_exact_log_scale_table
import Definitions.Def_mme_dwz_fourth_log_scale_table_data

open MME MME.DWZFourthLogScaleTable
open scoped Classical

set_option autoImplicit false

theorem mme_dwz_fourth_log_lookup_sound :
    ∀ {index : Nat} {entry : Prod Rat Nat} (hlookup : entries[index]? = some entry),
    0 < entry.1 /\
      (MME.autoScaledLogLower entry.1 entry.2 6 : Real) <=
          Real.log (entry.1 : Real) /\
        Real.log (entry.1 : Real) <=
          (MME.autoScaledLogUpper entry.1 entry.2 6 : Real) := by sorry
