-- Prove2me | Theorems.Thm_d9_slope_norm_le_of_lipschitz
-- name    : d9_slope_norm_le_of_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:07:32.883663+00:00
-- url     : https://prove2.me/theorems/ccb20a6a-6f4c-436a-9f15-7650e93d01a9
-- title:
--   d9_slope_norm_le_of_lipschitz
-- statement:
--   Automatically extracted helper theorem d9_slope_norm_le_of_lipschitz from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

theorem d9_slope_norm_le_of_lipschitz
    (g : ℝ → ℝ) (K a b : ℝ) (hK : 0 ≤ K)
    (hLip : |g b - g a| ≤ K * |b - a|) :
    ‖slope g a b‖ ≤ K := by sorry
