-- Prove2me | Theorems.Thm_d9_hasDerivWithinAt_sub_const
-- name    : d9_hasDerivWithinAt_sub_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T08:07:31.586641+00:00
-- url     : https://prove2.me/theorems/08067c5a-f948-47e3-93fa-41a1c9ec543b
-- title:
--   d9_hasDerivWithinAt_sub_const
-- statement:
--   Automatically extracted helper theorem d9_hasDerivWithinAt_sub_const from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

theorem d9_hasDerivWithinAt_sub_const
    (g : ℝ → ℝ) (s x d : ℝ)
    (hg : HasDerivWithinAt g d (Set.Ici (s - x)) (s - x)) :
    HasDerivWithinAt (fun t => g (t - x)) d (Set.Ici s) s := by sorry
