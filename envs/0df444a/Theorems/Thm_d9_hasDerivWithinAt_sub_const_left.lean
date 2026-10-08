-- Prove2me | Theorems.Thm_d9_hasDerivWithinAt_sub_const_left
-- name    : d9_hasDerivWithinAt_sub_const_left
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T08:08:08.644639+00:00
-- url     : https://prove2.me/theorems/7a2379b7-5e13-4748-bc1f-5d14fe412c5f
-- title:
--   d9_hasDerivWithinAt_sub_const_left
-- statement:
--   Automatically extracted helper theorem d9_hasDerivWithinAt_sub_const_left from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

theorem d9_hasDerivWithinAt_sub_const_left
    (g : ℝ → ℝ) (s x d : ℝ)
    (hg : HasDerivWithinAt g d (Set.Iic (s - x)) (s - x)) :
    HasDerivWithinAt (fun t => g (t - x)) d (Set.Iic s) s := by sorry
