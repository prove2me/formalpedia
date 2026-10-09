-- Prove2me | Theorems.Thm_d9Revenue_update_protection_hasDerivWithinAt_eq_below_left
-- name    : d9Revenue_update_protection_hasDerivWithinAt_eq_below_left
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T14:40:31.001832+00:00
-- url     : https://prove2.me/theorems/35d66574-0ffe-44e2-952d-282eef220593
-- title:
--   d9Revenue_update_protection_hasDerivWithinAt_eq_below_left
-- statement:
--   Automatically extracted helper theorem d9Revenue_update_protection_hasDerivWithinAt_eq_below_left from oversized parent candidate 639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_d9Revenue_update_protection_eq_below
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_update_protection_hasDerivWithinAt_eq_below_left
    (f p x : ℕ → ℝ) (j k : ℕ) (s : ℝ) (hkj : k ≤ j) :
    HasDerivWithinAt
      (fun u => revenue f (Function.update p j u) x k s)
      0 (Set.Iic (p j)) (p j) := by sorry
