-- Prove2me | Theorems.Thm_d9Revenue_update_protection_hasDerivWithinAt_eq_below
-- name    : d9Revenue_update_protection_hasDerivWithinAt_eq_below
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T14:40:19.301039+00:00
-- url     : https://prove2.me/theorems/c05aba7e-6ec0-42f1-b941-f5e9609c0142
-- title:
--   d9Revenue_update_protection_hasDerivWithinAt_eq_below
-- statement:
--   Automatically extracted helper theorem d9Revenue_update_protection_hasDerivWithinAt_eq_below from oversized parent candidate 639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_d9Revenue_update_protection_eq_below
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_update_protection_hasDerivWithinAt_eq_below
    (f p x : ℕ → ℝ) (j k : ℕ) (s : ℝ) (hkj : k ≤ j) :
    HasDerivWithinAt
      (fun u => revenue f (Function.update p j u) x k s)
      0 (Set.Ici (p j)) (p j) := by sorry
