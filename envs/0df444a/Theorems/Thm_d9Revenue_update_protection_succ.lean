-- Prove2me | Theorems.Thm_d9Revenue_update_protection_succ
-- name    : d9Revenue_update_protection_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T14:40:50.614971+00:00
-- url     : https://prove2.me/theorems/c7e3f1c2-bf6f-4b7b-8eba-2cdbb53004f8
-- title:
--   d9Revenue_update_protection_succ
-- statement:
--   Automatically extracted helper theorem d9Revenue_update_protection_succ from oversized parent candidate 639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
import Theorems.Thm_d9Revenue_succ_eq_nextRevenue
import Theorems.Thm_d9Revenue_eq_of_policy_agree_below
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_update_protection_succ
    (f p x : ℕ → ℝ) (j : ℕ) (u s : ℝ) (hj : 1 ≤ j) :
    revenue f (Function.update p j u) x (j + 1) s =
      d9NextRevenue (fun t => revenue f p x j t) u
        (x (j + 1)) (f (j + 1)) s := by sorry
