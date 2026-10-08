-- Prove2me | Theorems.Thm_d9Revenue_update_protection_eq_below
-- name    : d9Revenue_update_protection_eq_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:15.924001+00:00
-- url     : https://prove2.me/theorems/165a44d0-5626-4b11-9e6e-462e2ad782f7
-- title:
--   d9Revenue_update_protection_eq_below
-- statement:
--   Automatically extracted helper theorem d9Revenue_update_protection_eq_below from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_d9Revenue_eq_of_policy_agree_below
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_update_protection_eq_below
    (f p x : ℕ → ℝ) (j k : ℕ) (u s : ℝ) (hkj : k ≤ j) :
    revenue f (Function.update p j u) x k s = revenue f p x k s := by sorry
