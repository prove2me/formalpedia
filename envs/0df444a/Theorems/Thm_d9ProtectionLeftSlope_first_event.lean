-- Prove2me | Theorems.Thm_d9ProtectionLeftSlope_first_event
-- name    : d9ProtectionLeftSlope_first_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:40:29.339082+00:00
-- url     : https://prove2.me/theorems/7af5600f-ace4-482c-af6f-c5aaf9394f0a
-- title:
--   d9ProtectionLeftSlope_first_event
-- statement:
--   Automatically extracted helper theorem d9ProtectionLeftSlope_first_event from oversized parent candidate 639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9LeftSlope
import Definitions.Def_d9ProtectionLeftSlope
open NestedSeatAlloc.IntPolicy

theorem d9ProtectionLeftSlope_first_event
    (f p x : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (s : ℝ) :
    d9ProtectionLeftSlope f p x j (j + 1) s =
      if p j ≤ s ∧ s < p j + x (j + 1) then
        d9LeftSlope f p x j (p j) - f (j + 1)
      else 0 := by sorry
