-- Prove2me | Theorems.Thm_main_case_one
-- name    : main_case_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:50.486615+00:00
-- url     : https://prove2.me/theorems/957bb7a4-34a5-46a4-899d-4d391aebdbc9
-- title:
--   main case one: main case one
-- statement:
--   **Main Case 1 (Single Cycle).** Aggregates all subcases (1a)–(1d).
--       Reduces to {0,1,g,g+1} via `exists_g_of_coprime`, applies WLOG g ≤ m/2,
--       then dispatches via `case_one_dispatch`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L942-L960
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L942-L960

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem main_case_one (a b : ℤ) (hm : m ≥ 289) (hcard : (zmod_set m a b).card = 4)
    (h_gcd : Nat.gcd b.natAbs m = 1 ∨ Nat.gcd (b - a).natAbs m = 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by sorry
