-- Prove2me | Theorems.Thm_case_one_interval
-- name    : case_one_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:21.020341+00:00
-- url     : https://prove2.me/theorems/4f61f4c3-3a34-4b3c-add1-28a9a66a1d67
-- title:
--   case one interval: case one interval
-- statement:
--   **Subcase (1b): interval coloring strategy.**
--       Let s be the smallest multiple of 3 such that g > ⌈m/s⌉. Split Z_m into s
--       intervals of lengths ⌊m/s⌋ and ⌈m/s⌉, colored in a repeating 01/12/20
--       pattern (repeated s/3 times). Since ⌈m/s⌉ < g < 2⌊m/s⌋, any translate of
--       {0,1,g,g+1} where the pairs {0,1} and {g,g+1} lie in different intervals gets
--       all three colors. This is the workhorse subcase, handling most values of g.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L468-L617
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L468-L617

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_interval (s g : ℕ) (hs : 0 < s) (hs3 : 3 ∣ s)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s)) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
