-- Prove2me | Theorems.Thm_BookSixth_tait_fox_five
-- name    : BookSixth.tait_fox_five
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:37:31.684142+00:00
-- url     : https://prove2.me/theorems/9de91e75-6365-431b-a2d3-c4695cc4a1e2
-- title:
--   Chapter 15, Theorem 2 proof: Tait Fox 5-colorings
-- statement:
--   For the reduced Fox equations of Tait diagram 18 modulo five, the even-indexed outer labels agree and the odd-indexed labels agree, with the two labels otherwise arbitrary. Thus there are 25 assignments. The statement concerns the explicit equations, not an assumed link invariant.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 2 proof: Tait Fox 5-colorings, p. 104. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.tait_fox_five (a : Fin 6 → ZMod 5) :
    TaitFox a ↔ a 0 = a 2 ∧ a 2 = a 4 ∧ a 1 = a 3 ∧ a 3 = a 5 := by sorry
