-- Prove2me | Theorems.Thm_card_sub_erase_zero_le
-- name    : card_sub_erase_zero_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:36.927954+00:00
-- url     : https://prove2.me/theorems/9c73fc6b-0644-4d23-be31-4cf9fedf35f8
-- title:
--   card sub erase zero le: card sub erase zero le
-- statement:
--   The cardinality of `(S - S) \ {0}` is at most `|S| * (|S| - 1)`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L42-L54
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L42-L54

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open Pointwise

theorem card_sub_erase_zero_le {G : Type*} [DecidableEq G] [AddGroup G] {S : Finset G} :
    #((S - S).erase 0) ≤ #S * (#S - 1) := by sorry
