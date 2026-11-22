-- Prove2me | Theorems.Thm_allB_one
-- name    : allB_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:37.142272+00:00
-- url     : https://prove2.me/theorems/b94bce30-e3d6-41d6-a5df-6ef6aaa0b636
-- title:
--   all B one: all B one
-- statement:
--   The all B one construction uses the all B one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L188-L188
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L188-L188

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory
set_option autoImplicit true
open Finset

theorem allB_one (c : ℕ) : allB (nat_lit 1) c := by sorry
