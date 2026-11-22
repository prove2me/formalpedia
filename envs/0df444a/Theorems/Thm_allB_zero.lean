-- Prove2me | Theorems.Thm_allB_zero
-- name    : allB_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:39.927194+00:00
-- url     : https://prove2.me/theorems/8fef4bff-41d8-476b-8aa8-a21b7995a1d9
-- title:
--   all B zero: all B zero
-- statement:
--   The all B zero construction uses the all B zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L187-L187
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L187-L187

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

theorem allB_zero (c : ℕ) : allB (nat_lit 0) c := by sorry
