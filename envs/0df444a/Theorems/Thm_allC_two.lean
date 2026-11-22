-- Prove2me | Theorems.Thm_allC_two
-- name    : allC_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:38.359178+00:00
-- url     : https://prove2.me/theorems/2dfca1da-7b63-4239-aa05-d8eb510e454e
-- title:
--   all C two: all C two
-- statement:
--   The all C two construction uses the all C two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L178-L178
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L178-L178

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

theorem allC_two : allC (nat_lit 2) := by sorry
