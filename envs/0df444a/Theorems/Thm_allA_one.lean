-- Prove2me | Theorems.Thm_allA_one
-- name    : allA_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:53.945877+00:00
-- url     : https://prove2.me/theorems/99590cea-b5ff-4488-b7c8-7109eb3a92e8
-- title:
--   all A one: all A one
-- statement:
--   The all A one construction uses the all A one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L209-L209
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L209-L209

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

theorem allA_one (b c : ℕ) : allA (nat_lit 1) b c := by sorry
