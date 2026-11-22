-- Prove2me | Theorems.Thm_allA_succ_of_gcd
-- name    : allA_succ_of_gcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:57.29395+00:00
-- url     : https://prove2.me/theorems/106e416a-1bac-4f3d-89a5-b692d2c3b3ef
-- title:
--   all A succ of gcd: all A succ of gcd
-- statement:
--   The all A succ of gcd construction uses the all A succ of gcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L218-L229
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L218-L229

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

theorem allA_succ_of_gcd (A b c g ga gb gc : ℕ) (hga : A.beq (ga.mul g)) (hgb : b.beq (gb.mul g))
    (hg : Nat.ble (nat_lit 2) g)
    (hgc : c.beq (gc.mul g)) (hA : allA A b c) :
    allA A.succ b c := by sorry
