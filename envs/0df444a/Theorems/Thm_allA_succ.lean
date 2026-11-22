-- Prove2me | Theorems.Thm_allA_succ
-- name    : allA_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:46:58.513432+00:00
-- url     : https://prove2.me/theorems/f224b379-ef80-4823-b72d-a47b7614d542
-- title:
--   all A succ: all A succ
-- statement:
--   The all A succ construction uses the all A succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L211-L216
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L211-L216

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

theorem allA_succ (A b c : ℕ) (h : Accept A b c ∨ A.gcd (b.gcd c) ≠ 1) (hA : allA A b c) :
    allA (A + 1) b c := by sorry
