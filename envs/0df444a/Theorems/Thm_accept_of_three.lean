-- Prove2me | Theorems.Thm_accept_of_three
-- name    : accept_of_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:49:00.010501+00:00
-- url     : https://prove2.me/theorems/e49b11d7-2acc-4497-ad1b-6842bf9d21b3
-- title:
--   accept of three: accept of three
-- statement:
--   The accept of three construction uses the accept of three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L239-L247
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L239-L247

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

theorem accept_of_three {a b c : ℕ}
    (h : ({0, 1, 2} : Finset (ZMod 3)) ⊆ {0, (a : ZMod 3), (b : ZMod 3), (c : ZMod 3)}) :
    Accept a b c := by sorry
