-- Prove2me | Theorems.Thm_allC_three
-- name    : allC_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:34.919343+00:00
-- url     : https://prove2.me/theorems/1ae731a9-006e-4ed2-82e7-2878b077f919
-- title:
--   all C three: all C three
-- statement:
--   The all C three construction uses the all C three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L179-L179
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L179-L179

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

theorem allC_three : allC (nat_lit 3) := by sorry
