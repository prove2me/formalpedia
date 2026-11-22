-- Prove2me | Theorems.Thm_gcd_pos
-- name    : gcd_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:42.963021+00:00
-- url     : https://prove2.me/theorems/6b6ef06f-3440-4296-a940-7860171d010d
-- title:
--   gcd pos: gcd pos
-- statement:
--   The gcd pos construction uses the gcd pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L60-L68
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L60-L68

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset

theorem gcd_pos {ι : Type*} {f : ι → ℤ} {s : Finset ι} (hf : ∃ i ∈ s, f i ≠ 0) : 0 < s.gcd f := by sorry
