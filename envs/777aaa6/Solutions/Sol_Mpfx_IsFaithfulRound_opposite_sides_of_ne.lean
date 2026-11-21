-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.opposite_sides_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:55:34.128734+00:00
-- url     : https://prove2.me/submissions/1e812623-7eb6-458d-a7b1-e1ad5de5afdb

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_isFaithfulRound_iff_directed
import Theorems.Thm_Mpfx_RoundsFinite_unique_toNegative
import Theorems.Thm_Mpfx_RoundsFinite_unique_toPositive

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {x : ℝ}
    {a b : Dyadic} (ha : IsFaithfulRound F x a) (hb : IsFaithfulRound F x b)
    (hab : a ≠ b) :
    (RoundsFinite F .toNegative x a ∧ RoundsFinite F .toPositive x b) ∨
    (RoundsFinite F .toNegative x b ∧ RoundsFinite F .toPositive x a) := by
  rcases isFaithfulRound_iff_directed.mp ha with hda | hua <;>
    rcases isFaithfulRound_iff_directed.mp hb with hdb | hub
  · exact absurd (RoundsFinite.unique_toNegative hda hdb) hab
  · exact Or.inl ⟨hda, hub⟩
  · exact Or.inr ⟨hdb, hua⟩
  · exact absurd (RoundsFinite.unique_toPositive hua hub) hab
end IsFaithfulRound
end Mpfx
