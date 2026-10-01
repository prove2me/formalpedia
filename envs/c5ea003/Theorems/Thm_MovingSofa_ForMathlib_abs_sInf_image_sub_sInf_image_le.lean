-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_abs_sInf_image_sub_sInf_image_le
-- name    : MovingSofa.ForMathlib.abs_sInf_image_sub_sInf_image_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:15:59.680534+00:00
-- url     : https://prove2.me/theorems/44a37c89-8a2f-432e-8960-052ab07ebe60
-- title:
--   Uniformly close functions have close infima
-- statement:
--   Uniformly $C$-close real functions on a nonempty set have $C$-close infima. Two one-sided bounds via csInf, then abs_le. Drift repairs: Archimedean instance from `Data.Real.Archimedean`.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Order/Infimum.lean#L8-L11

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
open Set

namespace MovingSofa.ForMathlib

theorem abs_sInf_image_sub_sInf_image_le {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f g : ι → ℝ) (hf : BddBelow (f '' s)) (hg : BddBelow (g '' s)) {C : ℝ} (h : ∀ x ∈ s, |f x - g x| ≤ C) : |sInf (f '' s) - sInf (g '' s)| ≤ C := by sorry

end MovingSofa.ForMathlib
