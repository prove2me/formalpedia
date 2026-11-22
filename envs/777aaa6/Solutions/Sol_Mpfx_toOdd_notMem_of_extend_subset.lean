-- Prove2me | solution 1 for Mpfx.toOdd_notMem_of_extend_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:21:35.533937+00:00
-- url     : https://prove2.me/submissions/5e2761f9-ba7c-4fb0-b286-e1e6a5502acd

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Theorems.Thm_Mpfx_FiniteFormat_isEven_of_subset
import Theorems.Thm_Mpfx_FiniteFormat_not_isEven_and_isOdd
import Theorems.Thm_Mpfx_Format_self_subset_extend
import Theorems.Thm_Mpfx_Format_shrink_extend_one
import Theorems.Thm_Mpfx_mem_unbounded_of_mem


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z : Dyadic} (hz : RoundsFinite F₂ .toOdd x z)
    (hxne : x ≠ (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  refine FiniteFormat.not_isEven_and_isOdd (FiniteFormat.isEven_of_subset hsub hp_F₂
    (Format.self_subset_extend F₁.toFormat 1 z hzF₁) ?_) (hz.2.2 hxne)
  change z ∈ (F₁.toFormat.extend 1).shrink.unbounded
  rw [Format.shrink_extend_one]
  exact mem_unbounded_of_mem hzF₁
end Mpfx
