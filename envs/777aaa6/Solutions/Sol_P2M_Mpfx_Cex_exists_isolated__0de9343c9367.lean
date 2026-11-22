-- Prove2me | solution 1 for P2M_Mpfx_Cex_exists_isolated__0de9343c9367
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:49:26.745429+00:00
-- url     : https://prove2.me/submissions/042ce92c-5199-4081-8cf0-937ce8e6a25e

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Theorems.Thm_Mpfx_Cex_Isolated_mono
import Theorems.Thm_Mpfx_Cex_exists_isolated_le

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F G : FiniteFormat) {m : _root_.Mpfx.Dyadic} (hm : (0 : ℝ) < m) :
    ∃ K : ℤ, Isolated F m K ∧ Isolated G m K ∧ (2 : ℝ) ^ K ≤ m := by
  obtain ⟨K₁, h₁, hK₁⟩ := exists_isolated_le F hm
  obtain ⟨K₂, h₂, -⟩ := exists_isolated_le G hm
  exact ⟨min K₁ K₂, h₁.mono (min_le_left _ _), h₂.mono (min_le_right _ _),
    (zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)).trans hK₁⟩
end Mpfx.Cex
