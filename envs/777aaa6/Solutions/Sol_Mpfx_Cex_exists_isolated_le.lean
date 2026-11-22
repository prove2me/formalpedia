-- Prove2me | solution 1 for Mpfx.Cex.exists_isolated_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:47:34.133336+00:00
-- url     : https://prove2.me/submissions/4d442a45-2087-49ce-824a-8100d9f7c958

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Theorems.Thm_Mpfx_Cex_Isolated_mono
import Theorems.Thm_Mpfx_Cex_exists_isolated

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F : FiniteFormat) {m : Dyadic} (hm : (0 : ℝ) < m) :
    ∃ K : ℤ, Isolated F m K ∧ (2 : ℝ) ^ K ≤ m := by
  obtain ⟨K, h⟩ := exists_isolated F hm.ne'
  exact ⟨min K (Int.log 2 (m : ℝ)), h.mono (min_le_left _ _),
    (zpow_le_zpow_right₀ (by norm_num) (min_le_right _ _)).trans
      (Int.zpow_log_le_self (b := 2) (by norm_num) hm)⟩
end Mpfx.Cex
