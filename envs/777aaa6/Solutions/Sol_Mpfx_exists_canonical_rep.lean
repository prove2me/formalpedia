-- Prove2me | solution 1 for Mpfx.exists_canonical_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:21.45129+00:00
-- url     : https://prove2.me/submissions/3e3ca620-bae1-4288-b118-c6d514e874c5

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Discrete
import Theorems.Thm_Mpfx_FiniteFormat_abs_lt_of_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_mem_unbounded_of_mem


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec))
    {y : _root_.Mpfx.Dyadic} (hmem : y ∈ F) (hpos : 0 < (y : ℝ)) :
    ∃ c : ℤ, |c| < (2 : ℤ) ^ p ∧
      (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ (F.canonicalExp (y : ℝ)) := by
  obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hmem)
  exact ⟨m, F.abs_lt_of_mul_zpow_canonicalExp hp hpos.ne' hm, hm⟩
end Mpfx
