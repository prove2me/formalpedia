-- Prove2me | solution 1 for Mpfx.Format.two_le_p_of_precision_two_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:15.103263+00:00
-- url     : https://prove2.me/submissions/df987217-fec5-41ce-ace1-af431b8ced8e

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mono


set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} {v : Dyadic}
    (hvF : v ∈ F) (hv_not_p1 : ¬ Dyadic.precisionAtMost ((1 : ℕ) : Prec) v) :
    ((2 : ℕ) : Prec) ≤ F.p := by
  by_contra h_p_lt
  push Not at h_p_lt
  have hv_p_F : Dyadic.precisionAtMost F.p v := hvF.1
  cases hpf : F.p using ENat.recTopCoe with
  | top => rw [hpf] at h_p_lt; exact not_top_lt h_p_lt
  | coe n =>
    rw [hpf] at h_p_lt hv_p_F
    have hn : n ≤ 1 := by
      have h2 : n < 2 := ENat.coe_lt_coe.mp h_p_lt
      omega
    exact hv_not_p1 (Dyadic.precisionAtMost_mono (ENat.coe_le_coe.mpr hn) hv_p_F)
end Mpfx.Format
