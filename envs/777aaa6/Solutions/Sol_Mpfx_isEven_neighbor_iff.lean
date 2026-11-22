-- Prove2me | solution 1 for Mpfx.isEven_neighbor_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:23:59.731735+00:00
-- url     : https://prove2.me/submissions/96d5f044-978d-401e-958f-95c82a8afafc

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Parity
import Theorems.Thm_Mpfx_neighbor_abs_le
import Theorems.Thm_Mpfx_isOdd_neighbor_iff
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} (hp1 : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ}
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x))
    {m : ℤ} (hm : m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ ∨
      m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) :
    F.IsEven (Dyadic.ofIntZpow m (F.canonicalExp x)) ↔ Even m := by
  have hmem : Dyadic.ofIntZpow m (F.canonicalExp x) ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun {e'} he' => F.exp_le_canonicalExp x he')
      (fun {_} hp => neighbor_abs_le x hm hp)
  rw [FiniteFormat.IsEven, isOdd_neighbor_iff hp1 h_lo_ne_s hm, not_not, and_iff_right hmem]
end Mpfx
