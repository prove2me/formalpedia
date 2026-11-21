-- Prove2me | solution 1 for Mpfx.quantum_le_of_odd_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:29:42.57261+00:00
-- url     : https://prove2.me/submissions/ae0468f6-108a-42a3-b57b-643d6cd50fe3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_coeff_eq_of_shift


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {e : ℤ} {x : Dyadic}
    (hq : Dyadic.quantumAtLeast (e : QExp) x) {c q : ℤ}
    (hodd : Odd c) (heq : ((x : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) :
    e ≤ q := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ((x : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
    rw [← Dyadic.quantumAtLeast_coe_real]; exact hq
  by_contra hlt; push Not at hlt
  have hc_int := coeff_eq_of_shift (K := ℝ) hlt.le (heq.symm.trans hm)
  have h2dvd : (2 : ℤ) ∣ c := by
    rw [hc_int]; exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) m
  rcases hodd with ⟨t, ht⟩
  omega
end Mpfx
