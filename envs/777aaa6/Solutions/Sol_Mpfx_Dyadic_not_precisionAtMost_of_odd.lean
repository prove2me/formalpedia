-- Prove2me | solution 1 for Mpfx.Dyadic.not_precisionAtMost_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:33:40.571177+00:00
-- url     : https://prove2.me/submissions/a9262d2a-7310-43c9-a946-d10025b0b255

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_Dyadic_exists_odd_canonical_of_precisionAtMost
import Theorems.Thm_Mpfx_quantum_le_of_odd_rep
section
namespace Mpfx
namespace IsDyadic
end IsDyadic
namespace Dyadic
end Dyadic
namespace Dyadic
private theorem odd_rep_unique {x : Dyadic} {c q c' q' : ℤ} (hc : Odd c) (hc' : Odd c')
    (h : (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) (h' : (x : ℝ) = (c' : ℝ) * (2 : ℝ) ^ q') :
    c = c' ∧ q = q' := by
  have hq : quantumAtLeast (q : QExp) x := (quantumAtLeast_coe_real q x).mpr ⟨c, h⟩
  have hq' : quantumAtLeast (q' : QExp) x := (quantumAtLeast_coe_real q' x).mpr ⟨c', h'⟩
  obtain rfl : q = q' :=
    le_antisymm (quantum_le_of_odd_rep hq hc' h') (quantum_le_of_odd_rep hq' hc h)
  refine ⟨?_, rfl⟩
  have h2q : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) _
  exact_mod_cast mul_right_cancel₀ (ne_of_gt h2q) (h.symm.trans h')
end Dyadic
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {p : ℕ} {x : Dyadic} {c q : ℤ}
    (hc : Odd c) (h : (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) (hge : (2 : ℤ) ^ p ≤ |c|) :
    ¬ precisionAtMost (p : Prec) x := by
  intro hp
  have hc_ne : c ≠ 0 := by
    have : (0 : ℤ) < 2 ^ p := by positivity
    intro h0; rw [h0, abs_zero] at hge; omega
  have hx_ne : (x : ℝ) ≠ 0 := by
    rw [h]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hc_ne) (ne_of_gt (zpow_pos (by norm_num) _))
  obtain ⟨c', q', h', hc'_odd, hc'_lt⟩ := exists_odd_canonical_of_precisionAtMost hp hx_ne
  obtain ⟨rfl, -⟩ := odd_rep_unique hc hc'_odd h h'
  omega
end Mpfx.Dyadic
