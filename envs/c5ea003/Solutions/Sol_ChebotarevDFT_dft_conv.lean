-- Prove2me | solution 1 for ChebotarevDFT.dft_conv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:56:56.129546+00:00
-- url     : https://prove2.me/submissions/68b1256a-df50-4203-a97a-3d10f160f83b

-- Sol generated from Novelty/ChebotarevCauchyDavenport.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevCauchyDavenport
import Definitions.Def_Novelty_ChebotarevUncertainty
/-
# From Chebotarev to Cauchy–Davenport

A Fourier-analytic proof of the Cauchy–Davenport theorem, obtained from the prime-order
uncertainty principle `ChebotarevDFT.uncertainty` (which in turn rests on Chebotarev's theorem
about the nonsingularity of the square submatrices of the DFT matrix).

The route is: Chebotarev ⟹ uncertainty principle ⟹ Cauchy–Davenport, i.e. an algebraic
statement about cyclotomic fields controls an additive-combinatorial one.  (Mathlib contains a
different, combinatorial proof of Cauchy–Davenport; the point here is the bridge.)
-/

open ChebotarevDFT

open Finset Complex ZMod
open scoped ZMod Pointwise

variable {p : ℕ} [NeZero p]

/-! ## Convolution -/




/-! ## Two counting lemmas -/


/-! ## Cauchy–Davenport -/



open ChebotarevDFT in
theorem solution(f g : ZMod p → ℂ) (k : ZMod p) : 𝓕 (conv f g) k = 𝓕 f k * 𝓕 g k := by
  have h1 : 𝓕 (conv f g) k
      = ∑ y, ∑ z, (ZMod.stdAddChar (-(y * k)) * f y) * (ZMod.stdAddChar (-(z * k)) * g z) := by
    rw [ZMod.dft_apply]
    simp only [conv, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Equiv.sum_comp (Equiv.addRight y)
      (fun x => ZMod.stdAddChar (-(x * k)) * (f y * g (x - y)))]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [show -((z + y) * k) = -(y * k) + -(z * k) by ring, AddChar.map_add_eq_mul]
    ring
  rw [h1, ← Finset.sum_mul_sum, ZMod.dft_apply, ZMod.dft_apply]
  simp [mul_comm]
