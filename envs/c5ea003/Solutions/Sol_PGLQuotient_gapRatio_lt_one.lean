-- Prove2me | solution 1 for PGLQuotient.gapRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:22:25.494255+00:00
-- url     : https://prove2.me/submissions/8de2eba8-c201-40b4-a7fb-6d885b15aa23

-- Sol generated from Algebra/PGLQuotient/HeightThreshold.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel

/-!
# Integrability threshold for the lattice-minima height

Let `α` be the homothety-invariant normalised lattice-minima height on the standard
arithmetic quotient of the Bruhat–Tits building of `PGL_d(F_q((t^{-1})))`, modelled as in
`Algebra.PGLQuotient.VertexModel`.

The main theorem of this file is the *exact integrability threshold*

`Summable (fun g => vertexWeight q g * α g ^ s) ↔ s < d`,

i.e. `α ∈ L^r` precisely for `r < d` (in particular for `0 < r < d`).  The positive direction
is proved by factoring the majorant into a product of `d-1` independent geometric series over
the gap coordinates; the negative direction uses the cusp ray `λ = (n,0,…,0)`, along which the
mass decays exactly like `α^{-d}`.
-/

open PGLQuotient

open Finset





variable {d : ℕ} {q : ℝ}

















open PGLQuotient in
theorem solution(hq : 1 < q) (hd : 2 ≤ d) {s : ℝ} (hs : s < d) (k : Fin (d - 1)) :
    gapRatio q d s k < 1 := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hd0 : (0:ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hcq : q ^ (s / d) < q := by
    have h1 : s / d < 1 := by rw [div_lt_one hd0]; exact hs
    calc q ^ (s / d) < q ^ (1:ℝ) := by
          exact (Real.rpow_lt_rpow_left_iff hq).mpr h1
      _ = q := Real.rpow_one q
  have hcpos : (0:ℝ) < q ^ (s / d) := Real.rpow_pos_of_pos hq0 _
  set m : ℕ := d - 1 - (k : ℕ) with hm
  have hm1 : 1 ≤ m := by have := k.isLt; omega
  have h1 : (q ^ (s / d)) ^ m < q ^ m :=
    pow_lt_pow_left₀ hcq (le_of_lt hcpos) (by omega)
  have h2 : q ^ m ≤ q ^ (((k : ℕ) + 1) * m) :=
    pow_le_pow_right₀ hq.le (by nlinarith [Nat.le_mul_of_pos_left m (Nat.succ_pos (k : ℕ))])
  unfold gapRatio
  rw [← hm, inv_mul_lt_one₀ (pow_pos hq0 _)]
  calc (q ^ (s / d)) ^ m < q ^ m := h1
    _ ≤ q ^ (((k : ℕ) + 1) * m) := h2
