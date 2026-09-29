-- Prove2me | solution 1 for PGLQuotient.not_summable_weight_height_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:47:48.060975+00:00
-- url     : https://prove2.me/submissions/24dc7068-f2d0-4439-996c-82d034211df0

-- Sol generated from Algebra/PGLQuotient/HeightThreshold.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_heightExp_ray
import Theorems.Thm_PGLQuotient_height_pow
import Theorems.Thm_PGLQuotient_pairExp_ray
import Theorems.Thm_PGLQuotient_rayVertex_injective
import Theorems.Thm_PGLQuotient_vertexWeight_ge
import Theorems.Thm_PGLQuotient_vertexWeight_pos

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
theorem solution(hq : 1 < q) (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) ≤ s) :
    ¬ Summable (fun g : Vertex d => vertexWeight q g * height q g ^ s) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hd0 : (0:ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  intro hsum
  have hcomp : Summable (fun n : ℕ => vertexWeight q (rayVertex d n)
      * height q (rayVertex d n) ^ s) := hsum.comp_injective (rayVertex_injective hd)
  -- every term along the ray is at least `q^{-d^2}`
  have hcq : q ≤ q ^ (s / d) := by
    have h1 : (1:ℝ) ≤ s / d := by rw [le_div_iff₀ hd0]; linarith
    calc q = q ^ (1:ℝ) := (Real.rpow_one q).symm
      _ ≤ q ^ (s / d) := by
          exact Real.rpow_le_rpow_left_iff hq |>.mpr h1
  have hlow : ∀ n : ℕ, (q ^ (d * d))⁻¹
      ≤ vertexWeight q (rayVertex d n) * height q (rayVertex d n) ^ s := by
    intro n
    have hw := vertexWeight_ge (rayVertex d n) hq
    rw [height_pow hq _ s, heightExp_ray hd, pairExp_ray hd] at *
    have hpow : q ^ ((d - 1) * n) ≤ (q ^ (s / d)) ^ ((d - 1) * n) :=
      pow_le_pow_left₀ (le_of_lt hq0) hcq _
    calc (q ^ (d * d))⁻¹
        = (q ^ (d * d))⁻¹ * ((q ^ ((d - 1) * n))⁻¹ * q ^ ((d - 1) * n)) := by
          rw [inv_mul_cancel₀ (ne_of_gt (pow_pos hq0 _)), mul_one]
      _ ≤ (q ^ (d * d))⁻¹ * ((q ^ ((d - 1) * n))⁻¹ * (q ^ (s / d)) ^ ((d - 1) * n)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((q ^ (d * d))⁻¹ * (q ^ ((d - 1) * n))⁻¹) * (q ^ (s / d)) ^ ((d - 1) * n) := by ring
      _ ≤ vertexWeight q (rayVertex d n) * (q ^ (s / d)) ^ ((d - 1) * n) := by
          refine mul_le_mul_of_nonneg_right hw ?_
          positivity
  have htend := hcomp.tendsto_atTop_zero
  have hpos : (0:ℝ) < (q ^ (d * d))⁻¹ := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend ((q ^ (d * d))⁻¹) hpos
  have h1 := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h1
  have h2 := hlow N
  have h3 : |vertexWeight q (rayVertex d N) * height q (rayVertex d N) ^ s|
      = vertexWeight q (rayVertex d N) * height q (rayVertex d N) ^ s := by
    refine abs_of_nonneg (mul_nonneg (le_of_lt (vertexWeight_pos _ hq)) ?_)
    exact le_of_lt (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hq0 _) s)
  rw [h3] at h1
  linarith
