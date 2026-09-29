-- Prove2me | solution 1 for PGLQuotient.summable_weight_height_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:32:19.700319+00:00
-- url     : https://prove2.me/submissions/c4a82a98-1615-404f-b7ea-32ff762b0dc5

-- Sol generated from Algebra/PGLQuotient/HeightThreshold.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_gapRatio_lt_one
import Theorems.Thm_PGLQuotient_gapRatio_nonneg
import Theorems.Thm_PGLQuotient_height_pow
import Theorems.Thm_PGLQuotient_prod_gapRatio
import Theorems.Thm_PGLQuotient_summable_pi_geom
import Theorems.Thm_PGLQuotient_vertexWeight_le
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
theorem solution(hq : 1 < q) (hd : 2 ≤ d) {s : ℝ} (hs : s < d) :
    Summable (fun g : Vertex d => vertexWeight q g * height q g ^ s) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  obtain ⟨hsum, -⟩ := summable_pi_geom (gapRatio q d s)
    (gapRatio_nonneg hq s) (gapRatio_lt_one hq hd hs)
  refine Summable.of_nonneg_of_le (fun g => ?_) (fun g => ?_)
    (hsum.mul_left (((1 - q⁻¹) ^ d)⁻¹))
  · exact mul_nonneg (le_of_lt (vertexWeight_pos g hq))
      (le_of_lt (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hq0 _) s))
  · rw [height_pow hq g s, prod_gapRatio s g, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (vertexWeight_le g hq)
      (pow_nonneg (le_of_lt (Real.rpow_pos_of_pos hq0 _)) _)
