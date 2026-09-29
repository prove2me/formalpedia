-- Prove2me | solution 1 for PGLQuotient.prod_gapRatio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:24:13.753267+00:00
-- url     : https://prove2.me/submissions/3f9ef4a8-5231-4cf6-9700-f8c78c19ea17

-- Sol generated from Algebra/PGLQuotient/HeightThreshold.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_gapAt_coe

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
theorem solution(s : ℝ) (g : Vertex d) :
    ∏ k, gapRatio q d s k ^ g k = (q ^ pairExp g)⁻¹ * (q ^ (s / d)) ^ heightExp g := by
  have hterm : ∀ k : Fin (d - 1), gapRatio q d s k ^ g k
      = (q⁻¹) ^ ((((k : ℕ) + 1) * (d - 1 - (k : ℕ))) * g k)
        * (q ^ (s / d)) ^ ((d - 1 - (k : ℕ)) * g k) := by
    intro k
    unfold gapRatio
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← inv_pow]
  congr 2
  · rw [pairExp, ← Fin.sum_univ_eq_sum_range (fun k => (k + 1) * (d - 1 - k) * gapAt g k)]
    exact Finset.sum_congr rfl (fun k _ => by rw [gapAt_coe, mul_assoc])
  · rw [heightExp, ← Fin.sum_univ_eq_sum_range (fun k => (d - 1 - k) * gapAt g k)]
    exact Finset.sum_congr rfl (fun k _ => by rw [gapAt_coe])
