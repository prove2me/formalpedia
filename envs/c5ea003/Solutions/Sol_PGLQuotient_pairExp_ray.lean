-- Prove2me | solution 1 for PGLQuotient.pairExp_ray
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:22:24.929376+00:00
-- url     : https://prove2.me/submissions/7c704312-fb67-482a-997b-69dff3333bf7

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









lemma gapAt_ray (hd : 2 ≤ d) (n k : ℕ) :
    gapAt (rayVertex d n) k = if k = 0 then n else 0 := by
  unfold gapAt rayVertex
  by_cases hk : k < d - 1
  · rw [dif_pos hk]
  · rw [dif_neg hk]
    have hk0 : k ≠ 0 := by omega
    simp [hk0]








open PGLQuotient in
theorem solution(hd : 2 ≤ d) (n : ℕ) : pairExp (rayVertex d n) = (d - 1) * n := by
  unfold pairExp
  rw [Finset.sum_eq_single 0]
  · rw [gapAt_ray hd]
    simp
  · intro k _ hk
    rw [gapAt_ray hd]
    simp [hk]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h
