-- Prove2me | solution 1 for PGLQuotient.height_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:22:26.46413+00:00
-- url     : https://prove2.me/submissions/1e46998f-8556-4539-a038-34a8dd890324

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
theorem solution(hq : 1 < q) (g : Vertex d) (s : ℝ) :
    height q g ^ s = (q ^ (s / d)) ^ heightExp g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  unfold height
  rw [← Real.rpow_natCast (q ^ (s / d)) (heightExp g), ← Real.rpow_mul hq0.le,
    ← Real.rpow_mul hq0.le]
  congr 1
  ring
