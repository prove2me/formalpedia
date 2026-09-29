-- Prove2me | solution 1 for PGLQuotient.gapAt_coe
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:22:27.005447+00:00
-- url     : https://prove2.me/submissions/c6d07bf4-2e17-460c-887c-18ffa612dce8

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
theorem solution(g : Vertex d) (k : Fin (d - 1)) : gapAt g (k : ℕ) = g k := by
  simp [gapAt, k.isLt]
