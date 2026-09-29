-- Prove2me | solution 1 for PGLQuotient.rayVertex_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:46:45.432768+00:00
-- url     : https://prove2.me/submissions/950da737-adcb-4437-897c-a9c9d4617434

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
theorem solution(hd : 2 ≤ d) : Function.Injective (rayVertex d) := by
  intro m n hmn
  have h0 : (0 : ℕ) < d - 1 := by omega
  have := congrFun hmn ⟨0, h0⟩
  simpa [rayVertex] using this
