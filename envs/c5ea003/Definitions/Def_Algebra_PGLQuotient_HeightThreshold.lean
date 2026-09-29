-- Prove2me | Definitions.Def_Algebra_PGLQuotient_HeightThreshold
-- name    : Algebra_PGLQuotient_HeightThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:27:04.074645+00:00
-- url     : https://prove2.me/theorems/d17413bf-293b-4dde-9c53-b302744ad879
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_HeightThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.HeightThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/HeightThreshold.lean by skeleton subtraction
import Mathlib
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

namespace PGLQuotient

open Finset

section PiGeom


end PiGeom

section Threshold

variable {d : ℕ} {q : ℝ}


/-- The base of the geometric series in the `k`-th gap direction, for the `s`-th moment. -/
noncomputable def gapRatio (q : ℝ) (d : ℕ) (s : ℝ) (k : Fin (d - 1)) : ℝ :=
  (q ^ (((k : ℕ) + 1) * (d - 1 - (k : ℕ))))⁻¹ * (q ^ (s / d)) ^ (d - 1 - (k : ℕ))






/-- The cusp ray `λ = (n, 0, …, 0)`. -/
def rayVertex (d : ℕ) (n : ℕ) : Vertex d := fun k => if (k : ℕ) = 0 then n else 0







end Threshold

end PGLQuotient


