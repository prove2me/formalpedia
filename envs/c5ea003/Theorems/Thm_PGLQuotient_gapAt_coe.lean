-- Prove2me | Theorems.Thm_PGLQuotient_gapAt_coe
-- name    : PGLQuotient.gapAt_coe
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:45:56.224979+00:00
-- url     : https://prove2.me/theorems/68462ee0-3f25-44b6-9a05-97bae0776ad3
-- title:
--   GapAt coe
-- statement:
--   Formal statement of `PGLQuotient.gapAt_coe` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PGLQuotient.gapAt_coe(g : Vertex d) (k : Fin (d - 1)) : gapAt g (k : ℕ) = g k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/HeightThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/HeightThreshold.lean#L72

-- Thm stub generated from Algebra/PGLQuotient/HeightThreshold.lean
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

theorem PGLQuotient.gapAt_coe(g : Vertex d) (k : Fin (d - 1)) : gapAt g (k : ℕ) = g k := by sorry
