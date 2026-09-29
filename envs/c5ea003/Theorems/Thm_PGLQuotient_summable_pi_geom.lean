-- Prove2me | Theorems.Thm_PGLQuotient_summable_pi_geom
-- name    : PGLQuotient.summable_pi_geom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:45:31.163631+00:00
-- url     : https://prove2.me/theorems/fbea80c4-09fe-4106-ad8f-9fdfe4b501ad
-- title:
--   A product of independent geometric series over the lattice `Fin m → ℕ`.
-- statement:
--   A product of independent geometric series over the lattice `Fin m → ℕ`.
--
--   ```lean
--   theorem PGLQuotient.summable_pi_geom: ∀ {m : ℕ} (x : Fin m → ℝ), (∀ k, 0 ≤ x k) → (∀ k, x k < 1) →
--       Summable (fun h : Fin m → ℕ => ∏ k, x k ^ h k) ∧
--         ∑' h : Fin m → ℕ, ∏ k, x k ^ h k = ∏ k, (1 - x k)⁻¹ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/HeightThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/HeightThreshold.lean#L25

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

theorem PGLQuotient.summable_pi_geom: ∀ {m : ℕ} (x : Fin m → ℝ), (∀ k, 0 ≤ x k) → (∀ k, x k < 1) →
    Summable (fun h : Fin m → ℕ => ∏ k, x k ^ h k) ∧
      ∑' h : Fin m → ℕ, ∏ k, x k ^ h k = ∏ k, (1 - x k)⁻¹ := by sorry
