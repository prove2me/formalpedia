-- Prove2me | Theorems.Thm_finite_contraction_fixedPoint_unique
-- name    : finite_contraction_fixedPoint_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T14:22:59.730701+00:00
-- url     : https://prove2.me/theorems/b6a0251b-4eba-4cfe-903a-3015179663a4
-- title:
--   Finite contraction fixedPoint unique
-- statement:
--   Formal statement of `finite_contraction_fixedPoint_unique` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem finite_contraction_fixedPoint_unique  {X : Type*} [MetricSpace X] [Fintype X] [Nonempty X]
--     (f : X → X) {K : ℝ}
--     (hK : K < 1)
--     (hcontr : ∀ x y : X, dist (f x) (f y) ≤ K * dist x y) :
--     ∃! x : X, f x = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/FiniteContraction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/FiniteContraction.lean#L26

-- Thm stub generated from Geometry/FiniteContraction.lean
import Mathlib

/-!
# A non-circular finite Banach fixed point theorem

A contraction on a nonempty finite metric space has a unique fixed point.

The proof is self-contained: it uses only finite minimization, basic metric-space
facts (`dist_eq_zero`, `dist_comm`), and ordered-ring arithmetic. It does **not**
rely on compactness, completeness, Cauchy sequences, Schauder/Brouwer, or any
existing fixed point theorem.
-/

theorem finite_contraction_fixedPoint_unique  {X : Type*} [MetricSpace X] [Fintype X] [Nonempty X]
  (f : X → X) {K : ℝ}
  (hK : K < 1)
  (hcontr : ∀ x y : X, dist (f x) (f y) ≤ K * dist x y) :
  ∃! x : X, f x = x := by sorry
