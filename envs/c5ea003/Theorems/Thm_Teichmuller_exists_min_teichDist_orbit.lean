-- Prove2me | Theorems.Thm_Teichmuller_exists_min_teichDist_orbit
-- name    : Teichmuller.exists_min_teichDist_orbit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:54:24.987532+00:00
-- url     : https://prove2.me/theorems/cfe438ca-15dd-4d48-ba4e-49efdd05acb3
-- title:
--   The Teichmüller distance from `z` to the orbit of `w` is *attained*.
-- statement:
--   The Teichmüller distance from `z` to the orbit of `w` is *attained*.
--
--   ```lean
--   theorem Teichmuller.exists_min_teichDist_orbit(z w : ℍ) :
--       ∃ g₀ : SL(2, ℤ), ∀ g : SL(2, ℤ), teichDist z (g₀ • w) ≤ teichDist z (g • w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Teichmuller/ProperAction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Teichmuller/ProperAction.lean#L226

-- Thm stub generated from Geometry/Teichmuller/ProperAction.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_TorusSpace
/-
# Proper discontinuity of the mapping class group and the moduli metric

`Geometry.Teichmuller.ModuliSpace` defines the moduli pseudometric of the torus as the infimum

    moduliDist τ τ' = ⨅ g : SL(2, ℤ), teichDist τ (g • τ')

over the *infinite* mapping class group, and proves that it is a symmetric, invariant
pseudometric.  Two facts were left open there (conjecture **C4** of `FUTURE_DIRECTIONS.md`):
the infimum is a *minimum*, and its vanishing detects exactly the mapping class group orbit.
Both are consequences of a single geometric statement — the action is **properly
discontinuous** — which is what this file proves.

Main results:

* `Teichmuller.finite_smul_dist_le` : for all `z w : ℍ` and `R : ℝ` the set of mapping classes
  `g` with `dist z (g • w) ≤ R` is *finite*.  This is proper discontinuity in its sharpest
  ("uniformly finite orbit-intersection") form.
* `Teichmuller.finite_stabilizer` : consequently every stabilizer is a finite group, so the two
  orbifold points found in `ModuliSpace.lean` have finite (in fact cyclic of order `2` and `3`)
  local groups.
* `Teichmuller.exists_min_teichDist_orbit`, `Teichmuller.exists_moduliDist_eq` : the infimum
  defining `moduliDist` is attained; `moduliDist` is a *minimum* over the orbit.
* `Teichmuller.moduliDist_eq_zero_iff` : `moduliDist τ τ' = 0 ↔ ∃ g, g • τ' = τ`.  The kernel of
  the pseudometric is exactly the orbit equivalence relation, i.e. `moduliDist` descends to a
  genuine *metric* on the moduli space `ℍ / SL(2, ℤ)`.
* `Teichmuller.moduliDist_pos_of_not_orbit`, `Teichmuller.moduliDist_rho_I_pos'` : distinct
  points of the moduli space are at positive distance; in particular the two orbifold points
  are, re-deriving `ConeSeparation.moduliDist_rho_I_pos` from a soft argument.

-- !-- Lab Notes -- !--
Hypothesizer (C4): the infimum should be attained because the orbit of a point is discrete and
the hyperbolic balls are compact.
Experimenter: compactness is not needed at all.  The two elementary distance estimates
`im_le_im_mul_exp_dist` and `dist_coe_le` bound, for `dist z (g • w) ≤ R`, both
`normSq (c w + d) = w.im / (g • w).im` and `normSq (a w + b) = ‖g • w‖² · normSq (c w + d)`
by explicit constants; `ModularGroup.tendsto_normSq_coprime_pair` then says that only finitely
many integer pairs satisfy such a bound, and a matrix is its two rows.
Analyst: so proper discontinuity of `SL(2, ℤ)` on `ℍ` is *purely arithmetic* — properness of
the quadratic form `|c w + d|²` on `ℤ²` — and the metric input is only the two-sided comparison
of imaginary parts along a bounded hyperbolic displacement.  Note the argument bounds the whole
matrix, not just its bottom row: the top row is controlled because `‖g • w‖` is bounded, which
is exactly where the *lower* bound on `(g • w).im` (equivalently: `z` and `g • w` stay in a
compact part of `ℍ`) enters.
Critic: is `moduliDist_eq_zero_iff` vacuous?  No: the forward direction genuinely needs
attainment — an infimum of positive numbers can be `0` — and the reverse direction is the
already-proved invariance.  The corollary `moduliDist_rho_I_pos'` is checked against the
independently proved `moduliDist_rho_I_pos` of `ConeSeparation.lean`.
-/

open Teichmuller

open Complex UpperHalfPlane Matrix MatrixGroups Filter

/-! ### The two rows of a modular matrix -/





/-! ### Properness of the quadratic form `|c w + d|²` -/


/-! ### Proper discontinuity -/



/-! ### The infimum defining `moduliDist` is a minimum -/

theorem Teichmuller.exists_min_teichDist_orbit(z w : ℍ) :
    ∃ g₀ : SL(2, ℤ), ∀ g : SL(2, ℤ), teichDist z (g₀ • w) ≤ teichDist z (g • w) := by sorry
