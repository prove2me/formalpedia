-- Prove2me | Theorems.Thm_Catalog_Geometry_Peel_peel_energy_identity
-- name    : Catalog.Geometry.Peel.peel_energy_identity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:07:23.370364+00:00
-- url     : https://prove2.me/theorems/9eaa1301-d185-4540-bd77-0df8ca545c81
-- title:
--   Energy identity.
-- statement:
--   **Energy identity.**  The excess of the layer energy over `A²/N` is exactly
--   the total squared deviation of the layers from the average.
--
--   ```lean
--   theorem Catalog.Geometry.Peel.peel_energy_identity(hN : 0 < N) :
--       peelEnergy P N - (peelBudget P N) ^ 2 / N
--         = ∑ k ∈ range N, (peelGap P k - peelRate P N) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PeelEnergyVariational.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PeelEnergyVariational.lean#L50

-- Thm stub generated from Geometry/PeelEnergyVariational.lean
import Mathlib
import Definitions.Def_Geometry_PeelDilationBodies
import Definitions.Def_Geometry_PeelEnergyVariational
import Definitions.Def_Geometry_PeelStoppingTime
/-
# Cycle 4: the variational characterisation of extremal peelings

Cycles 1–3 characterise the extremisers of the peeling bound by an
*inequality* (all layers small), by a *symmetry* (invariance of the layer
contents under a transitive action) and by an explicit *geometric family*
(equal-measure dilations of a star-shaped body).  This file adds the fourth,
variational, description and ties it to the previous three.

Write `A = peelBudget P N` for the content removed in a window of `N` steps.
The **layer energy** of the window is `∑_{k<N} gap_k²`.  The exact identity

`∑_{k<N} gap_k² - A²/N = ∑_{k<N} (gap_k - A/N)²`   (`peel_energy_identity`)

immediately gives:

* `peel_energy_ge` — the energy is at least `A²/N` (a Cauchy–Schwarz bound
  obtained here by a square-completion, with no appeal to Cauchy–Schwarz);
* `peel_energy_eq_iff_extremal` — equality holds exactly for the extremisers
  of the stopping-time bound, giving a second, independent proof of the
  rigidity theorem `peel_extremal_tfae`;
* `exists_peel_large_gap` — the dual pigeonhole: every window also contains a
  step whose layer is at least the average, so `min gap ≤ rate ≤ max gap`
  with a double equality precisely in the extremal case.

The geometric corollary `shell_energy_minimal` states that among all ball
peelings of `B(0,R) ⊆ ℝ^d` into `N` shells, the equal-volume shells of
`shellRadius` minimise the sum of squared shell volumes.

## Lab notes

`N = 4`, `A = 1`.  Uniform gaps `(¼,¼,¼,¼)`: energy `4·1/16 = 0.25 = A²/N`.
Front-loaded gaps `(1,0,0,0)`: energy `1`, excess `0.75`, which equals
`∑ (gap - ¼)² = (3/4)² + 3·(1/4)² = 0.5625 + 0.1875 = 0.75` — the identity
checks out numerically, and the excess is exactly the variance of the layer
distribution.
-/

open Catalog.Geometry.Peel

open Finset MeasureTheory

variable (P : PeelProfile) {N : ℕ}

/-! ## The energy identity -/

theorem Catalog.Geometry.Peel.peel_energy_identity(hN : 0 < N) :
    peelEnergy P N - (peelBudget P N) ^ 2 / N
      = ∑ k ∈ range N, (peelGap P k - peelRate P N) ^ 2 := by sorry
