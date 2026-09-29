-- Prove2me | Definitions.Def_Probability_F1TightnessDiscretisation
-- name    : Probability_F1TightnessDiscretisation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:47.554229+00:00
-- url     : https://prove2.me/theorems/f9681f26-19e5-4343-83bc-dccd0f9e07d0
-- title:
--   Aether Catalog definitions — Probability_F1TightnessDiscretisation
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.F1TightnessDiscretisation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/F1TightnessDiscretisation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_F1TightnessCore

/-!
# Discretisation bias of the slack factor (paper 250, next-cycle item)

The measured slack factor is computed on a finite cell grid (27 cells), while
the profile it summarises is a continuum density.  The exact identity
`gapX p = (M+1)/(2·M·E_x + 1)` of `Probability.F1TightnessCore` isolates the
grid dependence in a single scalar function, and this file settles its
behaviour: at a fixed mean probe position `E < 1/2` the finite-grid slack is
**strictly below** the continuum value `1/(2E)`, increases with the number of
cells, and converges to it.  Consequently a finite-grid estimate of the F1
slack is conservative.

Main results.

* `gapXofM` — the grid-dependent slack `X_M(E) = (M+1)/(2ME+1)`.
* `gapX_eq_gapXofM` — it is the slack of any profile with mean position `E`.
* `gapXofM_lt_continuum` — `X_M(E) < 1/(2E)` for every `M`, when `E < 1/2`.
* `gapXofM_strictMono` — `X_M(E)` strictly increases in the number of cells.
* `gapXofM_tendsto` — `X_M(E) → 1/(2E)`.
* `finite_grid_underestimates` — the packaged statement: the reported slack is
  a strict lower bound for the continuum slack of the same profile.
-/

open Filter

namespace F1Tightness

/-- The slack factor of an `M`-cell grid at mean probe position `E`. -/
noncomputable def gapXofM (E : ℝ) (M : ℕ) : ℝ := ((M : ℝ) + 1) / (2 * (M : ℝ) * E + 1)







end F1Tightness


