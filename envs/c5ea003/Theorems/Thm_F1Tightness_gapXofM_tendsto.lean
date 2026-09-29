-- Prove2me | Theorems.Thm_F1Tightness_gapXofM_tendsto
-- name    : F1Tightness.gapXofM_tendsto
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:26:10.9418+00:00
-- url     : https://prove2.me/theorems/2f027249-2832-4a7b-9a54-eaa2bf0622b5
-- title:
--   The finite-grid slack converges to the continuum slack.
-- statement:
--   The finite-grid slack converges to the continuum slack.
--
--   ```lean
--   theorem F1Tightness.gapXofM_tendsto{E : ℝ} (hE0 : 0 < E) :
--       Tendsto (gapXofM E) atTop (nhds (1 / (2 * E))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessDiscretisation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessDiscretisation.lean#L67

-- Thm stub generated from Probability/F1TightnessDiscretisation.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessDiscretisation

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

open F1Tightness

theorem F1Tightness.gapXofM_tendsto{E : ℝ} (hE0 : 0 < E) :
    Tendsto (gapXofM E) atTop (nhds (1 / (2 * E))) := by sorry
