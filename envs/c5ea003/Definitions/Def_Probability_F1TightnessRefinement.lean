-- Prove2me | Definitions.Def_Probability_F1TightnessRefinement
-- name    : Probability_F1TightnessRefinement
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:27.863993+00:00
-- url     : https://prove2.me/theorems/771e20d4-b778-42e1-b456-f3ddf53b0cdb
-- title:
--   Aether Catalog definitions — Probability_F1TightnessRefinement
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.F1TightnessRefinement`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/F1TightnessRefinement.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_F1TightnessCore

/-!
# Grid refinement raises the measured slack (paper 250, profile half)

`Probability.F1TightnessDiscretisation` settled the *scalar* half of the
discretisation question: at a **fixed** mean probe position `E < 1/2` the
grid-dependent slack `X_M(E) = (M+1)/(2ME+1)` increases in `M`.  That statement
holds the profile fixed, which is not what happens when a grid is refined: both
the number of cells *and* the measured mean position change.

This file closes the profile half in the dyadic setting.  A profile is presented
as a function `g : ℕ → ℝ` read on the first `2M` cells; its **coarsening**
merges cells pairwise, `coarseFn g j = g (2j) + g (2j+1)`, giving an `M`-cell
profile with the same total mass.  The two measured mean positions differ by an
explicit non-negative amount on a front-loaded profile, and the resulting
comparison of slack factors is strict:

* `meanPos_coarseFn` — the exact identity
  `E_coarse = E_fine + (∑_{j<M} (g(2j) − g(2j+1)))/(4M)`;
* `meanPos_coarseFn_le` — coarsening moves the mean position *forward* when the
  profile is front-loaded pairwise;
* `gapX_coarseFn_lt` — **the coarse grid strictly underestimates the slack**:
  `X(coarse) < X(fine)` whenever the fine mean position is below `1/2`;
* `refinement_increases_slack` — the packaged statement, phrased for an antitone
  profile.

Together with `finite_grid_underestimates` this says that every reported slack
value computed on a finite grid is a *lower* bound: the booked `X = 1.15302`
computed on 27 cells can be read one-sidedly.
-/

namespace F1Tightness

open Finset

/-- The dyadic coarsening of a cell profile presented as a function on `ℕ`:
cells `2j` and `2j+1` are merged. -/
def coarseFn (g : ℕ → ℝ) (j : ℕ) : ℝ := g (2 * j) + g (2 * j + 1)








/-! ## A fully explicit instance (non-vacuity of the hypotheses) -/

/-- The four-cell front-loaded profile `(2/5, 3/10, 1/5, 1/10)`. -/
noncomputable def demoFn : ℕ → ℝ :=
  fun i => if i = 0 then 2 / 5 else if i = 1 then 3 / 10 else if i = 2 then 1 / 5
    else if i = 3 then 1 / 10 else 0






end F1Tightness


