-- Prove2me | Theorems.Thm_F1Tightness_meanPos_coarseFn
-- name    : F1Tightness.meanPos_coarseFn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:25:28.214124+00:00
-- url     : https://prove2.me/theorems/19496bb9-5485-44c1-a9b1-4295f4905bf2
-- title:
--   The exact refinement identity for the mean probe position.
-- statement:
--   **The exact refinement identity for the mean probe position.**  Merging the
--   cells pairwise moves the measured mean position by
--   `(∑_{j<M} (g(2j) − g(2j+1)))/(4M)`.
--
--   ```lean
--   theorem F1Tightness.meanPos_coarseFn{M : ℕ} (hM : 0 < M) (g : ℕ → ℝ) :
--       meanPos (fun j : Fin M => coarseFn g (j : ℕ))
--         = meanPos (fun i : Fin (2 * M) => g (i : ℕ))
--           + (∑ j ∈ range M, (g (2 * j) - g (2 * j + 1))) / (4 * (M : ℝ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessRefinement.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessRefinement.lean#L62

-- Thm stub generated from Probability/F1TightnessRefinement.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessRefinement

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

open F1Tightness

open Finset

theorem F1Tightness.meanPos_coarseFn{M : ℕ} (hM : 0 < M) (g : ℕ → ℝ) :
    meanPos (fun j : Fin M => coarseFn g (j : ℕ))
      = meanPos (fun i : Fin (2 * M) => g (i : ℕ))
        + (∑ j ∈ range M, (g (2 * j) - g (2 * j + 1))) / (4 * (M : ℝ)) := by sorry
