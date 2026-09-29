-- Prove2me | solution 1 for F1Tightness.meanPos_coarseFn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:50:55.59708+00:00
-- url     : https://prove2.me/submissions/6ce5db5d-150e-4340-b4e8-7247d41cf565

-- Sol generated from Probability/F1TightnessRefinement.lean
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


/-- Splitting a sum over `2M` indices into `M` consecutive pairs. -/
theorem sum_range_two_mul (g : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ range (2 * M), g i = ∑ j ∈ range M, (g (2 * j) + g (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ n ih =>
      have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring







/-! ## A fully explicit instance (non-vacuity of the hypotheses) -/








open F1Tightness in
theorem solution{M : ℕ} (hM : 0 < M) (g : ℕ → ℝ) :
    meanPos (fun j : Fin M => coarseFn g (j : ℕ))
      = meanPos (fun i : Fin (2 * M) => g (i : ℕ))
        + (∑ j ∈ range M, (g (2 * j) - g (2 * j + 1))) / (4 * (M : ℝ)) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hfine :
      meanPos (fun i : Fin (2 * M) => g (i : ℕ))
        = ∑ j ∈ range M,
            (((2 * (j : ℝ) + 1 / 2) / (2 * (M : ℝ))) * g (2 * j)
              + ((2 * (j : ℝ) + 3 / 2) / (2 * (M : ℝ))) * g (2 * j + 1)) := by
    rw [meanPos]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ((((i : ℕ) : ℝ) + 1 / 2) / ((2 * M : ℕ) : ℝ)) * g i) (2 * M)]
    rw [sum_range_two_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hcoarse :
      meanPos (fun j : Fin M => coarseFn g (j : ℕ))
        = ∑ j ∈ range M,
            (((j : ℝ) + 1 / 2) / (M : ℝ)) * (g (2 * j) + g (2 * j + 1)) := by
    rw [meanPos]
    rw [Fin.sum_univ_eq_sum_range
      (fun j => ((((j : ℕ) : ℝ) + 1 / 2) / ((M : ℕ) : ℝ)) * coarseFn g j) M]
    rfl
  rw [hcoarse, hfine, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp
  ring
