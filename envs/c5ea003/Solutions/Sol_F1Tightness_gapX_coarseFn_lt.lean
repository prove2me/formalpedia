-- Prove2me | solution 1 for F1Tightness.gapX_coarseFn_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:54:11.639823+00:00
-- url     : https://prove2.me/submissions/f96ea95d-eb34-42af-970f-331411012baf

-- Sol generated from Probability/F1TightnessRefinement.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessRefinement
import Theorems.Thm_F1Tightness_gapX_eq_meanPos
import Theorems.Thm_F1Tightness_meanPos_coarseFn

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

/-- Coarsening preserves the total mass. -/
theorem sum_coarseFn (g : ℕ → ℝ) (M : ℕ) :
    ∑ j : Fin M, coarseFn g (j : ℕ) = ∑ i : Fin (2 * M), g (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => coarseFn g j) M,
    Fin.sum_univ_eq_sum_range (fun i => g i) (2 * M), sum_range_two_mul]
  rfl

/-- Coarsening preserves non-negativity. -/
theorem coarseFn_nonneg {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) (j : ℕ) : 0 ≤ coarseFn g j :=
  add_nonneg (hg _) (hg _)





/-! ## A fully explicit instance (non-vacuity of the hypotheses) -/








open F1Tightness in
theorem solution{M : ℕ} (hM : 0 < M) {g : ℕ → ℝ}
    (hg : ∀ i, 0 ≤ g i) (hsum : ∑ i : Fin (2 * M), g (i : ℕ) = 1)
    (hfront : ∀ j, j < M → g (2 * j + 1) ≤ g (2 * j))
    (hE : meanPos (fun i : Fin (2 * M) => g (i : ℕ)) < 1 / 2) :
    gapX (fun j : Fin M => coarseFn g (j : ℕ)) < gapX (fun i : Fin (2 * M) => g (i : ℕ)) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set E : ℝ := meanPos (fun i : Fin (2 * M) => g (i : ℕ)) with hEdef
  set D : ℝ := ∑ j ∈ range M, (g (2 * j) - g (2 * j + 1)) with hDdef
  have hD : 0 ≤ D :=
    Finset.sum_nonneg fun j hj => by
      have := hfront j (Finset.mem_range.mp hj); linarith
  have hE0 : 0 ≤ E := by
    rw [hEdef, meanPos]
    refine Finset.sum_nonneg fun i _ => ?_
    have : (0 : ℝ) ≤ ((((i : ℕ) : ℝ) + 1 / 2) / ((2 * M : ℕ) : ℝ)) := by positivity
    exact mul_nonneg this (hg _)
  -- the fine grid
  have hfine : gapX (fun i : Fin (2 * M) => g (i : ℕ))
      = (2 * (M : ℝ) + 1) / (4 * (M : ℝ) * E + 1) := by
    have h2M : 0 < 2 * M := by omega
    rw [gapX_eq_meanPos h2M (fun i => hg _) hsum]
    push_cast
    rw [← hEdef]
    ring_nf
  -- the coarse grid
  have hcsum : ∑ j : Fin M, coarseFn g (j : ℕ) = 1 := by rw [sum_coarseFn]; exact hsum
  have hcoarse : gapX (fun j : Fin M => coarseFn g (j : ℕ))
      = ((M : ℝ) + 1) / (2 * (M : ℝ) * E + D / 2 + 1) := by
    rw [gapX_eq_meanPos hM (fun j => coarseFn_nonneg hg _) hcsum, meanPos_coarseFn hM g,
      ← hEdef, ← hDdef]
    congr 1
    field_simp
    ring
  rw [hfine, hcoarse]
  have hden1 : 0 < 2 * (M : ℝ) * E + D / 2 + 1 := by positivity
  have hden2 : 0 < 4 * (M : ℝ) * E + 1 := by positivity
  rw [div_lt_div_iff₀ hden1 hden2]
  nlinarith [mul_pos hMR hMR, mul_nonneg hD hMR.le, mul_nonneg hE0 hMR.le]
