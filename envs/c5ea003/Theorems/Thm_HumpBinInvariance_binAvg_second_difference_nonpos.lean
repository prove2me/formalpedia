-- Prove2me | Theorems.Thm_HumpBinInvariance_binAvg_second_difference_nonpos
-- name    : HumpBinInvariance.binAvg_second_difference_nonpos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:37:49.57144+00:00
-- url     : https://prove2.me/theorems/62f5835a-2c35-447f-8887-26b6e39e2dad
-- title:
--   Bin-width and grid-shift invariance of concavity.
-- statement:
--   **Bin-width and grid-shift invariance of concavity.**  Whatever the bin width
--   `w`, the grid offset `a` and the sample spacing `δ`, the binned averages of a
--   concave profile are discretely concave.
--
--   ```lean
--   theorem HumpBinInvariance.binAvg_second_difference_nonpos(hg : ConcaveOn ℝ S g) {a δ : ℝ}
--       (hmem : ∀ i : ℕ, sample a δ i ∈ S) (w k : ℕ) :
--       binAvg a δ w g k + binAvg a δ w g (k + 2) ≤ 2 * binAvg a δ w g (k + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/HumpBinInvariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/HumpBinInvariance.lean#L84

-- Thm stub generated from Algebra/HumpBinInvariance.lean
import Mathlib
import Definitions.Def_Algebra_HumpBinInvariance
import Definitions.Def_Algebra_HumpWindowGeometry
/-
# Binning cannot create, destroy, or split the hump

Third formal core of experiment **581** (paper 231).  The pre-stated next probe
of the surviving channel `H0` is a **direct `j`-grid / `v`-size sensitivity
analysis: bin-width permutation and `u`-grid shift**.  The experiment reports a
binned profile on `64` positions with `R_peak` at bin `33`; the worry the probe
addresses is whether the concave shape and the single peak are artefacts of that
particular binning.

This file settles the discretisation half of the probe, in full generality.

## Main results

* `HumpBinInvariance.binAvg_second_difference_nonpos` — for **every** bin width
  `w`, **every** grid offset `a` and **every** sample spacing `δ`, the binned
  averages of a concave profile satisfy the discrete concavity inequality
  `b k + b (k+2) ≤ 2 · b (k+1)`.
* `HumpBinInvariance.binAvg_second_difference_neg` — strictly, for a strictly
  concave profile with `w ≥ 1` and `δ ≠ 0`.
* `HumpBinInvariance.affine_binAvg_second_difference_eq_zero` — the **control**:
  an affine profile bins to an exactly affine sequence, second difference `0`.
  A measured non-zero curvature therefore cannot come from the binning.
* `HumpBinInvariance.antitone_after_descent` — discrete concavity forces
  **unimodality**: once the binned profile turns down it never turns back up, so
  the binned profile has a single peak.  No bin-width permutation can split the
  measured peak into two, nor manufacture one.
* `HumpBinInvariance.window_binAvg_second_difference_neg` — the sieve
  instance: for `logSize c`, the log-size profile of `j² − N`, the binned profile
  is strictly discretely concave at every bin width and offset.

Conclusion for the experiment: `H0` **passes** the discretisation half of the
named probe — the concavity and single-peakedness of `R` are grid invariants of
any concave underlying profile.  What binning cannot rescue is the *vertex
location*, which `HumpWindowGeometry.vertex_lt_midpoint` pins strictly left of
centre while the measurement puts it at `0.5901`.
-/

open HumpBinInvariance

open Finset Set HumpWindowGeometry

/-! ## 1. Sample grid and bin averages -/




/-! ## 2. Midpoint concavity -/

variable {S : Set ℝ} {g : ℝ → ℝ}



/-! ## 3. Binning preserves concavity -/

theorem HumpBinInvariance.binAvg_second_difference_nonpos(hg : ConcaveOn ℝ S g) {a δ : ℝ}
    (hmem : ∀ i : ℕ, sample a δ i ∈ S) (w k : ℕ) :
    binAvg a δ w g k + binAvg a δ w g (k + 2) ≤ 2 * binAvg a δ w g (k + 1) := by sorry
