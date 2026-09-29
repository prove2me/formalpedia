-- Prove2me | Definitions.Def_Algebra_HumpBinInvariance
-- name    : Algebra_HumpBinInvariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:21:22.628712+00:00
-- url     : https://prove2.me/theorems/ac4a6185-6f5d-451a-bad2-a070eb57f076
-- title:
--   Aether Catalog definitions — Algebra_HumpBinInvariance
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.HumpBinInvariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/HumpBinInvariance.lean by skeleton subtraction
import Mathlib
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

namespace HumpBinInvariance

open Finset Set HumpWindowGeometry

/-! ## 1. Sample grid and bin averages -/

/-- The raw `j`-grid: sample `i` sits at `a + δ i`. -/
noncomputable def sample (a δ : ℝ) (i : ℕ) : ℝ := a + δ * i

/-- The binned profile: average of `g` over the `w` samples of bin `k`. -/
noncomputable def binAvg (a δ : ℝ) (w : ℕ) (g : ℝ → ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ range w, g (sample a δ (k * w + i))) / w


/-! ## 2. Midpoint concavity -/

variable {S : Set ℝ} {g : ℝ → ℝ}



/-! ## 3. Binning preserves concavity -/




/-! ## 4. Unimodality: the binned profile has a single peak -/



/-! ## 5. The sieve instance -/



end HumpBinInvariance


