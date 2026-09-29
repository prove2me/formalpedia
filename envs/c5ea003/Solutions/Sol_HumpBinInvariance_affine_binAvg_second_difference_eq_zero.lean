-- Prove2me | solution 1 for HumpBinInvariance.affine_binAvg_second_difference_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:46:41.40961+00:00
-- url     : https://prove2.me/submissions/aae49300-5b64-4128-a905-0a9e0cdff3e1

-- Sol generated from Algebra/HumpBinInvariance.lean
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



/-- Consecutive bins are equally spaced: sample `(k+1)w+i` is the midpoint of
samples `kw+i` and `(k+2)w+i`. -/
theorem sample_midpoint (a δ : ℝ) (w k i : ℕ) :
    sample a δ (k * w + i) + sample a δ ((k + 2) * w + i)
      = 2 * sample a δ ((k + 1) * w + i) := by
  simp only [sample]
  push_cast
  ring

/-! ## 2. Midpoint concavity -/

variable {S : Set ℝ} {g : ℝ → ℝ}



/-! ## 3. Binning preserves concavity -/




/-! ## 4. Unimodality: the binned profile has a single peak -/



/-! ## 5. The sieve instance -/




open HumpBinInvariance in
theorem solution(u v a δ : ℝ) (w k : ℕ) :
    binAvg a δ w (fun y => u + v * y) k + binAvg a δ w (fun y => u + v * y) (k + 2)
      = 2 * binAvg a δ w (fun y => u + v * y) (k + 1) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [binAvg]
  have hwR : (0 : ℝ) ≠ (w : ℝ) := by
    have : (0 : ℝ) < w := by exact_mod_cast hw
    linarith
  have hterm : ∀ i ∈ range w,
      (u + v * sample a δ (k * w + i)) + (u + v * sample a δ ((k + 2) * w + i))
        = 2 * (u + v * sample a δ ((k + 1) * w + i)) := by
    intro i _
    have hmid := sample_midpoint a δ w k i
    linear_combination v * hmid
  have hsum : (∑ i ∈ range w, (u + v * sample a δ (k * w + i)))
      + (∑ i ∈ range w, (u + v * sample a δ ((k + 2) * w + i)))
      = 2 * ∑ i ∈ range w, (u + v * sample a δ ((k + 1) * w + i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  simp only [binAvg, ← add_div]
  rw [hsum]
  field_simp
