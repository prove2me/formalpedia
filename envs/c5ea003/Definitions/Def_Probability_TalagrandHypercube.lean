-- Prove2me | Definitions.Def_Probability_TalagrandHypercube
-- name    : Probability_TalagrandHypercube
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:43.07346+00:00
-- url     : https://prove2.me/theorems/820ca603-99f8-4155-82a2-6b93cd09849f
-- title:
--   Aether Catalog definitions — Probability_TalagrandHypercube
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TalagrandHypercube`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TalagrandHypercube.lean by skeleton subtraction
import Mathlib

/-!
# A concrete instance: the uniform hypercube

This file records two things that guard the general theory against vacuity.

* `Talagrand.dTsq_singleton` — the convex distance to a single point really is
  the Euclidean length of the Hamming vector, so `dTsq` is not identically `0`;
  in particular `dTsq {y} x = n` when `x` and `y` differ in every coordinate.
* `Talagrand.hypercube_ones_concentration` — Talagrand's inequality applied to
  the uniform measure on the discrete cube `Fin n → Bool` and to the normalised
  number-of-ones functional `x ↦ (#{i : x i}) / √n`, which is `1`-Lipschitz for
  the Hamming metric weighted by `w i = 1 / √n` (a weight vector of Euclidean
  norm exactly one).  The conclusion is the classical statement
  `P(f ≤ m) * P(f ≥ m + t) ≤ exp (-t²/4)`.
* `Talagrand.biased_cube_concentration` — the same conclusion for independent
  coins with arbitrary, coordinate-dependent biases `θ i ∈ [0, 1]`, an instance of
  the non-identically-distributed form of the inequality.
-/

namespace Talagrand

open Finset Real

variable {α : Type*} [DecidableEq α] {n : ℕ}



/-! ### The uniform measure on the discrete cube -/

/-- The uniform weight on the coordinates of the discrete cube. -/
noncomputable def unif (n : ℕ) : Fin n → Bool → ℝ := fun _ _ => 1 / 2



/-- Independent coins with *arbitrary*, coordinate-dependent biases `θ i`. -/
def biased {n : ℕ} (θ : Fin n → ℝ) : Fin n → Bool → ℝ :=
  fun i b => if b then θ i else 1 - θ i



/-- The normalised number-of-ones functional on the discrete cube. -/
noncomputable def ones (n : ℕ) (x : Fin n → Bool) : ℝ :=
  ∑ i, (1 / Real.sqrt n) * (if x i then 1 else 0)

/-- The uniform Hamming weight vector: `w i = 1 / √n`. -/
noncomputable def cubeWeight (n : ℕ) : Fin n → ℝ := fun _ => 1 / Real.sqrt n






end Talagrand


