-- Prove2me | Theorems.Thm_Talagrand_dTsq_singleton
-- name    : Talagrand.dTsq_singleton
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:10:31.055965+00:00
-- url     : https://prove2.me/theorems/0c12d23b-013c-458d-92fe-fc02f7f1311b
-- title:
--   The convex distance to a singleton is the squared Hamming distance.
-- statement:
--   The convex distance to a singleton is the squared Hamming distance.
--
--   ```lean
--   theorem Talagrand.dTsq_singleton(y x : Fin n → α) :
--       dTsq {y} x = ∑ i, hamm (x i) (y i) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TalagrandHypercube.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TalagrandHypercube.lean#L27

-- Thm stub generated from Probability/TalagrandHypercube.lean
import Mathlib
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandHypercube

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

open Talagrand

open Finset Real

variable {α : Type*} [DecidableEq α] {n : ℕ}

theorem Talagrand.dTsq_singleton(y x : Fin n → α) :
    dTsq {y} x = ∑ i, hamm (x i) (y i) ^ 2 := by sorry
