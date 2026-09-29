-- Prove2me | Theorems.Thm_Rademacher_signAvg_le_of_bound
-- name    : Rademacher.signAvg_le_of_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:48.989184+00:00
-- url     : https://prove2.me/theorems/36d054b6-0bc3-479e-9acc-b146d3143bae
-- title:
--   A vector with coordinates bounded by `B` has sign-average bounded by `B`.
-- statement:
--   A vector with coordinates bounded by `B` has sign-average bounded by `B`.
--
--   ```lean
--   theorem Rademacher.signAvg_le_of_bound{v : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B)
--       (hv : ∀ i, |v i| ≤ B) (ε : Fin n → Bool) : signAvg ε v ≤ B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Basic.lean#L148

-- Thm stub generated from Logic/Rademacher/Basic.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Basic
/-
# Empirical Rademacher complexity: definitions and basic calculus

This file sets up the *empirical Rademacher complexity* of a class of real vectors
indexed by a finite sample of size `n`.  If `F : Set (Fin n → ℝ)` is the restriction
of a hypothesis class to a sample `x₁, …, xₙ`, its empirical Rademacher complexity is

  `R(F) = 𝔼_σ [ sup_{v ∈ F} (1/n) ∑ i, σ i * v i ]`,

where `σ` ranges uniformly over the `2ⁿ` sign vectors in `{-1, 1}ⁿ`.
The expectation is realised as an explicit finite average over `Fin n → Bool`.

The basic calculus proved here: the complexity of a singleton vanishes, it is
monotone in the class, nonnegative for nonempty classes, homogeneous under scaling,
invariant under translation, and bounded by any uniform bound on the coordinates.
-/

open Rademacher

open Finset

variable {n : ℕ}

theorem Rademacher.signAvg_le_of_bound{v : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i, |v i| ≤ B) (ε : Fin n → Bool) : signAvg ε v ≤ B := by sorry
