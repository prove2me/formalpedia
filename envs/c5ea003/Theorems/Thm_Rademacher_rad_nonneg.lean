-- Prove2me | Theorems.Thm_Rademacher_rad_nonneg
-- name    : Rademacher.rad_nonneg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:31.620153+00:00
-- url     : https://prove2.me/theorems/ec912bd0-4f3b-4059-a906-2e12fc0276db
-- title:
--   The Rademacher complexity of a nonempty class is nonnegative.
-- statement:
--   The Rademacher complexity of a nonempty class is nonnegative.
--
--   ```lean
--   theorem Rademacher.rad_nonneg{F : Set (Fin n → ℝ)} (hF : F.Nonempty)
--       (hb : ∀ ε : Fin n → Bool, BddAbove (signAvg ε '' F)) :
--       0 ≤ rad F := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Basic.lean#L97

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

theorem Rademacher.rad_nonneg{F : Set (Fin n → ℝ)} (hF : F.Nonempty)
    (hb : ∀ ε : Fin n → Bool, BddAbove (signAvg ε '' F)) :
    0 ≤ rad F := by sorry
