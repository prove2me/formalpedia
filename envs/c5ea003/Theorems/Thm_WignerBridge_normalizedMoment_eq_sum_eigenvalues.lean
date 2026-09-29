-- Prove2me | Theorems.Thm_WignerBridge_normalizedMoment_eq_sum_eigenvalues
-- name    : WignerBridge.normalizedMoment_eq_sum_eigenvalues
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:01:40.754503+00:00
-- url     : https://prove2.me/theorems/7db52495-b540-4e91-a2f7-cf1c12d5dd3f
-- title:
--   The normalised spectral moment is the average of the `k`-th powers of the
-- statement:
--   The normalised spectral moment is the average of the `k`-th powers of the
--   rescaled eigenvalues `λᵢ / √N`; this is exactly the `k`-th moment of the empirical
--   spectral distribution of `A / √N`.
--
--   ```lean
--   theorem WignerBridge.normalizedMoment_eq_sum_eigenvalues{A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
--       normalizedMoment A k =
--         (1 / (Fintype.card n : ℝ)) *
--           ∑ i, (hA.eigenvalues i / Real.sqrt (Fintype.card n)) ^ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerTraceBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerTraceBridge.lean#L62

-- Thm stub generated from Probability/WignerTraceBridge.lean
import Mathlib
import Definitions.Def_Probability_WignerTraceBridge
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The trace–eigenvalue bridge for empirical spectral distributions

The moment method for the Wigner semicircle law rests on the identity

  (1/N) Σᵢ λᵢᵏ = (1/N) tr(Aᵏ),

which converts a statement about the *empirical spectral distribution* (ESD) of a
Hermitian matrix into a statement about traces of powers, i.e. into a sum over
closed walks in the complete graph.  This file proves that bridge for arbitrary
Hermitian matrices over an `RCLike` field, specialises it to the real symmetric
case, and sets up the `√N`-normalised spectral moments used in the semicircle law.
-/

open Matrix BigOperators

open WignerBridge

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem WignerBridge.normalizedMoment_eq_sum_eigenvalues{A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    normalizedMoment A k =
      (1 / (Fintype.card n : ℝ)) *
        ∑ i, (hA.eigenvalues i / Real.sqrt (Fintype.card n)) ^ k := by sorry
