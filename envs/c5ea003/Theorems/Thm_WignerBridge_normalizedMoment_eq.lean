-- Prove2me | Theorems.Thm_WignerBridge_normalizedMoment_eq
-- name    : WignerBridge.normalizedMoment_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:02:00.085767+00:00
-- url     : https://prove2.me/theorems/a8f4b03a-cb1d-4e70-9eff-e2b141d7f9e4
-- title:
--   NormalizedMoment eq
-- statement:
--   Formal statement of `WignerBridge.normalizedMoment_eq` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem WignerBridge.normalizedMoment_eq(A : Matrix n n ℝ) (k : ℕ) :
--       normalizedMoment A k =
--         (1 / (Fintype.card n : ℝ)) * (Real.sqrt (Fintype.card n))⁻¹ ^ k * (A ^ k).trace := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerTraceBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerTraceBridge.lean#L56

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

theorem WignerBridge.normalizedMoment_eq(A : Matrix n n ℝ) (k : ℕ) :
    normalizedMoment A k =
      (1 / (Fintype.card n : ℝ)) * (Real.sqrt (Fintype.card n))⁻¹ ^ k * (A ^ k).trace := by sorry
