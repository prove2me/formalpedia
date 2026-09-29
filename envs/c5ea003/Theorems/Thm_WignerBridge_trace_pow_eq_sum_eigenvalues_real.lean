-- Prove2me | Theorems.Thm_WignerBridge_trace_pow_eq_sum_eigenvalues_real
-- name    : WignerBridge.trace_pow_eq_sum_eigenvalues_real
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:01:37.432985+00:00
-- url     : https://prove2.me/theorems/35c083c3-a592-4cf5-a633-0ef6a8d01aa2
-- title:
--   Real symmetric version of the trace–eigenvalue bridge.
-- statement:
--   Real symmetric version of the trace–eigenvalue bridge.
--
--   ```lean
--   theorem WignerBridge.trace_pow_eq_sum_eigenvalues_real{A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
--       (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerTraceBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerTraceBridge.lean#L36

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

theorem WignerBridge.trace_pow_eq_sum_eigenvalues_real{A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by sorry
