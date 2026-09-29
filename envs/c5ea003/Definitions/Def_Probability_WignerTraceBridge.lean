-- Prove2me | Definitions.Def_Probability_WignerTraceBridge
-- name    : Probability_WignerTraceBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:22.178254+00:00
-- url     : https://prove2.me/theorems/91c75fb5-0591-4ed4-867b-39032f02f800
-- title:
--   Aether Catalog definitions — Probability_WignerTraceBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerTraceBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerTraceBridge.lean by skeleton subtraction
import Mathlib
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

namespace WignerBridge

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]



/-- The `k`-th moment of the empirical spectral distribution of a Hermitian matrix:
the average of the `k`-th powers of its eigenvalues. -/
noncomputable def esdMoment {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  (1 / (Fintype.card n : ℝ)) * ∑ i, (hA.eigenvalues i) ^ k


/-- The `√N`-normalised spectral moment used in the semicircle law: the `k`-th ESD
moment of `A / √N`. -/
noncomputable def normalizedMoment (A : Matrix n n ℝ) (k : ℕ) : ℝ :=
  (1 / (Fintype.card n : ℝ)) *
    (((Real.sqrt (Fintype.card n))⁻¹ • A) ^ k).trace



end WignerBridge


