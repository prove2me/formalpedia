-- Prove2me | Theorems.Thm_RademacherWigner_sum_indA
-- name    : RademacherWigner.sum_indA
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:04:00.001238+00:00
-- url     : https://prove2.me/theorems/bd386fc9-905f-47a8-999f-dea8dcbc64b6
-- title:
--   Sum indA
-- statement:
--   Formal statement of `RademacherWigner.sum_indA` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RademacherWigner.sum_indA(N : ℕ) :
--       (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, indA i j k l)
--         = (N:ℝ) * ((N:ℝ) - 1) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerRademacherEnsemble.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerRademacherEnsemble.lean#L329

-- Thm stub generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The symmetric Rademacher Wigner ensemble and its spectral moments

This file constructs a concrete Wigner ensemble — the uniform measure on real
symmetric `N × N` sign matrices with zero diagonal — and computes the first
nontrivial normalised spectral moments of `W/√N` by the moment method:

* the second moment is **deterministically** `1 - 1/N` (self-averaging), and
* the expected fourth moment is exactly `(N-1)(2N-3)/N²`.

Both converge to the corresponding moments of the Wigner semicircle law,
`C₁ = 1` and `C₂ = 2` (see `Probability.WignerSemicircleMoments`), which is the
moment-method statement of the semicircle law at orders 2 and 4.

The key probabilistic input is a *sign-flip involution*: if some edge of the
closed walk `i → j → k → l → i` is traversed an odd number of times, flipping
the corresponding Rademacher variable negates the summand, so the expectation
vanishes.  This replaces the usual independence/factorisation argument by an
exact combinatorial symmetry.
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}















/-! ### The second spectral moment is deterministic -/


/-! ### Expectation over the ensemble -/






/-! ### The sign-flip involution -/



/-! ### The fourth moment -/

theorem RademacherWigner.sum_indA(N : ℕ) :
    (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, indA i j k l)
      = (N:ℝ) * ((N:ℝ) - 1) ^ 2 := by sorry
