-- Prove2me | Theorems.Thm_RademacherWigner_expect_const
-- name    : RademacherWigner.expect_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:02:19.861229+00:00
-- url     : https://prove2.me/theorems/3e966d4e-6b9f-4fc2-b34e-d59934a088dd
-- title:
--   Expect const
-- statement:
--   Formal statement of `RademacherWigner.expect_const` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RademacherWigner.expect_const(c : ℝ) : expect (fun _ : Config N => c) = c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerRademacherEnsemble.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerRademacherEnsemble.lean#L124

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

theorem RademacherWigner.expect_const(c : ℝ) : expect (fun _ : Config N => c) = c := by sorry
