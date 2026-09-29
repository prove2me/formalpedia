-- Prove2me | Theorems.Thm_RainbowAP_sum_choose_missCount
-- name    : RainbowAP.sum_choose_missCount
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:36.617917+00:00
-- url     : https://prove2.me/theorems/83a679ea-5da5-4b2c-8c05-a27fdcfd423b
-- title:
--   The `r`-th binomial moment identity.
-- statement:
--   **The `r`-th binomial moment identity.**
--
--   ```lean
--   theorem RainbowAP.sum_choose_missCount(r m : ℕ) :
--       ∑ f : Fin m → α, (missCount f).choose r
--         = (Fintype.card α).choose r * (Fintype.card α - r) ^ m := by sorry
--   /-- The first moment identity is the case `r = 1`. -/
--   example (m : ℕ) :
--       ∑ f : Fin m → α, missCount f = Fintype.card α * (Fintype.card α - 1) ^ m := by
--     have h := sum_choose_missCount (α := α) 1 m
--     simpa [Nat.choose_one_right] using h
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPHigherMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPHigherMoments.lean#L48

-- Thm stub generated from Shared/RainbowAPHigherMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

/-!
# All binomial moments of the missed-letter count

The first and second moment identities of `Shared.RainbowAPSpectrumMoments` are the cases
`r = 1, 2` of a single exact identity: for every `r`,

  `∑_{f : Fin m → α} C(missCount f, r) = C(N, r) · (N - r) ^ m`,  `N = |α|`.

Equivalently, the `r`-th binomial moment of the number of missed letters of a uniformly random
word is `C(N,r)(1 - r/N)^m`, which is the moment sequence of a Poisson variable of mean
`N (1-1/N)^m` in the limit.  This is the exact combinatorial input needed for a Poisson limit
law of the full-spectrum transition.
-/

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem RainbowAP.sum_choose_missCount(r m : ℕ) :
    ∑ f : Fin m → α, (missCount f).choose r
      = (Fintype.card α).choose r * (Fintype.card α - r) ^ m := by sorry
