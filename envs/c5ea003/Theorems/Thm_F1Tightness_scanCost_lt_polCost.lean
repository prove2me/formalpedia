-- Prove2me | Theorems.Thm_F1Tightness_scanCost_lt_polCost
-- name    : F1Tightness.scanCost_lt_polCost
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:27:09.812341+00:00
-- url     : https://prove2.me/theorems/9f7bf498-de6c-49b3-9592-56d62843fdb0
-- title:
--   Strict rearrangement.
-- statement:
--   **Strict rearrangement.**  On a strictly front-loaded profile every policy
--   other than the ascending scan is strictly more expensive.
--
--   ```lean
--   theorem F1Tightness.scanCost_lt_polCost{p : Fin M → ℝ} (hanti : StrictAnti p)
--       {σ : Equiv.Perm (Fin M)} (hσ : σ ≠ 1) : scanCost p < polCost p σ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessUniqueness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessUniqueness.lean#L59

-- Thm stub generated from Probability/F1TightnessUniqueness.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore

/-!
# Uniqueness of the optimal scan policy (paper 250)

`Probability.F1TightnessCore` shows that on an antitone profile the ascending
scan minimises the expected probe count, so its speed-up `S_asc = 1/Λ` is the
best realizable one and the master bound overshoots it by the factor `X`.  Here
we sharpen that statement: on a *strictly* front-loaded profile the ascending
scan is the **unique** minimiser, so the quantity `S_asc` compared with the
bound is not an artefact of a particular tie-breaking among optimal policies.

Main results.

* `perm_eq_one_of_strictMono` — a strictly monotone permutation of `Fin M` is
  the identity (hence a non-identity policy always has an inversion).
* `scanCost_lt_polCost` — strict rearrangement: every policy other than the
  ascending one is strictly more expensive on a strictly antitone profile.
* `polCost_eq_scanCost_iff` — the optimal policy is unique.
* `speedup_lt_Sasc` — consequently the ascending speed-up strictly dominates
  every other policy, and (with `F1Tightness.speedup_lt_bound`) still falls
  short of the master bound by the factor `X`.
-/

open Finset

open F1Tightness

variable {M : ℕ}

theorem F1Tightness.scanCost_lt_polCost{p : Fin M → ℝ} (hanti : StrictAnti p)
    {σ : Equiv.Perm (Fin M)} (hσ : σ ≠ 1) : scanCost p < polCost p σ := by sorry
