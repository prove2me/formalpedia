-- Prove2me | Theorems.Thm_CollatzSpectral_resonance_sets_pairwise_distinct
-- name    : CollatzSpectral.resonance_sets_pairwise_distinct
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:23:12.815406+00:00
-- url     : https://prove2.me/theorems/714e5ae4-e285-487c-860c-e1d01fbacb33
-- title:
--   Separation of the three classical multipliers.
-- statement:
--   **Separation of the three classical multipliers.**  There is a frequency at
--   which `3n+1` has a spectral gap while `5n+1` and `7n+1` do not, and symmetrically
--   for the other two multipliers; the three resonance sets are pairwise distinct.
--
--   ```lean
--   theorem CollatzSpectral.resonance_sets_pairwise_distinct:
--       (limitAmp 3 (1 / 5 : ℝ) = 0 ∧ limitAmp 5 (1 / 5 : ℝ) ≠ 0 ∧ limitAmp 7 (1 / 5 : ℝ) ≠ 0) ∧
--       (limitAmp 5 (1 / 9 : ℝ) = 0 ∧ limitAmp 3 (1 / 9 : ℝ) ≠ 0 ∧ limitAmp 7 (1 / 9 : ℝ) ≠ 0) ∧
--       (limitAmp 7 (1 / 13 : ℝ) = 0 ∧ limitAmp 3 (1 / 13 : ℝ) ≠ 0 ∧
--         limitAmp 5 (1 / 13 : ℝ) ≠ 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CollatzSpectralResonance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CollatzSpectralResonance.lean#L122

-- Thm stub generated from Novelty/CollatzSpectralResonance.lean
import Mathlib
import Definitions.Def_Novelty_CollatzSpectralNormalized

/-!
# The arithmetic of the resonance sets of the `a n + 1` maps

`Catalog/Novelty/CollatzSpectralNormalized.lean` shows that the normalized
transform of the `a n + 1` map converges to `limitAmp a ω`, and that it vanishes
exactly on the *resonance set*

`R a = {ω : (2a - 1) ω ∈ 2ℤ + 1}`.

This file studies the arithmetic of these sets.  The picture that emerges is a
clean dichotomy:

* every multiplier resonates at every odd integer frequency
  (`limitAmp_odd_int`) — these carry no information about `a`;
* off the odd integers the resonance sets are genuinely different, and their
  pairwise intersections are governed by a linear Diophantine condition.  For
  the three classical multipliers we compute the intersections exactly
  (`common_resonance_three_five`, `common_resonance_three_seven`,
  `common_resonance_five_seven`): they contain *nothing but* the trivial odd
  integers.

Thus any spectral discriminator between the `3n+1`, `5n+1` and `7n+1` maps must
be read off at non-integer frequencies; the behaviour near frequency `0`, or at
any integer frequency, is identical for all three maps
(`limitAmp_int_indep_of_multiplier`).
-/

open CollatzSpectral

open Filter Complex
open scoped Real Topology

theorem CollatzSpectral.resonance_sets_pairwise_distinct:
    (limitAmp 3 (1 / 5 : ℝ) = 0 ∧ limitAmp 5 (1 / 5 : ℝ) ≠ 0 ∧ limitAmp 7 (1 / 5 : ℝ) ≠ 0) ∧
    (limitAmp 5 (1 / 9 : ℝ) = 0 ∧ limitAmp 3 (1 / 9 : ℝ) ≠ 0 ∧ limitAmp 7 (1 / 9 : ℝ) ≠ 0) ∧
    (limitAmp 7 (1 / 13 : ℝ) = 0 ∧ limitAmp 3 (1 / 13 : ℝ) ≠ 0 ∧
      limitAmp 5 (1 / 13 : ℝ) ≠ 0) := by sorry
