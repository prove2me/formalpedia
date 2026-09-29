-- Prove2me | Theorems.Thm_CollatzSpectral_common_resonance_three_five
-- name    : CollatzSpectral.common_resonance_three_five
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:22:30.413117+00:00
-- url     : https://prove2.me/theorems/e61bbf16-250e-437e-9171-9add9bb0c1c1
-- title:
--   The `3n+1` and `5n+1` maps share only the trivial resonances.
-- statement:
--   **The `3n+1` and `5n+1` maps share only the trivial resonances.**  Their
--   common spectral gaps occur exactly at odd integer frequencies.
--
--   ```lean
--   theorem CollatzSpectral.common_resonance_three_five(ω : ℝ) :
--       (limitAmp 3 ω = 0 ∧ limitAmp 5 ω = 0) ↔ ∃ t : ℤ, ω = 2 * (t : ℝ) + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CollatzSpectralResonance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CollatzSpectralResonance.lean#L76

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

theorem CollatzSpectral.common_resonance_three_five(ω : ℝ) :
    (limitAmp 3 ω = 0 ∧ limitAmp 5 ω = 0) ↔ ∃ t : ℤ, ω = 2 * (t : ℝ) + 1 := by sorry
