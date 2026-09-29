-- Prove2me | Theorems.Thm_Spike_Quantile_firstDecile_card
-- name    : Spike.Quantile.firstDecile_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:07:27.043293+00:00
-- url     : https://prove2.me/theorems/2462f0a9-d206-40a0-941e-5f63d96198f7
-- title:
--   The first decile of that window has exactly `m` positions.
-- statement:
--   The first decile of that window has exactly `m` positions.
--
--   ```lean
--   theorem Spike.Quantile.firstDecile_card(m : ℕ) :
--       ((window ((5 * m) ^ 2)).filter (fun j => inFirstDecile ((5 * m) ^ 2) j)).card = m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SpikeQuantileIdentity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SpikeQuantileIdentity.lean#L163

-- Thm stub generated from Probability/SpikeQuantileIdentity.lean
import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry
import Definitions.Def_Probability_SpikeQuantileIdentity

/-!
# The exact quantile identity: positional prefixes *are* magnitude sublevel sets

`Catalog/Probability/SpikePositionMagnitudeDegeneracy.lean` shows that, at a
fixed modulus, position and residue determine each other.  This file closes the
counting half of that statement (future direction 1 of
`FUTURE_DIRECTIONS.md`) in its exact, non-asymptotic form: the *empirical
quantile function of the residue on the window is an explicit closed-form
expression in the position variable*, namely

`#{ j ∈ W N : residue N j ≤ x } = min (3 * isqrt N) (isqrt (N + x)) - isqrt N`
(`Spike.Quantile.card_sublevel`),

so every magnitude sublevel set is literally a positional prefix
(`Spike.Quantile.sublevel_eq_prefix`) and conversely
(`Spike.Quantile.prefix_eq_sublevel`).

Applied to the geometry of the round-85 window this gives the sharp form of the
inclusion artifact.  For the exactly divisible moduli `N = (5m)^2` we obtain

* `Spike.Quantile.window_card` : the window has exactly `10 * m` positions;
* `Spike.Quantile.firstDecile_card` : the first decile has exactly `m` of them —
  it really is a tenth (`Spike.Quantile.firstDecile_is_a_tenth`);
* `Spike.Quantile.firstDecile_eq_residue_sublevel` : on that window the
  first-decile predicate is *equivalent* to the magnitude predicate
  `v ≤ 11 * m ^ 2` — the decile cut is a magnitude cut, with no positional
  content whatsoever;
* `Spike.Quantile.card_residue_le_eq_firstDecile_card` : consequently the
  first-decile count and the tiny-`v` count are the same number.

Together with `Spike.size_residue_lt_96` this upgrades "100% of first-decile
hits have `bitlen v < 96`" from a bound to an identity of counting statistics:
a first-decile analysis and a `v`-threshold analysis are the *same* analysis.
-/

open Spike.Quantile

open Spike

variable {N : ℕ}









/-! ### The round-85 window: the decile cut *is* a magnitude cut -/


variable (m : ℕ)

theorem Spike.Quantile.firstDecile_card(m : ℕ) :
    ((window ((5 * m) ^ 2)).filter (fun j => inFirstDecile ((5 * m) ^ 2) j)).card = m := by sorry
