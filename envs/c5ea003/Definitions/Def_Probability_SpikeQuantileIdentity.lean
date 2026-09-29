-- Prove2me | Definitions.Def_Probability_SpikeQuantileIdentity
-- name    : Probability_SpikeQuantileIdentity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:57.537557+00:00
-- url     : https://prove2.me/theorems/d8e574ae-088b-4fa4-b243-354ef77d6dbe
-- title:
--   Aether Catalog definitions — Probability_SpikeQuantileIdentity
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SpikeQuantileIdentity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SpikeQuantileIdentity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry

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

namespace Spike.Quantile

open Spike

variable {N : ℕ}

instance decidableInWindow (N j : ℕ) : Decidable (inWindow N j) := by
  unfold inWindow; infer_instance

instance decidableInFirstDecile (N j : ℕ) : Decidable (inFirstDecile N j) := by
  unfold inFirstDecile; infer_instance

/-- The stored window as a finite set of positions. -/
def window (N : ℕ) : Finset ℕ := Finset.Icc (Nat.sqrt N + 1) (3 * Nat.sqrt N)






/-! ### The round-85 window: the decile cut *is* a magnitude cut -/

section Divisible

variable (m : ℕ)








end Divisible

end Spike.Quantile


