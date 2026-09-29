-- Prove2me | solution 1 for Spike.Quantile.card_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:19.765342+00:00
-- url     : https://prove2.me/submissions/591f36ab-c6f4-45e8-85a0-1e8d529d81eb

-- Sol generated from Probability/SpikeQuantileIdentity.lean
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




/-- Above `isqrt N` the modulus never exceeds the square of the position. -/
theorem le_sq_of_window {j : ℕ} (hj : Nat.sqrt N + 1 ≤ j) : N ≤ j ^ 2 := by
  have h1 : N < (Nat.sqrt N + 1) ^ 2 := by simpa [pow_two] using Nat.lt_succ_sqrt N
  exact le_of_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_left hj 2))

/-- **Pointwise inversion of the sublevel condition.**  For a window position,
`residue N j ≤ x` holds exactly when `j ≤ isqrt (N + x)`. -/
theorem residue_le_iff {j x : ℕ} (hj : Nat.sqrt N + 1 ≤ j) :
    residue N j ≤ x ↔ j ≤ Nat.sqrt (N + x) := by
  have h := le_sq_of_window hj
  rw [Nat.le_sqrt']
  simp only [residue]
  omega

/-- **A magnitude sublevel set is a positional prefix.** -/
theorem sublevel_eq_prefix (x : ℕ) :
    (window N).filter (fun j => residue N j ≤ x)
      = Finset.Icc (Nat.sqrt N + 1) (min (3 * Nat.sqrt N) (Nat.sqrt (N + x))) := by
  ext j
  simp only [window, Finset.mem_filter, Finset.mem_Icc, le_min_iff]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hres⟩
    exact ⟨hlo, hhi, (residue_le_iff hlo).mp hres⟩
  · rintro ⟨hlo, hhi, hsq⟩
    exact ⟨⟨hlo, hhi⟩, (residue_le_iff hlo).mpr hsq⟩



/-! ### The round-85 window: the decile cut *is* a magnitude cut -/


variable (m : ℕ)










open Spike.Quantile in
theorem solution(x : ℕ) :
    ((window N).filter (fun j => residue N j ≤ x)).card
      = min (3 * Nat.sqrt N) (Nat.sqrt (N + x)) - Nat.sqrt N := by
  have hmono : Nat.sqrt N ≤ Nat.sqrt (N + x) := Nat.sqrt_le_sqrt (Nat.le_add_right _ _)
  have h3 : Nat.sqrt N ≤ 3 * Nat.sqrt N := by omega
  rw [sublevel_eq_prefix x, Nat.card_Icc]
  omega
