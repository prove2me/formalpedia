-- Prove2me | solution 1 for Spike.Quantile.firstDecile_eq_residue_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:50:23.284982+00:00
-- url     : https://prove2.me/submissions/64a3fee5-28e9-4231-872e-c0796a9f9f8f

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









/-! ### The round-85 window: the decile cut *is* a magnitude cut -/


variable (m : ℕ)

/-- On the exactly divisible modulus `N = (5m)^2` the square root is `5m`. -/
theorem sqrt_sq_five (m : ℕ) : Nat.sqrt ((5 * m) ^ 2) = 5 * m := Nat.sqrt_eq' (5 * m)


/-- The residue at position `5m + t` of the modulus `(5m)^2` is `10mt + t^2`. -/
theorem residue_shift (m t : ℕ) :
    residue ((5 * m) ^ 2) (5 * m + t) = 10 * m * t + t ^ 2 := by
  have h : (5 * m + t) ^ 2 = (5 * m) ^ 2 + (10 * m * t + t ^ 2) := by ring
  simp only [residue, h]
  omega







open Spike.Quantile in
theorem solution(m : ℕ) {j : ℕ}
    (hj : j ∈ window ((5 * m) ^ 2)) :
    inFirstDecile ((5 * m) ^ 2) j ↔ residue ((5 * m) ^ 2) j ≤ 11 * m ^ 2 := by
  simp only [window, Finset.mem_Icc, sqrt_sq_five] at hj
  obtain ⟨hlo, hhi⟩ := hj
  obtain ⟨t, rfl⟩ : ∃ t, j = 5 * m + t := ⟨j - 5 * m, by omega⟩
  have hres := residue_shift m t
  constructor
  · rintro ⟨-, hdec⟩
    have ht : t ≤ m := by
      simp only [sqrt_sq_five] at hdec
      omega
    have : 10 * m * t + t ^ 2 ≤ 10 * m * m + m ^ 2 := by
      have h1 : 10 * m * t ≤ 10 * m * m := Nat.mul_le_mul_left _ ht
      have h2 : t ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left ht 2
      omega
    rw [hres]
    nlinarith
  · intro hle
    rw [hres] at hle
    have ht : t ≤ m := by
      by_contra hcon
      push_neg at hcon
      have h1 : 10 * m * (m + 1) ≤ 10 * m * t := Nat.mul_le_mul_left _ hcon
      nlinarith
    refine ⟨⟨by simpa [sqrt_sq_five] using hlo, by simpa [sqrt_sq_five] using hhi⟩, ?_⟩
    simp only [sqrt_sq_five]
    omega
