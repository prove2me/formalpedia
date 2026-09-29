-- Prove2me | solution 1 for FermatPosition.card_positions_value_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:14:00.064197+00:00
-- url     : https://prove2.me/submissions/7ae82e9f-6f9f-49c2-b660-0874948f3906

-- Sol generated from NumberTheory/FermatPositionDensity.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionDensity
import Definitions.Def_NumberTheory_FermatPositionGeometry
/-
# Densities of the two position carriers of the Fermat / quadratic-sieve polynomial

Companion to `Catalog/NumberTheory/FermatPositionGeometry.lean`.

That file isolated two magnitude-free ("beyond-magnitude") arithmetic mechanisms that
could bias where the smooth values of `v(j) = (b + j)^2 - N` sit:

* the **gcd carrier** `g(j) = gcd (j, v(0))`, which is *positionally uniform*
  (`FermatPosition.gcd_carrier_window_card_indep`), so it enriches smoothness without
  favouring any position; and
* the **self-divisibility carrier** `j ∣ v(j) ↔ j ∣ v(0)`, whose density at position
  `j` is exactly `1/j`.

This file proves the quantitative half of the story.

Main results.

* `dvd_window_card_eq_one`, `card_filter_dvd` : exactly one multiple of `d` in every
  window of `d` consecutive integers, hence exactly `t` in a window of length `d * t`;
  the self-divisibility carrier has density exactly `1/j` at position `j`.
* `harmonic_block_decline` : `∑_{K < j ≤ 2K} 1/j < ∑_{1 ≤ j ≤ K} 1/j` for `K ≥ 1`.
* `divisor_positions_small_j_excess` : consequently, averaged over base values `v(0)`,
  the expected number of positions `j ≤ K` with `j ∣ v(j)` **strictly exceeds** the
  expected number in the next block `K < j ≤ 2K`.  A proved, magnitude-free, small-`j`
  excess — the shape of the empirically observed monotone-declining deciles.
* `sieveVal_sandwich` and `position_le_of_value_le` : the competing *magnitude* law,
  `2 b j ≤ v(j) ≤ 2 b j + j² + 2 b`, so a bound on the value forces a bound on the
  position (`j ≤ X / (2b)`).  This is what a positional test has to be controlled
  against, and by `FermatPosition.cell_collapse` bit-length cells do not control it.
-/

open FermatPosition

open Finset

/-! ## Exact density of the self-divisibility carrier -/



/-! ## The harmonic decline of the divisor-position profile -/




/-! ## Discrepancy of local (periodic) carriers

The general principle behind `FermatPosition.gcd_carrier_window_card_indep`: a carrier
that is *local*, i.e. determined by the position modulo some fixed `T`, has a bounded
discrepancy in every window.  It can never produce more than `T` excess hits between two
consecutive blocks of equal length.  Contrapositively, an observed positional excess of
`E` hits between consecutive equal blocks forces **every** local explanation to have
modulus `T ≥ E`. -/







/-! ## The competing magnitude law -/

/-- Two-sided sandwich for the sieve polynomial at `b = ⌈√N⌉`:
`2 b j ≤ v(j) ≤ 2 b j + j² + 2 b`.  The value is essentially `2 b j`, so magnitude and
position are tied together by a linear law. -/
theorem sieveVal_sandwich {b N j : ℤ} (hj : 0 ≤ j) (hN₁ : (b - 1) ^ 2 ≤ N)
    (hN₂ : N ≤ b ^ 2) :
    2 * b * j ≤ sieveVal b N j ∧ sieveVal b N j ≤ 2 * b * j + j ^ 2 + 2 * b := by
  constructor
  · simp only [sieveVal]; nlinarith
  · simp only [sieveVal]; nlinarith

/-- A bound on the magnitude forces a bound on the position: all positions carrying a
value below `X` lie below `X / (2b)`.  This is the *magnitude* explanation of small-`j`
clustering, against which any claimed positional structure must be controlled. -/
theorem position_le_of_value_le {b N j X : ℤ} (hj : 0 ≤ j)
    (hN₁ : (b - 1) ^ 2 ≤ N) (hN₂ : N ≤ b ^ 2) (hX : sieveVal b N j ≤ X) :
    2 * b * j ≤ X :=
  le_trans (sieveVal_sandwich hj hN₁ hN₂).1 hX






open FermatPosition in
theorem solution{b N X : ℤ} (hb : 1 ≤ b) (hN₁ : (b - 1) ^ 2 ≤ N)
    (hN₂ : N ≤ b ^ 2) (J : ℕ) :
    ((range J).filter (fun i : ℕ => sieveVal b N ((i : ℤ) + 1) ≤ X)).card
      ≤ (X / (2 * b)).toNat := by
  classical
  have hb0 : (0 : ℤ) < 2 * b := by linarith
  have hsub : (range J).filter (fun i : ℕ => sieveVal b N ((i : ℤ) + 1) ≤ X)
      ⊆ range (X / (2 * b)).toNat := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    have hpos : (0 : ℤ) ≤ (i : ℤ) + 1 := by positivity
    have hlin : 2 * b * ((i : ℤ) + 1) ≤ X :=
      position_le_of_value_le hpos hN₁ hN₂ hi.2
    have hdiv : (i : ℤ) + 1 ≤ X / (2 * b) := Int.le_ediv_iff_mul_le hb0 |>.2 (by linarith)
    have hX : 0 < X / (2 * b) := by omega
    refine mem_range.2 ?_
    omega
  calc ((range J).filter (fun i : ℕ => sieveVal b N ((i : ℤ) + 1) ≤ X)).card
      ≤ (range (X / (2 * b)).toNat).card := card_le_card hsub
    _ = (X / (2 * b)).toNat := card_range _
