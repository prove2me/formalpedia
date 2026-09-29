-- Prove2me | solution 1 for FermatPosition.card_filter_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:13:59.289835+00:00
-- url     : https://prove2.me/submissions/095b19b4-8be5-4615-9c22-c019b0998b9f

-- Sol generated from NumberTheory/FermatPositionDensity.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionDensity
import Definitions.Def_NumberTheory_FermatPositionGeometry
import Theorems.Thm_FermatPosition_window_card_eq_zmod
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

/-- Exactly one position in a window of `d` consecutive positions is divisible by `d`. -/
theorem dvd_window_card_eq_one (d : ℕ) (hd : 0 < d) (a : ℤ) :
    ((range d).filter (fun i : ℕ => (d : ℤ) ∣ (a + i))).card = 1 := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have h := window_card_eq_zmod d (fun j : ℤ => (d : ℤ) ∣ j) (fun x : ZMod d => x = 0)
    (fun j => by simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd j d).symm) a
  rw [h]
  simp [Finset.filter_eq']


/-! ## The harmonic decline of the divisor-position profile -/




/-! ## Discrepancy of local (periodic) carriers

The general principle behind `FermatPosition.gcd_carrier_window_card_indep`: a carrier
that is *local*, i.e. determined by the position modulo some fixed `T`, has a bounded
discrepancy in every window.  It can never produce more than `T` excess hits between two
consecutive blocks of equal length.  Contrapositively, an observed positional excess of
`E` hits between consecutive equal blocks forces **every** local explanation to have
modulus `T ≥ E`. -/







/-! ## The competing magnitude law -/








open FermatPosition in
theorem solution(d : ℕ) (hd : 0 < d) (t : ℕ) (a : ℤ) :
    ((range (d * t)).filter (fun i : ℕ => (d : ℤ) ∣ (a + i))).card = t := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
    have hsplit : d * (t + 1) = d * t + d := by ring
    have hdisj : Disjoint (range (d * t)) ((range d).map (addLeftEmbedding (d * t))) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [mem_range] at hx
      simp only [mem_map, mem_range, addLeftEmbedding_apply] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      omega
    have hmap : (((range d).map (addLeftEmbedding (d * t))).filter
          (fun i : ℕ => (d : ℤ) ∣ (a + i))).card
        = ((range d).filter (fun i : ℕ => (d : ℤ) ∣ ((a + (d : ℤ) * t) + i))).card := by
      rw [Finset.filter_map, card_map]
      congr 1
      refine filter_congr ?_
      intro i _
      have hcomp : ((fun i : ℕ => (d : ℤ) ∣ (a + i)) ∘ (addLeftEmbedding (d * t))) i
          = ((d : ℤ) ∣ (a + ((d * t + i : ℕ) : ℤ))) := by
        simp [Function.comp, addLeftEmbedding_apply]
      rw [hcomp]
      have harg : (a + ((d * t + i : ℕ) : ℤ)) = ((a + (d : ℤ) * t) + i) := by push_cast; ring
      rw [harg]
    rw [hsplit, Finset.range_add, filter_union,
      card_union_of_disjoint (hdisj.mono (filter_subset _ _) (filter_subset _ _)), ih, hmap,
      dvd_window_card_eq_one d hd]
