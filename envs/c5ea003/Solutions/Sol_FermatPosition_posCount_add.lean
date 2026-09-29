-- Prove2me | solution 1 for FermatPosition.posCount_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:27:59.510417+00:00
-- url     : https://prove2.me/submissions/c6555910-4a54-4e85-bde3-c86661a9314c

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








open FermatPosition in
theorem solution(P : ℤ → Prop) [DecidablePred P] (a : ℤ) (L₁ L₂ : ℕ) :
    posCount P a (L₁ + L₂) = posCount P a L₁ + posCount P (a + L₁) L₂ := by
  classical
  unfold posCount
  have hdisj : Disjoint (range L₁) ((range L₂).map (addLeftEmbedding L₁)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_range] at hx
    simp only [mem_map, mem_range, addLeftEmbedding_apply] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    omega
  have hmap : (((range L₂).map (addLeftEmbedding L₁)).filter
        (fun i : ℕ => P (a + (i : ℤ)))).card
      = ((range L₂).filter (fun i : ℕ => P ((a + (L₁ : ℤ)) + (i : ℤ)))).card := by
    rw [Finset.filter_map, card_map]
    congr 1
    refine filter_congr ?_
    intro i _
    have hcomp : ((fun i : ℕ => P (a + (i : ℤ))) ∘ (addLeftEmbedding L₁)) i
        = P (a + ((L₁ + i : ℕ) : ℤ)) := by
      simp [Function.comp, addLeftEmbedding_apply]
    rw [hcomp]
    have harg : (a + ((L₁ + i : ℕ) : ℤ)) = ((a + (L₁ : ℤ)) + (i : ℤ)) := by push_cast; ring
    rw [harg]
  rw [Finset.range_add, filter_union,
    card_union_of_disjoint (hdisj.mono (filter_subset _ _) (filter_subset _ _)), hmap]
