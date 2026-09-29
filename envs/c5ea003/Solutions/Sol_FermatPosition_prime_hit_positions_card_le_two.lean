-- Prove2me | solution 1 for FermatPosition.prime_hit_positions_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:33:26.190877+00:00
-- url     : https://prove2.me/submissions/87372003-096b-43ca-8d1a-a06ef5f52fe7

-- Sol generated from NumberTheory/FermatPositionGeometry.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionGeometry
/-
# Positional geometry of the Fermat / quadratic-sieve polynomial

For a modulus `N` and a base `b` (in practice `b = ⌈√N⌉`) the *sieve polynomial* is

    `sieveVal b N j = (b + j)^2 - N`,

and a *hit* at position `j` is a position at which `sieveVal b N j` is `B`-smooth.
Empirically (paper 228 / exp 578, replicated here in `evidence/`) hits cluster toward
small `j`.  The question is whether this is *only* the magnitude decay of `sieveVal`
(the polynomial is increasing in `j`) or whether there is genuine *positional*
arithmetic structure.

This file isolates the arithmetic, magnitude-free content of the question.

Main results.

* `sieveVal_sub_base` / `sieveVal_strictMonoOn` : the exact expansion
  `v(j) - v(0) = j (j + 2b)` and strict monotonicity in `j ≥ 0`.
* `gcd_position_law` : `gcd (j, v(j)) = gcd (j, v(0))` — the **position–gcd law**.
  Position `j` and the *fixed* integer `v(0)` determine the guaranteed common factor;
  in particular `j ∣ v(j) ↔ j ∣ v(0)`.
* `smooth_iff_cofactor_smooth` : the guaranteed factor `g = gcd (j, v(0))` may be
  divided out for free when `g < B`, so the smoothness test at position `j` only
  concerns the cofactor `v(j)/g`.  This is an *arithmetic* enrichment that is
  invisible to `|v(j)|`: a genuinely beyond-magnitude carrier.
* `window_card_eq_zmod`, `window_card_indep_of_start` : a general equidistribution
  device.  Any position predicate that factors through `ZMod T` has exactly the same
  count in every window of `T` consecutive positions.
* `prime_hit_positions_card_le_two` and `prime_window_card_indep` : for a prime `p`
  the positions with `p ∣ v(j)` form at most two residue classes mod `p` and are
  **exactly equidistributed**: no single small prime can produce a small-`j` excess.
* `gcd_carrier_window_card_indep` : the gcd-carrier of `smooth_iff_cofactor_smooth`
  is *itself* exactly equidistributed in position (period `|v(0)|`).  Hence the
  carrier is real but **cannot** be the source of a small-`j` excess.
* `sizeClass_ordConnected` and `cell_collapse` : the confound-analysis theorems.
  Because `v` is strictly monotone, every magnitude class is an *interval of
  positions*, and a magnitude cell of width a factor `2` confines positions to a
  window `j₂ ≤ 2 j₁ + 2 + j₁²/b`.  Stratifying by `|v|` therefore cannot decorrelate
  position from magnitude within a single `N`.
-/

open FermatPosition

open Finset

/-! ## The sieve polynomial -/





/-! ## The position–gcd law -/



/-! ## The gcd carrier: a beyond-magnitude smoothness enrichment -/



/-! ## Equidistribution device -/



/-! ## No single prime can create a small-`j` excess -/






/-! ## The gcd carrier is itself positionally uniform -/



/-! ## Confound analysis: magnitude cells are position intervals -/





open FermatPosition in
theorem solution(p : ℕ) [Fact p.Prime] (b N : ZMod p) :
    (univ.filter (fun x : ZMod p => (b + x) ^ 2 = N)).card ≤ 2 := by
  classical
  by_cases h : ∃ r : ZMod p, (b + r) ^ 2 = N
  · obtain ⟨r, hr⟩ := h
    have hsub : (univ.filter (fun x : ZMod p => (b + x) ^ 2 = N)) ⊆ {r, -r - 2 * b} := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have hz : (x - r) * (x + r + 2 * b) = 0 := by
        have : (b + x) ^ 2 - (b + r) ^ 2 = 0 := by rw [hx, hr]; ring
        linear_combination this
      rcases mul_eq_zero.1 hz with h1 | h2
      · exact mem_insert.2 (Or.inl (sub_eq_zero.1 h1))
      · refine mem_insert.2 (Or.inr (mem_singleton.2 ?_))
        linear_combination h2
    calc (univ.filter (fun x : ZMod p => (b + x) ^ 2 = N)).card
        ≤ ({r, -r - 2 * b} : Finset (ZMod p)).card := card_le_card hsub
      _ ≤ 2 := (card_insert_le _ _).trans (by simp)
  · push_neg at h
    have : (univ.filter (fun x : ZMod p => (b + x) ^ 2 = N)) = ∅ := by
      refine filter_eq_empty_iff.2 ?_
      intro x _; exact h x
    simp [this]
