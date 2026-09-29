-- Prove2me | solution 1 for FermatPosition.prime_window_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:38:13.223298+00:00
-- url     : https://prove2.me/submissions/ebedbf68-982f-4bb0-bb03-df769e1978ea

-- Sol generated from NumberTheory/FermatPositionGeometry.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionGeometry
import Theorems.Thm_FermatPosition_prime_hit_positions_card_le_two
import Theorems.Thm_FermatPosition_window_card_eq_zmod
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
theorem solution(p : ℕ) [hp : Fact p.Prime] (b N a : ℤ) :
    ((range p).filter (fun i : ℕ => (p : ℤ) ∣ sieveVal b N (a + (i : ℤ)))).card ≤ 2 := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h := window_card_eq_zmod p (fun j => (p : ℤ) ∣ sieveVal b N j)
    (fun x : ZMod p => ((b : ZMod p) + x) ^ 2 = (N : ZMod p)) ?_ a
  · rw [h]; exact prime_hit_positions_card_le_two p _ _
  · intro j
    constructor
    · intro hdvd
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
      have h2 : (((b + j) ^ 2 - N : ℤ) : ZMod p) = 0 := by simpa [sieveVal] using this
      push_cast at h2
      linear_combination h2
    · intro hq
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_
      have : (((b + j) ^ 2 - N : ℤ) : ZMod p) = 0 := by push_cast; linear_combination hq
      simpa [sieveVal] using this
