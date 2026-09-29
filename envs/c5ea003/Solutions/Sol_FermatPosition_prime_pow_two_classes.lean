-- Prove2me | solution 1 for FermatPosition.prime_pow_two_classes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:33:26.741246+00:00
-- url     : https://prove2.me/submissions/c381d54c-5113-4ee3-a81b-33117875c6f6

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
theorem solution{p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {b N x y : ℤ}
    (hk : 1 ≤ k) (hN : ¬ ((p : ℤ) ∣ N))
    (hx : ((p : ℤ) ^ k) ∣ sieveVal b N x) (hy : ((p : ℤ) ^ k) ∣ sieveVal b N y) :
    ((p : ℤ) ^ k) ∣ (x - y) ∨ ((p : ℤ) ^ k) ∣ (x + y + 2 * b) := by
  have hprod : ((p : ℤ) ^ k) ∣ (x - y) * (x + y + 2 * b) := by
    have hid : (x - y) * (x + y + 2 * b) = sieveVal b N x - sieveVal b N y := by
      simp only [sieveVal]; ring
    rw [hid]; exact dvd_sub hx hy
  have hp1 : (p : ℤ) ∣ sieveVal b N x := dvd_trans (dvd_pow_self _ (by omega)) hx
  have hpbx : ¬ ((p : ℤ) ∣ (b + x)) := by
    intro hd
    apply hN
    have h2 : (p : ℤ) ∣ (b + x) ^ 2 := Dvd.dvd.pow hd (by norm_num)
    have h3 : (p : ℤ) ∣ ((b + x) ^ 2 - sieveVal b N x) := dvd_sub h2 hp1
    simpa [sieveVal] using h3
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsum : (x - y) + (x + y + 2 * b) = 2 * (b + x) := by ring
  have hp2 : ¬ ((p : ℤ) ∣ 2) := by
    intro hd
    have hle := Int.le_of_dvd (by norm_num) hd
    have h2 := hp.two_le
    exact hodd (by omega)
  by_cases h1 : (p : ℤ) ∣ (x - y)
  · left
    have hnd : ¬ ((p : ℤ) ∣ (x + y + 2 * b)) := by
      intro hd
      have hs : (p : ℤ) ∣ 2 * (b + x) := by rw [← hsum]; exact dvd_add h1 hd
      rcases hpprime.dvd_mul.1 hs with h | h
      · exact hp2 h
      · exact hpbx h
    exact hpprime.pow_dvd_of_dvd_mul_left k hnd (by rwa [mul_comm] at hprod)
  · right
    exact hpprime.pow_dvd_of_dvd_mul_left k h1 hprod
