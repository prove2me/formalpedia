-- Prove2me | solution 1 for FermatPosition.window_card_eq_zmod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:08:08.46523+00:00
-- url     : https://prove2.me/submissions/a1f5f6cb-3f28-47a5-897f-14adfcdf38ae

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
theorem solution(T : ℕ) [NeZero T] (P : ℤ → Prop) [DecidablePred P]
    (Q : ZMod T → Prop) [DecidablePred Q] (hPQ : ∀ j : ℤ, P j ↔ Q (j : ZMod T)) (a : ℤ) :
    ((range T).filter (fun i : ℕ => P (a + (i : ℤ)))).card = (univ.filter Q).card := by
  classical
  have hval : ∀ x : ZMod T, (((x - (a : ZMod T)).val : ℤ) : ZMod T) = x - (a : ZMod T) := by
    intro x; push_cast [ZMod.natCast_val, ZMod.cast_id]; rfl
  refine Finset.card_bij' (fun (i : ℕ) _ => ((a + (i : ℤ) : ℤ) : ZMod T))
    (fun (x : ZMod T) _ => ((x - (a : ZMod T)).val)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    simpa [mem_filter, mem_univ] using (hPQ (a + (i : ℤ))).1 hi.2
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    refine mem_filter.2 ⟨mem_range.2 (ZMod.val_lt _), ?_⟩
    refine (hPQ _).2 ?_
    have h2 : ((a + (((x - (a : ZMod T)).val : ℕ) : ℤ) : ℤ) : ZMod T) = x := by
      push_cast [hval x]; ring
    rw [h2]; exact hx
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    show ((((a + (i : ℤ) : ℤ) : ZMod T) - (a : ZMod T)).val) = i
    have h3 : ((a + (i : ℤ) : ℤ) : ZMod T) - (a : ZMod T) = ((i : ℕ) : ZMod T) := by
      push_cast; ring
    rw [h3, ZMod.val_natCast_of_lt hi.1]
  · intro x hx
    show ((a + (((x - (a : ZMod T)).val : ℕ) : ℤ) : ℤ) : ZMod T) = x
    push_cast [hval x]; ring
