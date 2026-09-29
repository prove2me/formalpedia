-- Prove2me | solution 1 for FermatPosition.gcd_carrier_window_card_indep
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:27:58.697874+00:00
-- url     : https://prove2.me/submissions/fc78c41c-106f-4f76-864f-b21e6ac175f1

-- Sol generated from NumberTheory/FermatPositionGeometry.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionGeometry
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


/-- Window counts of a `ZMod T`-periodic position predicate do not depend on where the
window starts: exact positional equidistribution. -/
theorem window_card_indep_of_start (T : ℕ) [NeZero T] (P : ℤ → Prop) [DecidablePred P]
    (Q : ZMod T → Prop) [DecidablePred Q] (hPQ : ∀ j : ℤ, P j ↔ Q (j : ZMod T)) (a a' : ℤ) :
    ((range T).filter (fun i : ℕ => P (a + (i : ℤ)))).card
      = ((range T).filter (fun i : ℕ => P (a' + (i : ℤ)))).card := by
  rw [window_card_eq_zmod T P Q hPQ a, window_card_eq_zmod T P Q hPQ a']

/-! ## No single prime can create a small-`j` excess -/






/-! ## The gcd carrier is itself positionally uniform -/



/-! ## Confound analysis: magnitude cells are position intervals -/





open FermatPosition in
theorem solution(b N : ℤ) (hv : sieveVal b N 0 ≠ 0) (a a' : ℤ) :
    ((range (sieveVal b N 0).natAbs).filter
        (fun i : ℕ => 1 < Int.gcd (a + (i : ℤ)) (sieveVal b N 0))).card
      = ((range (sieveVal b N 0).natAbs).filter
        (fun i : ℕ => 1 < Int.gcd (a' + (i : ℤ)) (sieveVal b N 0))).card := by
  classical
  set v₀ := sieveVal b N 0 with hv₀
  haveI : NeZero v₀.natAbs := ⟨Int.natAbs_ne_zero.2 hv⟩
  refine window_card_indep_of_start v₀.natAbs (fun j : ℤ => 1 < Int.gcd j v₀)
    (fun x : ZMod v₀.natAbs => 1 < Int.gcd ((x.val : ℤ)) v₀) ?_ a a'
  intro j
  have hmod : ((j : ZMod v₀.natAbs).val : ℤ) % v₀ = j % v₀ := by
    have : ((j : ZMod v₀.natAbs).val : ℤ) % (v₀.natAbs : ℤ) = j % (v₀.natAbs : ℤ) := by
      have h1 : (((j : ZMod v₀.natAbs).val : ℤ) : ZMod v₀.natAbs) = (j : ZMod v₀.natAbs) := by
        push_cast [ZMod.natCast_val, ZMod.cast_id]; rfl
      have := (ZMod.intCast_eq_intCast_iff' _ _ _).1 h1
      simpa using this
    rcases Int.natAbs_eq v₀ with h | h
    · rw [← h] at this; exact this
    · have hneg : ((v₀.natAbs : ℤ)) = -v₀ := by omega
      rw [hneg] at this
      simpa [Int.emod_neg] using this
  have hg : ∀ x y : ℤ, x % v₀ = y % v₀ → Int.gcd x v₀ = Int.gcd y v₀ := by
    intro x y hxy
    have hx : Int.gcd x v₀ = Int.gcd (x % v₀) v₀ := (Int.gcd_emod x v₀).symm
    have hy : Int.gcd y v₀ = Int.gcd (y % v₀) v₀ := (Int.gcd_emod y v₀).symm
    rw [hx, hy, hxy]
  simp only [hg _ _ hmod.symm]
