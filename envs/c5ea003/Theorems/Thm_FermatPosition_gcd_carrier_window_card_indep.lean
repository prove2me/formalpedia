-- Prove2me | Theorems.Thm_FermatPosition_gcd_carrier_window_card_indep
-- name    : FermatPosition.gcd_carrier_window_card_indep
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:28:53.875761+00:00
-- url     : https://prove2.me/theorems/b036c2c7-66fa-490e-b948-1f87acf871e3
-- title:
--   The carrier cannot explain a small-`j` excess.
-- statement:
--   **The carrier cannot explain a small-`j` excess.**  The set of positions carrying a
--   nontrivial guaranteed common factor `gcd (j, v(0)) > 1` has exactly the same count in
--   every window of `|v(0)|` consecutive positions.  Combined with
--   `smooth_iff_cofactor_smooth` this says: the gcd carrier is a real, magnitude-free
--   smoothness enrichment, but it is *positionally uniform*, so it is not the source of the
--   observed clustering of hits at small `j`.
--
--   ```lean
--   theorem FermatPosition.gcd_carrier_window_card_indep(b N : ℤ) (hv : sieveVal b N 0 ≠ 0) (a a' : ℤ) :
--       ((range (sieveVal b N 0).natAbs).filter
--           (fun i : ℕ => 1 < Int.gcd (a + (i : ℤ)) (sieveVal b N 0))).card
--         = ((range (sieveVal b N 0).natAbs).filter
--           (fun i : ℕ => 1 < Int.gcd (a' + (i : ℤ)) (sieveVal b N 0))).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/FermatPositionGeometry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/FermatPositionGeometry.lean#L298

-- Thm stub generated from NumberTheory/FermatPositionGeometry.lean
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

theorem FermatPosition.gcd_carrier_window_card_indep(b N : ℤ) (hv : sieveVal b N 0 ≠ 0) (a a' : ℤ) :
    ((range (sieveVal b N 0).natAbs).filter
        (fun i : ℕ => 1 < Int.gcd (a + (i : ℤ)) (sieveVal b N 0))).card
      = ((range (sieveVal b N 0).natAbs).filter
        (fun i : ℕ => 1 < Int.gcd (a' + (i : ℤ)) (sieveVal b N 0))).card := by sorry
