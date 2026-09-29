-- Prove2me | Theorems.Thm_CartesianFootprint_exists_eval_ne_zero
-- name    : CartesianFootprint.exists_eval_ne_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:38:39.078484+00:00
-- url     : https://prove2.me/theorems/4ab4acde-0136-4eaa-979a-46a02d16b326
-- title:
--   Exists eval ne zero
-- statement:
--   Formal statement of `CartesianFootprint.exists_eval_ne_zero` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CartesianFootprint.exists_eval_ne_zero{n : ℕ} {F : Type*} [Field F]
--       (S : Fin n → Finset F)
--       (hS : ∀ i, (S i).Nonempty)
--       (f : MvPolynomial (Fin n) F)
--       (hf : f ≠ 0)
--       (hred : IsReducedOnGrid S f) :
--       ∃ x ∈ grid (F := F) S, MvPolynomial.eval x f ≠ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CartesianFootprintBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CartesianFootprintBound.lean#L79

-- Thm stub generated from Bridges/CartesianFootprintBound.lean
import Mathlib
import Definitions.Def_Bridges_CartesianFootprintBound
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Anisotropic Footprint Bound on Finite Cartesian Products

This file proves the Alon–Füredi / footprint bound for multivariate polynomials
on arbitrary finite Cartesian products over a field:

> Given finite nonempty sets S₁, ..., Sₙ ⊆ F and a nonzero polynomial f ∈ F[X₁,...,Xₙ]
> with deg_{Xᵢ}(f) ≤ eᵢ < |Sᵢ|, the number of points in ∏ᵢ Sᵢ where f does not
> vanish is at least ∏ᵢ (|Sᵢ| - eᵢ).

This upgrades the classical footprint bound from uniform coordinate alphabets (F_q^n)
to **anisotropic finite geometries** — the natural setting for coding theory with
unequal symbol sets and restricted interpolation.

## Main results

- `CartesianFootprint.exists_eval_ne_zero`: A nonzero reduced polynomial has at least
  one nonzero on the grid (restricted-grid combinatorial Nullstellensatz).
- `CartesianFootprint.footprint_bound`: The full quantitative lower bound on the
  number of nonzeros.

## References

- N. Alon, "Combinatorial Nullstellensatz", Combin. Probab. Comput. 8 (1999)
- S. Ball, O. Serra, "Punctured combinatorial Nullstellensätze", Combinatorica 29 (2009)
- H. López, C. Rentería-Márquez, R. Villarreal, "Affine Cartesian codes", Des. Codes Cryptogr. 71 (2014)
-/

open MvPolynomial Polynomial Finset BigOperators Classical

noncomputable section

open CartesianFootprint

/-! ## Definitions -/




/-! ## Grid membership -/



/-! ## Existence of nonzero evaluation (restricted-grid Nullstellensatz) -/

/-
**Restricted-grid Combinatorial Nullstellensatz.**
    A nonzero polynomial that is reduced on the grid ∏ᵢ Sᵢ
    (i.e., each monomial exponent in variable i is < |Sᵢ|)
    has at least one nonzero evaluation on the grid.
-/

theorem CartesianFootprint.exists_eval_ne_zero{n : ℕ} {F : Type*} [Field F]
    (S : Fin n → Finset F)
    (hS : ∀ i, (S i).Nonempty)
    (f : MvPolynomial (Fin n) F)
    (hf : f ≠ 0)
    (hred : IsReducedOnGrid S f) :
    ∃ x ∈ grid (F := F) S, MvPolynomial.eval x f ≠ 0 := by sorry
