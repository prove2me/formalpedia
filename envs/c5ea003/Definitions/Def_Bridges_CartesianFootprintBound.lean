-- Prove2me | Definitions.Def_Bridges_CartesianFootprintBound
-- name    : Bridges_CartesianFootprintBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:48.883738+00:00
-- url     : https://prove2.me/theorems/c3ebfa58-c963-434d-99ce-e74b9f3f94e1
-- title:
--   Aether Catalog definitions — Bridges_CartesianFootprintBound
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CartesianFootprintBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CartesianFootprintBound.lean by skeleton subtraction
import Mathlib
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

namespace CartesianFootprint

/-! ## Definitions -/

/-- The finite Cartesian product ∏ᵢ Sᵢ as a `Finset` of functions `Fin n → F`. -/
def grid {n : ℕ} {F : Type*} [DecidableEq F] (S : Fin n → Finset F) : Finset (Fin n → F) :=
  Fintype.piFinset S

/-- A polynomial is **reduced on grid S** if every monomial in its support has
    each coordinate exponent strictly less than the corresponding set cardinality.
    This is the support-based surrogate for reduction modulo the coordinate
    vanishing ideal ⟨∏_{a∈Sᵢ}(Xᵢ-a) : i⟩. -/
def IsReducedOnGrid {n : ℕ} {F : Type*} [CommSemiring F]
    (S : Fin n → Finset F) (f : MvPolynomial (Fin n) F) : Prop :=
  ∀ i m, m ∈ f.support → m i < (S i).card


/-! ## Grid membership -/



/-! ## Existence of nonzero evaluation (restricted-grid Nullstellensatz) -/

/-
**Restricted-grid Combinatorial Nullstellensatz.**
    A nonzero polynomial that is reduced on the grid ∏ᵢ Sᵢ
    (i.e., each monomial exponent in variable i is < |Sᵢ|)
    has at least one nonzero evaluation on the grid.
-/

/-! ## Main theorem: Quantitative footprint bound -/

/-
**Anisotropic Footprint Bound (Alon–Füredi on arbitrary Cartesian products).**

    Let F be a field, Sᵢ ⊆ F finite nonempty sets, and f ∈ F[X₁,...,Xₙ] nonzero.
    If for each variable i, every monomial of f has exponent ≤ eᵢ < |Sᵢ| in Xᵢ,
    then the number of grid points where f ≠ 0 is at least ∏ᵢ (|Sᵢ| - eᵢ).
-/


/-! ## Corollaries -/

/-
Footprint bound using `degreeOf` instead of explicit exponent bounds.
-/

/-
**Uniform grid specialization.**
    When all Sᵢ = S (same set), and all degree bounds are d,
    the number of nonzeros is at least (|S| - d)ⁿ.
    This recovers the classical footprint bound on Fqⁿ.
-/

end CartesianFootprint


