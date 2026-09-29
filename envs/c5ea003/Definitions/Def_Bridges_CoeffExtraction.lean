-- Prove2me | Definitions.Def_Bridges_CoeffExtraction
-- name    : Bridges_CoeffExtraction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:05.855115+00:00
-- url     : https://prove2.me/theorems/4f16ec51-ec67-4995-996d-8186892e52f6
-- title:
--   Aether Catalog definitions — Bridges_CoeffExtraction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CoeffExtraction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CoeffExtraction.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coefficient Extraction and the Combinatorial Nullstellensatz

This file formalizes the **coefficient extraction identity** for univariate polynomials
over a field, and derives the Combinatorial Nullstellensatz as a corollary.

## Main results

* `CoeffExtraction.lagrangeDen_ne_zero` : The Lagrange denominator is nonzero for elements
  of a Finset.
* `CoeffExtraction.gridPoly_dvd_of_roots` : The vanishing polynomial divides any polynomial that
  vanishes on the entire set.
* `CoeffExtraction.coeff_eq_sum_eval_div_lagrangeDen` : **The Univariate Coefficient Extraction
  Theorem.** For `p` with `natDegree p < |S|`:
  `p.coeff (|S| - 1) = ∑ s ∈ S, p.eval s * (lagrangeDen S s)⁻¹`
* `CoeffExtraction.exists_eval_ne_zero_of_coeff_ne_zero_univ` : **Univariate Combinatorial
  Nullstellensatz.** Nonzero top coefficient implies a nonzero evaluation in `S`.
* `CoeffExtraction.exists_eval_ne_zero_mv` : **Multivariate Combinatorial Nullstellensatz.**
  Nonzero grid evaluation existence from nonzero top monomial coefficient.

## References

* N. Alon, "Combinatorial Nullstellensatz", Combin. Probab. Comput. 8 (1999), 7–29.

## Tags

combinatorial nullstellensatz, coefficient extraction, Lagrange interpolation, polynomial method
-/


open Polynomial Finset BigOperators

namespace CoeffExtraction

variable {K : Type*} [Field K] [DecidableEq K]

/-! ## §1. Lagrange denominator -/

/-- The Lagrange denominator at `x` with respect to a set `S`:
  `lagrangeDen S x = ∏ y ∈ S.erase x, (x - y)` -/
noncomputable def lagrangeDen (S : Finset K) (x : K) : K :=
  ∏ y ∈ S.erase x, (x - y)


/-! ## §2. Grid polynomial (vanishing polynomial) -/

/-- The vanishing polynomial of a finite set `S`:
  `gridPoly S = ∏ s ∈ S, (X - C s)` -/
noncomputable def gridPoly (S : Finset K) : Polynomial K :=
  ∏ s ∈ S, (X - C s)


/-
If a polynomial vanishes on all elements of `S`, then `∏_{s ∈ S} (X - s)` divides it.
-/

/-! ## §3. Lagrange basis coefficient -/

/-
The leading coefficient of `Lagrange.basisDivisor a b` is `(a - b)⁻¹`.
-/

/-
The natDegree of `Lagrange.basisDivisor a b` is 1 when `a ≠ b`.
-/

/-
The leading coefficient of `Lagrange.basis S id s` for `s ∈ S` is
  `(lagrangeDen S s)⁻¹ = (∏_{t ∈ S.erase s} (s - t))⁻¹`.
-/

/-
The natDegree of `Lagrange.basis S id s` for `s ∈ S` is `|S| - 1`.
-/


/-! ## §4. Univariate coefficient extraction -/

/-
**Univariate Coefficient Extraction Theorem.**
For a polynomial `p` with `p.natDegree < |S|`, the coefficient of `X^{|S|-1}` equals
the weighted sum of evaluations divided by Lagrange denominators:

  `p.coeff (|S| - 1) = ∑ s ∈ S, p.eval s * (lagrangeDen S s)⁻¹`

This is the algebraic engine behind the Combinatorial Nullstellensatz.
-/

/-! ## §5. Univariate Nullstellensatz -/

/-
**Univariate Combinatorial Nullstellensatz.**
If `p` has degree `< |S|` and the coefficient of `X^{|S|-1}` is nonzero,
then `p` has a nonzero evaluation point in `S`.
-/

/-! ## §6. Multivariate definitions and Nullstellensatz -/

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The Cartesian product grid: all functions `ι → K` choosing from `S i` for each `i`. -/
noncomputable def grid (S : ι → Finset K) : Finset (ι → K) :=
  Fintype.piFinset S


/-
**Multivariate Combinatorial Nullstellensatz** (Alon's theorem).

If `f` is a multivariate polynomial over a field `K` and `S : ι → Finset K`
assigns a nonempty finite set to each variable, and if the coefficient of the
monomial `∏ i, X_i^{|S i| - 1}` in `f` is nonzero (with each variable degree
bounded by `|S i| - 1`), then there exists an evaluation point `x` in the
Cartesian product `∏ i, S i` where `f(x) ≠ 0`.

This is the key consequence of the coefficient extraction identity.
-/

end CoeffExtraction


