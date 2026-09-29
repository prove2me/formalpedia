-- Prove2me | Definitions.Def_Shared_GradedTransitivity_PolyClassification
-- name    : Shared_GradedTransitivity_PolyClassification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:53:50.877401+00:00
-- url     : https://prove2.me/theorems/05495add-1e8a-4ae8-8793-fc28185ecf67
-- title:
--   Aether Catalog definitions — Shared_GradedTransitivity_PolyClassification
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.GradedTransitivity.PolyClassification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/GradedTransitivity/PolyClassification.lean by skeleton subtraction
import Mathlib

/-!
# Denominator `(1-q)^{r+1}` ⟺ eventually polynomial of degree `≤ r`

`PolynomialGrowth` shows one implication and `Newton` produces, from the
vanishing of `Δ^{r+1}`, an explicit binomial expansion.  Here we convert that
binomial expansion into an honest polynomial, using the falling factorial
`descPochhammer`, and obtain the exact classification

`(1-q)^{r+1} · ∑ a n qⁿ` is a polynomial ⟺ `a` is eventually given by a
polynomial of degree `≤ r`.

## Main results

* `binomPoly_eval` : `C(n-N, j)` is a polynomial function of `n` of degree `j`.
* `exists_polynomial_of_sdiff_iter_eventuallyZero` : vanishing of `Δ^{r+1}`
  produces the polynomial.
* `gen_poly_iff_eventually_polynomial` : the classification.
-/

namespace GradedTransitivity

open Polynomial

/-- The polynomial of degree `j` interpolating `n ↦ C(n-N, j)`. -/
noncomputable def binomPoly (N j : ℕ) : ℚ[X] :=
  C (1 / (j.factorial : ℚ)) * (descPochhammer ℚ j).comp (X - C (N : ℚ))





end GradedTransitivity


