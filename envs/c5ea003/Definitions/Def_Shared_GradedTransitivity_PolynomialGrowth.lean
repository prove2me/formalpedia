-- Prove2me | Definitions.Def_Shared_GradedTransitivity_PolynomialGrowth
-- name    : Shared_GradedTransitivity_PolynomialGrowth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:51:10.772026+00:00
-- url     : https://prove2.me/theorems/61977755-ee22-4d66-86fb-a88ca1c3f10c
-- title:
--   Aether Catalog definitions — Shared_GradedTransitivity_PolynomialGrowth
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.GradedTransitivity.PolynomialGrowth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/GradedTransitivity/PolynomialGrowth.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference

/-!
# Eventually polynomial sequences have denominator `(1-q)^{r+1}`

The discrete derivative `p ↦ p(X+1) - p` lowers the degree of a polynomial.
Iterating it `r+1` times therefore annihilates every polynomial of degree `≤ r`,
and combined with `Shared.GradedTransitivity.FiniteDifference` this shows that a
sequence which is *eventually* given by a polynomial of degree `≤ r` has
generating function with denominator `(1-q)^{r+1}`.

## Main results

* `pdiff_natDegree_le` : the discrete derivative drops the degree.
* `sdiff_iter_eval_eq_zero` : `Δ^{r+1}` kills degree `≤ r` polynomial sequences.
* `exists_poly_of_eventually_polynomial` : the rationality statement.
-/

namespace GradedTransitivity

open Polynomial

/-- The *discrete derivative* of a polynomial, `(Δp)(X) = p(X+1) - p(X)`. -/
noncomputable def pdiff (p : ℚ[X]) : ℚ[X] := p.comp (X + C 1) - p








end GradedTransitivity


