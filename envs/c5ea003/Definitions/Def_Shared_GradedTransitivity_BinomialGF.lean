-- Prove2me | Definitions.Def_Shared_GradedTransitivity_BinomialGF
-- name    : Shared_GradedTransitivity_BinomialGF
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:51:58.070948+00:00
-- url     : https://prove2.me/theorems/1238d6da-e501-4b62-9335-dc1513d424a1
-- title:
--   Aether Catalog definitions — Shared_GradedTransitivity_BinomialGF
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.GradedTransitivity.BinomialGF`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/GradedTransitivity/BinomialGF.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_PolynomialGrowth

/-!
# The binomial generating function and sharpness of the exponent `r+1`

The sequence `n ↦ C(n, r)` is the universal example of polynomial growth of
degree exactly `r`.  Here we compute its generating function *exactly*,

`∑_{n} C(n,r) qⁿ = q^r / (1-q)^{r+1}`,

purely from the Pascal recurrence, and we deduce that the exponent `r+1` in
`Shared.GradedTransitivity.PolynomialGrowth` cannot be lowered: for this
sequence `(1-q)^r ∑ C(n,r) qⁿ` is *not* a polynomial.

## Main results

* `sdiff_choose` : Pascal's rule as a statement about forward differences.
* `binomial_generating_function` : `(1-X)^{r+1} ∑ C(n,r) Xⁿ = X^r`.
* `binomial_denominator_sharp` : the exponent `r+1` is optimal.
-/

namespace GradedTransitivity

open Polynomial

/-- The sequence `n ↦ C(n, r)` viewed with rational values. -/
def chooseSeq (r : ℕ) : ℕ → ℚ := fun n => (n.choose r : ℚ)









end GradedTransitivity


