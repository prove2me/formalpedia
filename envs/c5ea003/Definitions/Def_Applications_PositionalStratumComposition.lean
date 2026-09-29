-- Prove2me | Definitions.Def_Applications_PositionalStratumComposition
-- name    : Applications_PositionalStratumComposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:38.867569+00:00
-- url     : https://prove2.me/theorems/eb44b5de-7d19-466b-9200-949d17ed625c
-- title:
--   Aether Catalog definitions — Applications_PositionalStratumComposition
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PositionalStratumComposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PositionalStratumComposition.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_PositionalStratumCertifiedLaw
/-
# Composition of positional strata : the pathwise product is lost, an inequality survives

Stacking two independent stratifications multiplies the bookings: the composite retained
fraction is `μ₁μ₂` and the composite capture probability is `P₁P₂` (the target must survive
*both* filters).  Does the certified value multiply as well?

* `certifiedValue_not_multiplicative` : **no.**  The pathwise product fails already at
  `(μ₁,P₁) = (1/2, 9/10)`, `(μ₂,P₂) = (1/2, 1)`, where the composite value is `10/3` while
  the product of the factor values is `4`.
* `certifiedValue_submultiplicative` : **but the inequality survives**, unconditionally on
  the admissible box:  `S(μ₁μ₂, P₁P₂) ≤ S(μ₁,P₁) · S(μ₂,P₂)`.  So a composed guarantee may
  be *reported* as a product — it is then conservative, never optimistic.

The proof rests on an exact coupling identity (`coupling_slack_identity`): the reciprocal
value `D(μ,P) = μP + (1-μ)(1-P)` is the agreement probability of two independent Bernoulli
draws, and the event "`the two products agree`" contains the event "`both coordinates
agree`".  The slack is the probability of the difference of those two events, written out
explicitly as a sum of four nonnegative products.
-/

namespace PositionalStratum

noncomputable section

/-- The reciprocal of the certified value: the *agreement probability* of the locus. -/
def agreement (mu P : ℝ) : ℝ := mu * P + (1 - mu) * (1 - P)







end

end PositionalStratum


