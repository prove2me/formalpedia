-- Prove2me | Theorems.Thm_PositionalStratum_certifiedValue_strict_submultiplicative
-- name    : PositionalStratum.certifiedValue_strict_submultiplicative
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:00:12.126797+00:00
-- url     : https://prove2.me/theorems/d0b89575-61ea-428f-b833-a671b61c0dca
-- title:
--   Strict submultiplicativity.
-- statement:
--   **Strict submultiplicativity.**  On the open admissible box the composite agreement
--   probability strictly exceeds the product of the factor agreements, so the certified value
--   of a composite stratum is *strictly* below the product of its factors' values.
--
--   ```lean
--   theorem PositionalStratum.certifiedValue_strict_submultiplicative{a b c d : ℝ}
--       (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
--       (hc : 0 < c) (hc1 : c < 1) (hd : 0 < d) (hd1 : d < 1) :
--       certifiedValue (a * c) (b * d) < certifiedValue a b * certifiedValue c d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PositionalStratumComposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PositionalStratumComposition.lean#L46

-- Thm stub generated from Applications/PositionalStratumComposition.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumCertifiedLaw
import Definitions.Def_Applications_PositionalStratumComposition
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

open PositionalStratum

noncomputable section

theorem PositionalStratum.certifiedValue_strict_submultiplicative{a b c d : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hc1 : c < 1) (hd : 0 < d) (hd1 : d < 1) :
    certifiedValue (a * c) (b * d) < certifiedValue a b * certifiedValue c d := by sorry
