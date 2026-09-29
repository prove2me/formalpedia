-- Prove2me | solution 1 for PositionalStratum.certifiedValue_strict_submultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:59:11.848524+00:00
-- url     : https://prove2.me/submissions/071231b7-e105-40a0-8fff-a255afe80836

-- Sol generated from Applications/PositionalStratumComposition.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumCertifiedLaw
import Definitions.Def_Applications_PositionalStratumComposition
import Theorems.Thm_PositionalStratum_denom_pos
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


lemma certifiedValue_eq_inv_agreement (mu P : ℝ) :
    certifiedValue mu P = 1 / agreement mu P := by
  rw [certifiedValue, agreement]

lemma agreement_pos {mu P : ℝ} (hmu : 0 < mu) (hmu1 : mu < 1) (hP : 0 < P) (hP1 : P < 1) :
    0 < agreement mu P := denom_pos hmu hmu1 hP hP1

/-- **Coupling slack identity.**  The composite agreement probability exceeds the product of
the factor agreement probabilities by exactly the probability of the configurations in
which the two *products* agree while some coordinate pair disagrees. -/
theorem coupling_slack_identity (a b c d : ℝ) :
    agreement (a * c) (b * d) - agreement a b * agreement c d
      = (1 - a) * b * (1 - d) + a * (1 - b) * (1 - c)
        + (1 - a) * (1 - b) * ((1 - c) * d + c * (1 - d)) := by
  rw [agreement, agreement, agreement]
  ring






open PositionalStratum in
theorem solution{a b c d : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hc1 : c < 1) (hd : 0 < d) (hd1 : d < 1) :
    certifiedValue (a * c) (b * d) < certifiedValue a b * certifiedValue c d := by
  have hac : 0 < a * c := mul_pos ha hc
  have hac1 : a * c < 1 := by nlinarith
  have hbd : 0 < b * d := mul_pos hb hd
  have hbd1 : b * d < 1 := by nlinarith
  have hD1 : 0 < agreement a b := agreement_pos ha ha1 hb hb1
  have hD2 : 0 < agreement c d := agreement_pos hc hc1 hd hd1
  have hD : 0 < agreement (a * c) (b * d) := agreement_pos hac hac1 hbd hbd1
  have hslack : agreement a b * agreement c d < agreement (a * c) (b * d) := by
    have hid := coupling_slack_identity a b c d
    have h1 : 0 < (1 - a) * b * (1 - d) :=
      mul_pos (mul_pos (by linarith) hb) (by linarith)
    have h2 : 0 ≤ a * (1 - b) * (1 - c) :=
      mul_nonneg (mul_nonneg ha.le (by linarith)) (by linarith)
    have h3 : 0 ≤ (1 - a) * (1 - b) * ((1 - c) * d + c * (1 - d)) := by
      have hcd1 : 0 ≤ (1 - c) * d := mul_nonneg (by linarith) hd.le
      have hcd2 : 0 ≤ c * (1 - d) := mul_nonneg hc.le (by linarith)
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith [hid, h1, h2, h3]
  rw [certifiedValue_eq_inv_agreement, certifiedValue_eq_inv_agreement,
    certifiedValue_eq_inv_agreement, div_mul_div_comm, one_mul,
    div_lt_div_iff₀ hD (mul_pos hD1 hD2)]
  linarith [hslack]
