-- Prove2me | Theorems.Thm_ZOGlobalLB_Supplement_theorem_A_7
-- name    : ZOGlobalLB.Supplement.theorem_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:53:26.474104+00:00
-- url     : https://prove2.me/theorems/491feae8-414b-4c0c-aea3-5dd41a77ecb2
-- title:
--   Theorem A.7 — binary information contraction
-- statement:
--   Let $P_{XY}$ be a joint probability law, let $Q=P_X\otimes P_Y$ be the product of its marginals, and let $E\subseteq\mathcal X\times\mathcal Y$ be measurable. Set $p=P_{XY}(E)$ and assume $q=Q(E)\in(0,1)$. Then
--
--   $$
--   I(X;Y)=D_{\mathrm{KL}}(P_{XY}\Vert Q)
--   \ge D_{\mathrm{KL}}(\operatorname{Ber}(p)\Vert\operatorname{Ber}(q))
--   \ge p\log(1/q)-\log 2.
--   $$
--
--   The first inequality is binary data processing for the event indicator; logarithms are natural.
--
--   Differences from the source:
--   - encoding: random elements $X,Y$ and their joint law → the two coordinate projections on the probability space carrying $P_{XY}$; reason: their joint and marginal laws are definitionally the same measures
--   - encoding: possibly infinite relative entropy followed by finite Bernoulli terms → the first two divergences in $[0,\infty]$ (coerced to extended reals for comparison) and the last inequality in $\mathbb R$; reason: preserves $+\infty$ while $q\in(0,1)$ makes the Bernoulli expression finite
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem A.7, p.36

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

open MeasureTheory ProbabilityTheory
open scoped ENNReal EReal

universe u v

namespace ZOGlobalLB

namespace Supplement

/-- **Theorem A.7 (Binary information contraction).** Xia, Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*, arXiv:2610.19652,
Theorem A.7, p.36.

For a joint probability law `PXY`, its product of marginals `Q`, and a measurable event `E`
with `q = Q(E)` strictly between zero and one, mutual information equals
`D_KL(PXY ‖ Q)`, which is at least the Bernoulli divergence of the event probabilities, and
that divergence is at least `p log(1/q) - log 2`.

**Formalization Note.** Mutual information and the first two divergence terms retain `+∞` in
`ℝ≥0∞`. The final Bernoulli quantities are finite real numbers because `q ∈ (0,1)`. All logarithms
are natural. The random pair is represented by the identity coordinates on the joint-law space. -/
theorem theorem_A_7 (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
    (PXY : Measure (X × Y)) [IsProbabilityMeasure PXY]
    (E : Set (X × Y)) (hE : MeasurableSet E) :
    let Q := (PXY.map Prod.fst).prod (PXY.map Prod.snd)
    let p := (PXY E).toReal
    let q := (Q E).toReal
    0 < q → q < 1 →
      (ThompsonTutorial.InfoRatio.mutualInfo PXY Prod.fst Prod.snd : EReal) =
          (InformationTheory.klDiv PXY Q : EReal) ∧
      (ENNReal.ofReal (RegretBandits.Stochastic.klBern p q) : EReal) ≤
          (InformationTheory.klDiv PXY Q : EReal) ∧
      p * Real.log (1 / q) - Real.log 2 ≤ RegretBandits.Stochastic.klBern p q := by sorry

end Supplement

end ZOGlobalLB
