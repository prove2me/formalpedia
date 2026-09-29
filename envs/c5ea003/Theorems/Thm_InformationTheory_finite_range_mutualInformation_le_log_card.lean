-- Prove2me | Theorems.Thm_InformationTheory_finite_range_mutualInformation_le_log_card
-- name    : InformationTheory.finite_range_mutualInformation_le_log_card
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:55:16.025075+00:00
-- url     : https://prove2.me/theorems/2c4516ea-ebcf-4ba0-aec8-84358b416c2c
-- title:
--   Mutual information with a k-valued variable is at most $\log k$
-- statement:
--   Let $X$ and $Y$ be random variables on a common probability space, where $Y$ takes values in a nonempty set of $k$ elements. Their mutual information, defined as relative entropy of the joint law from the product of the marginals, obeys
--
--   $$
--   I(X;Y)
--   =D\!\left(P_{(X,Y)}\,\middle\|\,P_X\otimes P_Y\right)
--   \le H(Y)\le \log k.
--   $$
--
--   No finiteness assumption is imposed on the range of $X$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 471 (PDF p. 480), proof of Theorem 36.5: total information about the k-valued optimal action is at most the log k diameter of negentropy.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory ProbabilityTheory InformationTheory

theorem InformationTheory.finite_range_mutualInformation_le_log_card
    {Omega Alpha : Type} {mOmega : MeasurableSpace Omega}
    {mAlpha : MeasurableSpace Alpha} {k : ℕ} [NeZero k]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → Alpha) (g : Omega → Fin k)
    (hf : Measurable f) (hg : Measurable g) :
    (klDiv (Measure.map (fun x ↦ (f x, g x)) mu)
      ((Measure.map f mu).prod (Measure.map g mu))).toReal ≤ Real.log k := by
  sorry
