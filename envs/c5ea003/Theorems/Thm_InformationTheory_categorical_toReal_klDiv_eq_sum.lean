-- Prove2me | Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
-- name    : InformationTheory.categorical_toReal_klDiv_eq_sum
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T00:05:22.889093+00:00
-- url     : https://prove2.me/theorems/f4181a0f-b68b-4ce4-89cc-3f23990ed8be
-- title:
--   KL divergence of finite categorical distributions
-- statement:
--   Let $q=(q_a)_{a\in[k]}$ and $p=(p_a)_{a\in[k]}$ be categorical probability distributions on a nonempty finite set, with $q$ absolutely continuous with respect to $p$. Then
--
--   $$
--   D(q\,\|\,p)=\sum_{a\in[k]}q_a\log\frac{q_a}{p_a}.
--   $$
--
--   The usual convention for a zero $q_a$ is implemented by Lean's real logarithm and multiplication by $q_a$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 470 (PDF p. 479), Eq. (36.9) and the KL terms in Lemma 36.7; standard categorical expansion of relative entropy.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

theorem InformationTheory.categorical_toReal_klDiv_eq_sum {k : ℕ} [NeZero k]
    (q p : Measure (Fin k)) [IsProbabilityMeasure q] [IsProbabilityMeasure p]
    (hqp : q ≪ p) :
    (klDiv q p).toReal =
      ∑ a, q.real {a} * Real.log (q.real {a} / p.real {a}) := by
  sorry
