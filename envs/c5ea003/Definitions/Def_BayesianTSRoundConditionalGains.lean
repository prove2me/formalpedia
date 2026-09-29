-- Prove2me | Definitions.Def_BayesianTSRoundConditionalGains
-- name    : BayesianTSRoundConditionalGains
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-08-02T01:38:19.004283+00:00
-- url     : https://prove2.me/theorems/52584f4a-afb4-4994-87fb-1cf977d73a46
-- title:
--   Conditional regret and information gains for a Thompson round
-- statement:
--   Fix a Bayesian adversarial bandit, a round $t$, and a pre-round history $h$. The conditional regret gain is the regular conditional expectation
--
--   $$
--   r_t(h)=\mathbb E[X_{t,A^*}-X_{t,A_t}\mid H_t=h].
--   $$
--
--   The conditional information gain is the relative entropy between the conditional joint law of the optimal arm $A^*$ and the newly observed pair $(A_t,X_{t,A_t})$ and the product of their conditional marginals:
--
--   $$
--   g_t(h)=D\!\left(\mathcal L(A^*,(A_t,X_{t,A_t})\mid H_t=h)\,\middle\|\,\mathcal L(A^*\mid H_t=h)\otimes\mathcal L((A_t,X_{t,A_t})\mid H_t=h)\right).
--   $$
--
--   These are the canonical history-indexed quantities in the information-ratio proof of Bayesian Thompson-sampling regret bounds.
--
--   **Formalization Note** Regular conditional distributions are represented by Mathlib `condDistrib`; Kullback--Leibler divergence is converted from extended nonnegative reals to reals.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 (free PDF p. 479), https://tor-lattimore.com/downloads/book/book.pdf.

import Definitions.Def_BayesianHistoryMutualInformation
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
Lattimore--Szepesvari, *Bandit Algorithms* (2020), Lemma 36.7,
printed p. 470 / free PDF p. 479.

These are the two history-indexed quantities used in the information-ratio
proof.  The regret gain is conditional expected one-round regret.  The
information gain is the conditional mutual information between the optimal
arm and the newly observed arm--reward pair.
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- Conditional expected regret in round `t`, indexed by the history before
that round. -/
noncomputable def bayesianTSRoundConditionalRegretGain
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n)
    (h : BanditHistory k t.1) : ℝ :=
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let roundRegret := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1)
  ∫ p, roundRegret p ∂condDistrib id history mu h

/-- Conditional mutual information gained in round `t`: given the history
before the round, this is the KL divergence between the conditional joint law
of the optimal arm and the new arm--reward observation and the product of its
conditional marginals. -/
noncomputable def bayesianTSRoundConditionalInformationGain
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n)
    (h : BanditHistory k t.1) : ℝ :=
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let optimal := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    bayesianOptimalAction p.1
  let observation := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦ p.2 t
  let joint := condDistrib (fun p ↦ (optimal p, observation p)) history mu h
  let optimalMarginal := condDistrib optimal history mu h
  let observationMarginal := condDistrib observation history mu h
  (klDiv joint (optimalMarginal.prod observationMarginal)).toReal

end BanditAlgorithm


