-- Prove2me | Definitions.Def_AdversarialBandit
-- name    : AdversarialBandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-17T23:26:57.457174+00:00
-- url     : https://prove2.me/theorems/6333c025-81c5-4528-9f09-925ada21d57b
-- statement:
--   The adversarial $k$-armed bandit over horizon $n$: a reward matrix $x$ with entries in $[0,1]$ (threaded as $x : \mathbb{N} \to [k] \to \mathbb{R}$; only rows $t < n$ are used). A (randomized) policy $\pi$ (per-round Markov kernels on histories, as in the canonical model of §4.6) samples $A_t \sim P_t$ and observes the deterministic reward $X_t = x_{t A_t}$, giving the interconnection measure `adversarialMeasure` on histories. The expected regret (Eq. 11.1, `adversarialRegret`) is
--
--   $$R_n(\pi, x) = \max_{i\in[k]} \sum_{t=1}^n x_{ti} - \mathbb{E}\Big[\sum_{t=1}^n x_{tA_t}\Big],$$
--
--   and the random regret (Eq. 12.2, `adversarialRandomRegret`) is
--
--   $$\hat R_n = \max_i \sum_t x_{ti} - \sum_t X_t.$$
-- source:
--   L&S Ch 11.1, Eq. (11.1), pp.148-150

import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §11.1:
the adversarial `k`-armed bandit environment.

An adversary fixes a reward matrix `x` with `x t i ∈ [0,1]` — the reward of
arm `i` in round `t + 1` (rounds are indexed from `0` here). In each round the
learner samples an arm `A_t` from its policy's selection kernel applied to the
observed history and receives the DETERMINISTIC reward `X_t = x t (A_t)`
(Fig. 11.2). Interconnecting a policy `π : BanditPolicy k` (the same canonical
policy object as in the stochastic model, §4.6) with the reward matrix `x`
yields the probability measure `adversarialMeasure x π n` on histories of `n`
completed rounds: round `t` samples `A_t ~ π.select t (history)`, appends
`(A_t, x t A_t)`.

The (expected) regret is Eq. (11.1):
`R_n(π, x) = max_{i ∈ [k]} ∑_{t=1}^n x_{ti} - E[∑_{t=1}^n x_{t A_t}]`,
and the random regret (Ch 11 Note 1 / Eq. (12.2)) is
`R̂_n = max_{i ∈ [k]} ∑_{t=1}^n x_{ti} - ∑_{t=1}^n X_t`,
a function of the history.

The reward matrix is threaded as `x : ℕ → Fin k → ℝ` so that the round index
is available in the measure recursion; only the rows `t < n` are ever used by
`adversarialMeasure x π n`.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- One round of the adversarial bandit interconnection (L&S Fig. 11.2):
given the history of the first `n` rounds, sample the arm `A ~ π.select n`
and return the pair `(A, x n A)` — the reward is the deterministic matrix
entry, unlike the stochastic model. -/
noncomputable def adversarialStepKernel {k : ℕ} (x : ℕ → Fin k → ℝ)
    (π : BanditPolicy k) (n : ℕ) :
    Kernel (BanditHistory k n) (Fin k × ℝ) :=
  (π.select n).map (fun a ↦ (a, x n a))

instance adversarialStepKernel.instIsMarkovKernel {k : ℕ} (x : ℕ → Fin k → ℝ)
    (π : BanditPolicy k) (n : ℕ) :
    IsMarkovKernel (adversarialStepKernel x π n) :=
  Kernel.IsMarkovKernel.map _ (measurable_of_countable _)

/-- The adversarial bandit probability measure (L&S §11.1, Fig. 11.2): the
distribution of the history after `n` rounds of the interconnection of the
policy `π` with the fixed reward matrix `x`. Round `t` samples
`A_t ~ π.select t (history)` and appends `(A_t, x t A_t)` to the history.
All randomness comes from the learner's arm choices. -/
noncomputable def adversarialMeasure {k : ℕ} (x : ℕ → Fin k → ℝ)
    (π : BanditPolicy k) : (n : ℕ) → Measure (BanditHistory k n)
  | 0 => Measure.dirac (fun t ↦ t.elim0)
  | n + 1 =>
      ((adversarialMeasure x π n).compProd (adversarialStepKernel x π n)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2)

instance adversarialMeasure.instIsProbabilityMeasure {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (n : ℕ) :
    IsProbabilityMeasure (adversarialMeasure x π n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
      rw [adversarialMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map
        measurable_banditHistorySnoc.aemeasurable

/-- The random regret `R̂_n` (L&S Ch 11 Note 1 / Eq. (12.2)) of a history `h`
against the reward matrix `x`: the deficit of the collected rewards relative
to the best fixed arm in hindsight,
`R̂_n = max_{i ∈ [k]} ∑_{t=1}^n x_{ti} - ∑_{t=1}^n X_t`. -/
noncomputable def adversarialRandomRegret {k : ℕ} (n : ℕ)
    (x : ℕ → Fin k → ℝ) (h : BanditHistory k n) : ℝ :=
  (⨆ i, ∑ t : Fin n, x t i) - ∑ t, (h t).2

/-- The expected regret of the policy `π` on the adversarial bandit `x` over
horizon `n` (L&S Eq. (11.1)):
`R_n(π, x) = max_{i ∈ [k]} ∑_{t=1}^n x_{ti} - E[∑_{t=1}^n x_{t A_t}]`,
the expectation taken over the interconnection measure. -/
noncomputable def adversarialRegret {k : ℕ} (n : ℕ) (x : ℕ → Fin k → ℝ)
    (π : BanditPolicy k) : ℝ :=
  (⨆ i, ∑ t : Fin n, x t i) -
    ∫ h, (∑ t, (h t).2) ∂(adversarialMeasure x π n)

end BanditAlgorithm


