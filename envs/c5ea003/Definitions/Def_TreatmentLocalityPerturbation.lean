-- Prove2me | Definitions.Def_TreatmentLocalityPerturbation
-- name    : TreatmentLocalityPerturbation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T03:47:10.886149+00:00
-- url     : https://prove2.me/theorems/38397d74-17d2-4174-ac0d-fa293861ee11
-- title:
--   The SST family through a score direction
-- statement:
--   **The SST family through a score direction.** The Cramér-Rao bound of arXiv:2407.19618, Theorem 5, is computed along the family of SST models that share a base model's crucial state, discount factor and reward variances, and differ from it in the transition probabilities and the reward means. A *direction* in that family is a pair $(\alpha, \beta)$: at parameter $t$ the reward law at a state-action pair $(s,a)$ becomes
--   $$\mathcal{N}\bigl(m(s,a) + t\,\alpha(s,a)\,\sigma^2(s,a),\ \sigma^2(s,a)\bigr),$$
--   and the transition row becomes
--   $$P_t(j \mid s,a) \;=\; P(j \mid s,a)\bigl(1 + t\,\beta(s,a,j)\bigr).$$
--
--   The second is a probability vector exactly when $\sum_j P(j\mid s,a)\beta(s,a,j) = 0$ and $t$ is small enough for the weights to stay non-negative — which is the reason the transition part of a score is required to be centred. Only *executed* state-action pairs are moved: in the SST model the treatment action is available only at the crucial state, so the pairs with $\mathrm{act}(a,s) \ne a$ never occur along the experiment and their rows are left alone. The transition law falls back to the unperturbed one outside the admissible range of $t$, so the family is a total function of $t$.
--
--   These two directions span the tangent space of the family at the base model, and the corresponding score of one experiment step is
--   $$\alpha(s,a)\bigl(r - m(s,a)\bigr) + \beta(s,a,s'),$$
--   the general form against which an influence function is matched.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Appendix EC.4 (the parametrisation of the SST family by transition probabilities and reward means at fixed crucial state, discount factor and reward variances, and the constrained Cramér-Rao bound computed along it).

import Definitions.Def_TreatmentLocality
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
The one-parameter family of SST models obtained by moving the transition rows and the
Gaussian reward means of a base model along a score direction.

Source: Chen, Simchi-Levi, Wang, *Improving the Estimation of Lifetime Effects in A/B
Testing via Treatment Locality* (arXiv:2407.19618), Appendix EC.4: the parametrisation of
the SST family by the transition probabilities and the reward means, at fixed crucial
state, discount factor and reward variances, along which the Cramér-Rao bound of
Theorem 5 is computed.

Conventions: a direction is a pair `(α, β)`, where `α s a` moves the mean of the reward
law at `(s, a)` by `t · α s a · σ²(s,a)` and `β s a ·` moves the transition row
`P(· | s, a)` to `P(· | s, a)(1 + t β s a ·)`.  Only *executed* state-action pairs — those
with `act a s = a` — are perturbed; the remaining rows never occur along the experiment
and are left alone.  The transition law falls back to the unperturbed one when the
perturbed weights fail to be a probability vector, which happens only outside the range
of `t` for which the direction is admissible.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The perturbed transition weights: the row of an *executed* state-action pair is
multiplied by `1 + t β`, every other row is left alone. -/
noncomputable def perturbCoef (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (s : S) (a : Bool) (j : S) : ℝ :=
  if M.act a s = a then (M.trans s a j).toReal * (1 + t * β s a j)
  else (M.trans s a j).toReal

/-- The perturbed transition law, with the unperturbed law as a fallback when the weights
fail to be a probability vector. -/
noncomputable def perturbTrans (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (s : S) (a : Bool) : PMF S :=
  if h : (∑ j, ENNReal.ofReal (perturbCoef M β t s a j)) = 1 then
    PMF.ofFintype (fun j => ENNReal.ofReal (perturbCoef M β t s a j)) h
  else M.trans s a

/-- The perturbed SST model: transition rows moved along `β`, Gaussian reward means moved
along `α`, with the crucial state, the discount factor and the reward variances
unchanged. -/
noncomputable def perturbModel (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) : Model S where
  crucial := M.crucial
  trans := perturbTrans M β t
  reward := fun s a => gaussianReal (m s a + t * α s a * (v s a : ℝ)) (v s a)
  reward_prob := fun s a => inferInstance
  γdisc := M.γdisc
  γdisc_nonneg := M.γdisc_nonneg
  γdisc_lt_one := M.γdisc_lt_one

@[simp] lemma perturbModel_crucial (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) :
    (perturbModel M m v α β t).crucial = M.crucial := rfl

@[simp] lemma perturbModel_γdisc (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) :
    (perturbModel M m v α β t).γdisc = M.γdisc := rfl

@[simp] lemma perturbModel_act (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) (a : Bool) (s : S) :
    (perturbModel M m v α β t).act a s = M.act a s := rfl

@[simp] lemma perturbModel_trans (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) :
    (perturbModel M m v α β t).trans = perturbTrans M β t := rfl

/-- The perturbed model stays in the Gaussian family with the *same* variance profile. -/
lemma perturbModel_gaussianRewards (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) :
    (perturbModel M m v α β t).GaussianRewards
      (fun s a => m s a + t * α s a * (v s a : ℝ)) v := fun _ _ => rfl

end TreatmentLocality


