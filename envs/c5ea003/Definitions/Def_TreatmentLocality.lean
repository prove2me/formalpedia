-- Prove2me | Definitions.Def_TreatmentLocality
-- name    : TreatmentLocality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T15:59:51.872384+00:00
-- url     : https://prove2.me/theorems/eb99cebb-8b79-403a-904d-a14b95fc274b
-- title:
--   The single-state-treatment (SST) experiment model
-- statement:
--   The **single-state treatment (SST)** experiment model of arXiv:2407.19618, §2-§3. A `Model` is a finite-state MDP with binary actions (`true` = treatment $t$, `false` = control $c$): a crucial state $s^1$, transition laws $P(\cdot\mid s,a)$, reward laws with means $r(s,a)$, and a discount factor $0 \le \gamma < 1$. The SST restriction is built into `Model.act`: the arm labelled $\gamma$ executes the treatment action iff $\gamma = t$ **and** the current state is $s^1$, so the treatment policy $\pi^t$ and the control policy $\pi^c$ agree away from $s^1$ by construction. `Model.polTrans`/`Model.polReward`/`Model.value` are the policy transition matrices $P^a$, mean reward vectors $r^a$, and value functions $V^a = (I-\gamma P^a)^{-1} r^a$; `Model.ate` is the average treatment effect $\Delta = V^t - V^c$. The experiment runs the mixed policy $\pi^{1/2}$: at every step a fair coin picks the arm; a trajectory sample is the tuple $X_i = (s_i, \gamma_i, s_{i+1}, r_i)$ on `Step S` $= S \times \mathrm{Bool} \times S \times \mathbb{R}$, and `expKernel` is the Markov transition kernel of this tuple chain: the new current state is the previous next state, and the new (arm, next state, reward) triple is drawn by the coin flip, the transition law and the reward law (reward conditionally independent of the next state given the state-action pair). `Model.RewardL2` states all reward laws have finite second moment; `Model.GaussianRewards m v` states they are Gaussian with means $m$ and variances $v$.
-- source:
--   Chen, Simchi-Levi, Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, https://arxiv.org/abs/2407.19618, §2 (the MDP, SST, policies, value functions, ATE), §3 (Algorithm 1: the mixed policy), Appendix EC.3.1 (the tuple chain)

import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The Single-State Treatment (SST) experiment model: a finite-state MDP with two
actions (control `c` and treatment `t`), where the treatment is applicable only
in a designated *crucial* state `s¹`; the mixed experiment policy `π^{1/2}`
flips a fair coin between the treatment arm and the control arm at every step,
and the resulting experiment trajectory `(sᵢ, aᵢ, sᵢ₊₁, rᵢ)` is a Markov chain
on `S × Bool × S × ℝ`.

Source: Chen, Simchi-Levi, Wang, *Improving the Estimation of Lifetime Effects
in A/B Testing via Treatment Locality* (arXiv:2407.19618), §2 (the MDP and the
SST structure, the policies `π^c`, `π^t`, the value functions and the ATE
`Δ = V^t - V^c`) and §3 (Algorithm 1: running the mixed policy `π^{1/2}`).

Conventions:
* actions are `Bool`, with `true` = treatment `t` and `false` = control `c`;
* an *arm label* `γᵢ : Bool` is drawn i.i.d. fair at every step (which of
  `π^t`/`π^c` acts at step `i`); the executed action is
  `act γ s = γ && (s = s¹)` — the two policies only differ at the crucial
  state, which is exactly the SST restriction that the treatment action is
  available only in `s¹`;
* the reward `rᵢ` is drawn from the reward law `reward sᵢ aᵢ`, conditionally
  independent of `sᵢ₊₁` given `(sᵢ, aᵢ)`;
* a trajectory sample is the tuple `Xᵢ = (sᵢ, γᵢ, sᵢ₊₁, rᵢ)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable (S : Type*)

/-- The **SST model**: a finite-state MDP with binary actions
(`true` = treatment, `false` = control), a designated crucial state, transition
laws, reward laws, and a discount factor `0 ≤ γdisc < 1`
(arXiv:2407.19618, §2).  The SST restriction is built into `Model.act` below:
the treatment action is executed only in the crucial state, so the two
policies `π^t`/`π^c` agree away from it by construction. -/
structure Model where
  /-- The crucial state `s¹` targeted by the single-state treatment. -/
  crucial : S
  /-- The transition law `P(· | s, a)`. -/
  trans : S → Bool → PMF S
  /-- The reward law at `(s, a)`; its mean is the mean reward `r(s, a)`. -/
  reward : S → Bool → Measure ℝ
  /-- Each reward law is a probability measure. -/
  reward_prob : ∀ s a, IsProbabilityMeasure (reward s a)
  /-- The discount factor `γ`. -/
  γdisc : ℝ
  γdisc_nonneg : 0 ≤ γdisc
  γdisc_lt_one : γdisc < 1

variable {S}

instance (M : Model S) (s : S) (a : Bool) : IsProbabilityMeasure (M.reward s a) :=
  M.reward_prob s a

variable [DecidableEq S]

/-- The action executed at state `s` by the arm labelled `γ`: the treatment is
applied iff the arm is the treatment arm **and** the state is the crucial one —
the SST restriction (arXiv:2407.19618, §2). -/
def Model.act (M : Model S) (γ : Bool) (s : S) : Bool :=
  γ && decide (s = M.crucial)

/-- Every reward law has a finite second moment (finite `σ²(s, a)`;
arXiv:2407.19618, §2, where the reward noise has finite variance). -/
def Model.RewardL2 (M : Model S) : Prop :=
  ∀ s a, MemLp (fun x : ℝ => x) 2 (M.reward s a)

/-- All reward laws are Gaussian with mean `m s a` and variance `v s a` —
the parametric reward model under which the Cramér-Rao lower bound
(arXiv:2407.19618, Theorem 5 and Appendix EC.4) is stated. -/
def Model.GaussianRewards (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0) :
    Prop :=
  ∀ s a, M.reward s a = gaussianReal (m s a) (v s a)

section Matrices

variable [Fintype S]

/-- The transition matrix `P^a` of the policy that plays arm `a`
(`P^t` for `a = true`, `P^c` for `a = false`): row `s` is the law of the next
state when the arm-`a` policy acts at `s` (arXiv:2407.19618, §2). -/
noncomputable def Model.polTrans (M : Model S) (a : Bool) : Matrix S S ℝ :=
  Matrix.of fun s j => ((M.trans s (M.act a s)) j).toReal

/-- The mean reward vector `r^a` of the policy that plays arm `a`
(arXiv:2407.19618, §2). -/
noncomputable def Model.polReward (M : Model S) (a : Bool) : S → ℝ :=
  fun s => ∫ x, x ∂(M.reward s (M.act a s))

/-- The value function `V^a = (I - γ P^a)⁻¹ r^a` of the policy that plays arm
`a` — the model-based form of the Bellman equation (arXiv:2407.19618, §2,
eq. (2)). -/
noncomputable def Model.value (M : Model S) (a : Bool) : S → ℝ :=
  (((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹).mulVec (M.polReward a)

/-- The average treatment effect `Δ = V^t - V^c` (arXiv:2407.19618, §2). -/
noncomputable def Model.ate (M : Model S) : S → ℝ :=
  M.value true - M.value false

end Matrices

section Chain

variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The sample space of one experiment step: `Xᵢ = (sᵢ, γᵢ, sᵢ₊₁, rᵢ)` —
current state, arm label, next state, realized reward
(arXiv:2407.19618, Appendix EC.3.1). -/
abbrev Step (S : Type*) : Type _ := S × Bool × S × ℝ

/-- The state occupied at a step: the first component `sᵢ`. -/
def Step.state (z : Step S) : S := z.1

/-- The arm label `γᵢ` of a step. -/
def Step.arm (z : Step S) : Bool := z.2.1

/-- The next state `sᵢ₊₁` of a step. -/
def Step.next (z : Step S) : S := z.2.2.1

/-- The realized reward `rᵢ` of a step. -/
def Step.rwd (z : Step S) : ℝ := z.2.2.2

variable [Countable S] [DecidableEq S]

/-- The law of `(γᵢ, sᵢ₊₁, rᵢ)` given the current state `sᵢ = s` under the mixed
experiment policy `π^{1/2}`: a fair coin picks the arm `γ`, the executed action
is `act γ s`, then the next state and the reward are drawn independently from
`trans s (act γ s)` and `reward s (act γ s)`
(arXiv:2407.19618, §3, Algorithm 1). -/
noncomputable def stepLaw (M : Model S) (s : S) : Measure (Bool × S × ℝ) :=
  (2 : ℝ≥0∞)⁻¹ •
    ((Measure.dirac true).prod
        (((M.trans s (M.act true s)).toMeasure).prod (M.reward s (M.act true s)))
      + (Measure.dirac false).prod
        (((M.trans s (M.act false s)).toMeasure).prod (M.reward s (M.act false s))))

instance (M : Model S) (s : S) : IsProbabilityMeasure (stepLaw M s) := by
  constructor
  rw [stepLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  have h1 : ((Measure.dirac true).prod
      (((M.trans s (M.act true s)).toMeasure).prod (M.reward s (M.act true s))))
      Set.univ = 1 := measure_univ
  have h2 : ((Measure.dirac false).prod
      (((M.trans s (M.act false s)).toMeasure).prod (M.reward s (M.act false s))))
      Set.univ = 1 := measure_univ
  rw [h1, h2]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The one-step transition of the experiment chain, as a kernel from the
current state: `s ↦ stepLaw M s`. -/
noncomputable def stepKernel (M : Model S) : Kernel S (Bool × S × ℝ) :=
  Kernel.ofFunOfCountable (stepLaw M)

instance (M : Model S) : IsMarkovKernel (stepKernel M) :=
  ⟨fun s => inferInstanceAs (IsProbabilityMeasure (stepLaw M s))⟩

/-- The transition kernel of the experiment trajectory chain
`Xᵢ = (sᵢ, γᵢ, sᵢ₊₁, rᵢ) ↦ Xᵢ₊₁ = (sᵢ₊₁, γᵢ₊₁, sᵢ₊₂, rᵢ₊₁)` under the mixed
policy `π^{1/2}`: the new current state is the previous next state, and the new
`(arm, next state, reward)` triple is drawn from `stepLaw` at it.  The
experiment trajectory of arXiv:2407.19618 (§3, Algorithm 1; Appendix EC.3) is
the Markov chain on `Step S` with this kernel. -/
noncomputable def expKernel (M : Model S) : Kernel (Step S) (Step S) :=
  (Kernel.deterministic Step.next
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)))).prod
    ((stepKernel M).comap Step.next
      ((measurable_fst.comp (measurable_snd.comp measurable_snd))))

instance (M : Model S) : IsMarkovKernel (expKernel M) := by
  rw [expKernel]
  infer_instance

end Chain

end TreatmentLocality


