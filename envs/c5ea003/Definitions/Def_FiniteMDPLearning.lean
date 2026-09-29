-- Prove2me | Definitions.Def_FiniteMDPLearning
-- name    : FiniteMDPLearning
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-30T15:57:49.863327+00:00
-- url     : https://prove2.me/theorems/7cd7ee29-63d7-45f4-a177-3383e36fbe73
-- statement:
--   Online learning in a finite MDP $M = (\mathcal{S}, \mathcal{A}, P, r)$ with $S$ states, $A$ actions and deterministic rewards $r_a(s) \in [0,1]$ (L&S §38.1): the transition function $P_a(s,\cdot)$ is a probability vector over states. The interaction protocol (Fig. 38.1): $S_1 \sim \mu$, in round $t$ the learner observes $S_t$, chooses $A_t$ from the history via a Markov kernel, receives $r_{A_t}(S_t)$, and $S_{t+1} \sim P_{A_t}(S_t)$; the interconnection measure on trajectories $((S_1,A_1),\dots,(S_n,A_n))$ is built by finite-horizon kernel composition. Includes the gain
--
--   $$\bar\rho^\pi_s = \limsup_n \frac{1}{n}\sum_{t=1}^n \mathbb{E}^\pi[r_{A_t}(S_t) \mid S_1 = s]$$
--
--   and the optimal gain $\rho^* = \max_s \sup_\pi \bar\rho^\pi_s$ over all policies (§38.2); the diameter
--
--   $$D(M) = \max_{s\ne s'} \min_{\pi \in \Pi_{\mathrm{DM}}} \mathbb{E}^\pi[\min\{t \ge 1 : S_t = s\} \mid S_1 = s'] - 1$$
--
--   over memoryless deterministic policies (Definition 38.1, encoded via the tail-sum formula $\mathbb{E}[\tau] - 1 = \sum_{k\ge 1}\mathbb{P}(\tau > k)$ in $[0,\infty]$); strongly connected (communicating) MDPs (§38.1); and the random regret
--
--   $$\hat R_n = n\rho^* - \sum_{t=1}^n r_{A_t}(S_t)$$
--
--   (§38.4).
-- source:
--   L&S Ch 38.1-38.4, pp.510-523

import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 38
(§38.1, §38.2, §38.4): online learning in a finite Markov decision process.

A finite MDP with `S` states and `A` actions is a transition function
`P : Fin S → Fin A → (Fin S → ℝ≥0)` (each row a probability vector) together
with a deterministic reward function `r : Fin S → Fin A → ℝ` taking values in
`[0,1]` (§38.1: "it receives a deterministic reward `r_a(s)`").

The interaction protocol (Fig. 38.1): the initial state `S₁` is sampled from
an initial distribution `μ`; in round `t` the learner observes `S_t`, chooses
`A_t` (possibly at random, given the whole history), receives `r_{A_t}(S_t)`,
and the environment samples `S_{t+1} ~ P_{A_t}(S_t)`. A trajectory of `n`
completed rounds is the sequence `(S₁, A₁), …, (S_n, A_n)`; a policy is a
family of Markov kernels from (past trajectory, current state) to actions —
this is exactly the book's history `H_t = (S₁, A₁, …, S_{t−1}, A_{t−1}, S_t)`.
The interconnection of a policy with an MDP induces the probability measure
`mdpMeasure` on trajectories, built by the same `Fin.snoc` recursion as
`banditMeasure` (L&S §4.6); on a finite horizon this needs no Ionescu–Tulcea.

Further definitions, all transcribed from Ch 38:
* the gain `ρ̄ˢ_π = limsup_n (1/n) ∑_{t=1}^n E^π[r_{A_t}(S_t) | S₁ = s]`
  and the optimal gain `ρ* = max_s sup_π ρ̄ˢ_π` (sup over **all** policies, §38.2);
* the diameter `D(M) = max_{s ≠ s'} min_{π ∈ Π_DM} E^π[min{t ≥ 1 : S_t = s} | S₁ = s'] − 1`
  (Definition 38.1), the min running over memoryless **deterministic** policies.
  The expected hitting time is encoded by finite-horizon marginals:
  `E[τ] − 1 = ∑_{k ≥ 1} P(τ > k)` and `P(τ > k)` = probability that none of the
  first `k` states equals the target; the sum is taken in `ℝ≥0∞`, and the
  real-valued diameter is its `toReal` (junk value `0` iff `M` is not
  strongly connected, where the book's `D(M) = ∞`, cf. Exercise 38.4);
* strongly connected (communicating) MDPs (§38.1);
* the random regret `R̂_n = n ρ* − ∑_{t=1}^n r_{A_t}(S_t)` (§38.4), a function
  of the trajectory.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace BanditAlgorithm

/-- A finite Markov decision process `M = (S, A, P, r)` with `S` states and
`A` actions (L&S §38.1): transition probability vectors `P_a(s, ·)` and a
deterministic reward function `r_a(s) ∈ [0,1]`. -/
structure FiniteMDP (S A : ℕ) where
  /-- `P s a` is the probability vector of the next state when action `a`
  is taken in state `s`. -/
  P : Fin S → Fin A → Fin S → ℝ≥0
  /-- Each `P s a` is a probability vector. -/
  P_sum_one : ∀ s a, ∑ s', P s a s' = 1
  /-- The deterministic reward received when taking action `a` in state `s`. -/
  r : Fin S → Fin A → ℝ
  /-- Rewards take values in `[0,1]`. -/
  r_mem_Icc : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1

/-- A probability distribution over the states `Fin S`, as a probability
vector; used for the initial state distribution `μ` of L&S §38.1 and for the
rows of the transition function. -/
structure MDPStateDistribution (S : ℕ) where
  /-- The probability of each state. -/
  prob : Fin S → ℝ≥0
  /-- The probabilities sum to one. -/
  sum_one : ∑ s, prob s = 1

/-- The probability measure on `Fin S` associated with a probability
vector: `∑ s, prob s • δ_s`. -/
noncomputable def MDPStateDistribution.toMeasure {S : ℕ}
    (d : MDPStateDistribution S) : Measure (Fin S) :=
  ∑ s, (d.prob s : ℝ≥0∞) • Measure.dirac s

instance MDPStateDistribution.instIsProbabilityMeasure {S : ℕ}
    (d : MDPStateDistribution S) : IsProbabilityMeasure d.toMeasure := by
  constructor
  rw [MDPStateDistribution.toMeasure, Measure.finset_sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.coe_finset_sum, d.sum_one, ENNReal.coe_one]

/-- The Dirac distribution concentrated on state `s`; replaces the initial
distribution when the book writes `ℙ(· | S₁ = s)` (§38.1). -/
def mdpStateDirac {S : ℕ} (s : Fin S) : MDPStateDistribution S where
  prob := fun s' ↦ if s' = s then 1 else 0
  sum_one := by simp

/-- The transition row `P_a(s, ·)` of an MDP, as a state distribution. -/
def FiniteMDP.transitionDist {S A : ℕ} (M : FiniteMDP S A) (s : Fin S)
    (a : Fin A) : MDPStateDistribution S :=
  ⟨M.P s a, M.P_sum_one s a⟩

/-- A trajectory of `n` completed rounds of the MDP interaction protocol:
the sequence `(S₁, A₁), …, (S_n, A_n)` of (state, action) pairs
(L&S §38.1, Fig. 38.1; rewards are omitted because they are the deterministic
function `r` of the state-action pair). -/
abbrev MDPTrajectory (S A n : ℕ) := Fin n → Fin S × Fin A

/-- A (history-dependent, randomised) policy for MDP learning (L&S §38.1):
for each round, a Markov kernel from the observed history
`H_{n+1} = (S₁, A₁, …, S_n, A_n, S_{n+1})` — encoded as the pair (trajectory
of the `n` completed rounds, current state) — to the action played next. -/
structure MDPPolicy (S A : ℕ) where
  /-- The conditional distribution of the action of round `n + 1` given the
  first `n` completed rounds and the current state. -/
  select : (n : ℕ) → Kernel (MDPTrajectory S A n × Fin S) (Fin A)
  /-- Each round's selection kernel is a Markov kernel. -/
  markov : ∀ n, IsMarkovKernel (select n)

attribute [instance] MDPPolicy.markov

/-- The transition kernel of an MDP: from the current (state, action) pair
to the next state, `S_{t+1} ~ P_{A_t}(S_t)` (L&S §38.1). -/
noncomputable def mdpTransitionKernel {S A : ℕ} (M : FiniteMDP S A) :
    Kernel (Fin S × Fin A) (Fin S) :=
  Kernel.ofFunOfCountable fun p ↦ (M.transitionDist p.1 p.2).toMeasure

instance mdpTransitionKernel.instIsMarkovKernel {S A : ℕ} (M : FiniteMDP S A) :
    IsMarkovKernel (mdpTransitionKernel M) :=
  ⟨fun p ↦ (M.transitionDist p.1 p.2).instIsProbabilityMeasure⟩

/-- The kernel giving the state observed in round `n + 1` from the trajectory
of the first `n` rounds: the initial state is sampled from `μ0` (round 1),
and later states from the transition function applied to the last
(state, action) pair (L&S Fig. 38.1). -/
noncomputable def mdpStateKernel {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) :
    (n : ℕ) → Kernel (MDPTrajectory S A n) (Fin S)
  | 0 => Kernel.const _ μ0.toMeasure
  | n + 1 =>
      (mdpTransitionKernel M).comap
        (fun h : MDPTrajectory S A (n + 1) ↦ h (Fin.last n))
        (measurable_pi_apply _)

instance mdpStateKernel.instIsMarkovKernel {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (n : ℕ) :
    IsMarkovKernel (mdpStateKernel M μ0 n) := by
  cases n with
  | zero => rw [mdpStateKernel]; infer_instance
  | succ n => rw [mdpStateKernel]; infer_instance

/-- One round of the MDP interaction protocol (L&S Fig. 38.1): given the
trajectory of the first `n` rounds, observe the state `S ~ mdpStateKernel`,
then choose the action `A ~ π.select n` given the history and `S`,
returning the pair `(S, A)`. -/
noncomputable def mdpStepKernel {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ) :
    Kernel (MDPTrajectory S A n) (Fin S × Fin A) :=
  (mdpStateKernel M μ0 n).compProd (π.select n)

instance mdpStepKernel.instIsMarkovKernel {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ) :
    IsMarkovKernel (mdpStepKernel M μ0 π n) := by
  rw [mdpStepKernel]
  infer_instance

/-- Appending one round to a trajectory is measurable. -/
lemma measurable_mdpTrajectorySnoc {S A n : ℕ} :
    Measurable (fun p : MDPTrajectory S A n × (Fin S × Fin A) ↦
      Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2) := by
  rw [measurable_pi_iff]
  intro t
  by_cases ht : (t : ℕ) < n
  · have : (fun p : MDPTrajectory S A n × (Fin S × Fin A) ↦
        Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2 t) =
        fun p ↦ p.1 (Fin.castLT t ht) := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact (measurable_pi_apply _).comp measurable_fst
  · have : (fun p : MDPTrajectory S A n × (Fin S × Fin A) ↦
        Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2 t) =
        fun p ↦ p.2 := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact measurable_snd

/-- The MDP learning probability measure (L&S §38.1, Fig. 38.1): the
distribution of the trajectory `(S₁, A₁), …, (S_n, A_n)` resulting from the
interconnection of policy `π` with MDP `M` started from `S₁ ~ μ0`. -/
noncomputable def mdpMeasure {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) :
    (n : ℕ) → Measure (MDPTrajectory S A n)
  | 0 => Measure.dirac (fun t ↦ t.elim0)
  | n + 1 =>
      ((mdpMeasure M μ0 π n).compProd (mdpStepKernel M μ0 π n)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2)

instance mdpMeasure.instIsProbabilityMeasure {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ) :
    IsProbabilityMeasure (mdpMeasure M μ0 π n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
      rw [mdpMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map
        measurable_mdpTrajectorySnoc.aemeasurable

/-- The total reward `∑_{t=1}^n r_{A_t}(S_t)` collected along a trajectory
(L&S §38.1; rewards are the deterministic function `r` of the pairs). -/
def mdpTrajectoryReward {S A : ℕ} (M : FiniteMDP S A) {n : ℕ}
    (h : MDPTrajectory S A n) : ℝ :=
  ∑ t, M.r (h t).1 (h t).2

/-- The expected total reward `E^π[∑_{t=1}^n r_{A_t}(S_t)]` of `n` rounds of
the interconnection of `π` and `M` started from `μ0`. -/
noncomputable def mdpExpectedReward {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ) : ℝ :=
  ∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M μ0 π n)

/-- The gain `ρ̄ˢ_π = limsup_{n→∞} (1/n) ∑_{t=1}^n E^π[r_{A_t}(S_t) | S₁ = s]`
of policy `π` started at state `s` (L&S §38.2; the `limsup` version, which
exists for any policy and equals the Cesàro limit `ρˢ_π` whenever the latter
exists). -/
noncomputable def mdpGain {S A : ℕ} (M : FiniteMDP S A) (π : MDPPolicy S A)
    (s : Fin S) : ℝ :=
  Filter.limsup
    (fun n : ℕ ↦ mdpExpectedReward M (mdpStateDirac s) π n / n) Filter.atTop

/-- The optimal gain `ρ* = max_{s ∈ S} sup_π ρ̄ˢ_π` (L&S §38.2), the supremum
taken over **all** policies, as in the book. For strongly connected MDPs it is
attained by a deterministic memoryless policy (L&S Theorem 38.2). -/
noncomputable def mdpOptimalGain {S A : ℕ} (M : FiniteMDP S A) : ℝ :=
  ⨆ s : Fin S, ⨆ π : MDPPolicy S A, mdpGain M π s

/-- The random regret `R̂_n = n ρ* − ∑_{t=1}^n r_{A_t}(S_t)` of a trajectory
(L&S §38.4). -/
noncomputable def mdpRegret {S A : ℕ} (M : FiniteMDP S A) (n : ℕ)
    (h : MDPTrajectory S A n) : ℝ :=
  n * mdpOptimalGain M - mdpTrajectoryReward M h

/-- The memoryless deterministic policy determined by a map
`f : states → actions` (the class `Π_DM` of L&S §38.1). -/
noncomputable def mdpMemorylessDetPolicy {S A : ℕ} (f : Fin S → Fin A) :
    MDPPolicy S A where
  select _ :=
    Kernel.deterministic (fun p ↦ f p.2)
      ((measurable_of_countable f).comp measurable_snd)
  markov _ := Kernel.isMarkovKernel_deterministic _

/-- The expected travel time `E^π[min{t ≥ 1 : S_t = tgt} | S₁ = src] − 1` of
the memoryless deterministic policy `f` from state `src` to state `tgt`
(the quantity minimised in L&S Definition 38.1), encoded through its
finite-horizon marginals: for the hitting time `τ = min{t ≥ 1 : S_t = tgt}`
one has `E[τ] − 1 = ∑_{k ≥ 1} P(τ > k)`, and `P(τ > k)` is the probability
that none of the first `k` states equals `tgt`. The value is `⊤` iff the
expected hitting time is infinite. -/
noncomputable def mdpTravelTime {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (src tgt : Fin S) : ℝ≥0∞ :=
  ∑' k : ℕ,
    mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)
      {h | ∀ t, (h t).1 ≠ tgt}

/-- The diameter of an MDP, valued in `ℝ≥0∞` (L&S Definition 38.1):
`D(M) = max_{s ≠ s'} min_{π ∈ Π_DM} E^π[min{t ≥ 1 : S_t = s} | S₁ = s'] − 1`,
where the minimum runs over the memoryless deterministic policies `Π_DM`
(the book notes this restriction is inessential). `D(M) < ⊤` iff `M` is
strongly connected (L&S Exercise 38.4). -/
noncomputable def mdpDiameterENN {S A : ℕ} (M : FiniteMDP S A) : ℝ≥0∞ :=
  ⨆ src : Fin S, ⨆ tgt : Fin S, ⨆ _ : src ≠ tgt,
    ⨅ f : Fin S → Fin A, mdpTravelTime M f src tgt

/-- The real-valued diameter `D(M)` of L&S Definition 38.1
(junk value `0` when `M` is not strongly connected, i.e. `D(M) = ∞`). -/
noncomputable def mdpDiameter {S A : ℕ} (M : FiniteMDP S A) : ℝ :=
  (mdpDiameterENN M).toReal

/-- An MDP is strongly connected (communicating) if for any pair of distinct
states `s ≠ s'` there is a policy under which, starting from `s`, the state
`s'` is reached at some time with positive probability (L&S §38.1). -/
def FiniteMDP.IsCommunicating {S A : ℕ} (M : FiniteMDP S A) : Prop :=
  ∀ s s' : Fin S, s ≠ s' →
    ∃ π : MDPPolicy S A, ∃ n : ℕ,
      mdpMeasure M (mdpStateDirac s) π n {h | ∃ t, (h t).1 = s'} ≠ 0

end BanditAlgorithm


