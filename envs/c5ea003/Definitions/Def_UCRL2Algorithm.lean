-- Prove2me | Definitions.Def_UCRL2Algorithm
-- name    : UCRL2Algorithm
-- status  : Definition
-- author  : @Grace
-- created : 2026-08-02T23:13:48.765263+00:00
-- url     : https://prove2.me/theorems/8854b0d1-fff1-4297-843c-7c0f6bc756f6
-- title:
--   The UCRL2 algorithm
-- statement:
--   UCRL2 (Lattimore and Szepesvari, Section 38.5, after Jaksch, Ortner and Auer, Section 3) is the optimism-in-the-face-of-uncertainty algorithm for learning in a finite MDP with known rewards. It proceeds in *phases*: a phase ends as soon as the number of visits to some state-action pair inside it reaches the number of visits accumulated before it began -- the doubling criterion, which forces the number of phases to be logarithmic in the horizon. At the start of a phase the learner forms, from the transitions observed so far, an $L^1$ confidence ball around each empirical transition row, computes an *optimistic plan* -- a gain $\rho\in[0,1]$, a bias $v$ and a greedy action map $f$ with witnessing rows $q$ solving the average-reward Bellman optimality equation $\rho+v(s)=r(s,f(s))+\langle q(s),v\rangle$ of the extended MDP whose rows range over those balls, and dominating $r(s,a)+\langle p,v\rangle$ for every row $p$ the balls allow -- and plays that action map for the whole phase.
--
--   This file records the constructions: the phase schedule, the predicate of being an optimistic plan, the plan committed to for a phase, and the resulting policy. Two bookkeeping points are settled here. First, at the beginning of round $t$ the learner has already observed the state $S_t$, hence all $t$ transitions out of rounds $0,\dots,t-1$, although a trajectory of $t$ rounds records only the pairs $(S_i,A_i)$ for $i<t$; the counts are therefore read off the trajectory *extended by the current state*, at time $\tau+1$ where $\tau$ starts the current phase, which makes the sample size of the ball of a pair exactly the number of visits to it strictly before $\tau$. Second, an optimistic plan need not exist for an arbitrary family of balls -- it does whenever they are nonempty compact sets of probability vectors containing the rows of a communicating MDP, which is extended value iteration and is the case on the good event -- so off that case the plan is chosen arbitrarily, keeping the policy a total function of the observed history and of the known $n$, $\delta$ and $r$ alone.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5, printed pp. 524-526 / PDF pp. 533-535; after Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010), Section 3 (Figure 2).

import Definitions.Def_UCRL2ConfidenceSets

/-!
# The UCRL2 algorithm

Lattimore and Szepesvari, *Bandit Algorithms* (CUP 2020), Section 38.5, after
Jaksch, Ortner and Auer, *Near-optimal regret bounds for reinforcement
learning*, JMLR 11 (2010), Section 3.

UCRL2 is the optimism-in-the-face-of-uncertainty algorithm for learning in a
finite MDP with known rewards.  It proceeds in *phases*: a phase ends as soon as
the number of visits to some state-action pair inside it reaches the number of
visits accumulated before it began -- the doubling criterion, which forces the
number of phases to be logarithmic in the horizon.  At the start of a phase the
learner forms, from the transitions observed so far, an `L¹` confidence ball
around each empirical transition row (`Def_UCRL2ConfidenceSets`), computes an
*optimistic plan* -- a gain-bias pair solving the average-reward Bellman
optimality equation of the extended MDP whose rows range over those balls --
and plays its greedy action map for the whole phase.

Two bookkeeping points deserve care.

*The learner sees one more state than the trajectory records.*  A trajectory of
`t` rounds is the list of pairs `(S_0, A_0), …, (S_{t-1}, A_{t-1})`, so the
transition out of round `i` is visible only when round `i + 1` is recorded.  At
the beginning of round `t` the learner has, however, already observed the state
`S_t`, hence all `t` transitions out of rounds `0, …, t - 1`.  The counts are
therefore formed from the trajectory *extended by the current state*, and read
at time `τ + 1` where `τ` is the start of the current phase; this makes the
sample size of the ball of a pair exactly the number of visits to it strictly
before `τ`, which is the count the regret analysis sums over.

*The optimistic plan need not exist for every family of balls.*  It does exist
whenever the balls are nonempty compact sets of probability vectors containing
the rows of a communicating MDP -- extended value iteration -- which is the case
on the good event.  Off it the plan is chosen arbitrarily, so that the policy is
a total function of the observed history and of the known quantities `n`, `δ`
and `r` alone, never of the unknown transition function.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace BanditAlgorithm

variable {S A : ℕ}

/-! ### The phase schedule -/

/-- The time at which the phase current at time `u` began.  Phases start at
time `0`, and a new phase begins at time `u + 1` as soon as the number of visits
to some pair `(s, a)` since the start of the current phase has reached
`max 1` of the number of visits accumulated before it: the doubling criterion of
L&S Section 38.5. -/
def mdpPhaseStart {S A t : ℕ} (h : MDPTrajectory S A t) : ℕ → ℕ
  | 0 => 0
  | u + 1 =>
      let τ := mdpPhaseStart h u
      if ∃ s a, max 1 (mdpVisitCount h τ s a) ≤
          mdpVisitCount h (u + 1) s a - mdpVisitCount h τ s a then
        u + 1
      else τ

/-! ### Optimistic plans -/

/-- An *optimistic plan* for the reward function `r` and the confidence balls
`C`: a gain `ρ ∈ [0, 1]`, a bias `v`, and a memoryless deterministic action map
`f` with witnessing transition rows `q`, such that `(ρ, v)` satisfies the
average-reward Bellman inequality against *every* transition row allowed by `C`,
with equality attained at `(f, q)`.  This is a solution of the Bellman
optimality equation of the extended MDP of L&S Section 38.5. -/
def IsOptimisticPlan {S A : ℕ} (r : Fin S → Fin A → ℝ)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) (ρ : ℝ) (v : Fin S → ℝ)
    (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ) : Prop :=
  0 ≤ ρ ∧ ρ ≤ 1 ∧
  (∀ s a, ∀ p ∈ C s a, r s a + ∑ s', p s' * v s' ≤ ρ + v s) ∧
  (∀ s, q s ∈ C s (f s)) ∧
  (∀ s, ρ + v s = r s (f s) + ∑ s', q s s' * v s')

open Classical in
/-- The plan the learner commits to for a phase: an optimistic plan for the
balls `C` if one exists, and the trivial data otherwise.  Bundling the four
components makes the gain, the bias, the action map and the witnessing rows
*functions of the observed history*, which is what the martingale term of the
regret analysis refers to. -/
noncomputable def mdpOptimisticPlan {S A : ℕ} [NeZero A] (r : Fin S → Fin A → ℝ)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) :
    ℝ × (Fin S → ℝ) × (Fin S → Fin A) × (Fin S → Fin S → ℝ) :=
  if hex : ∃ p : ℝ × (Fin S → ℝ) × (Fin S → Fin A) × (Fin S → Fin S → ℝ),
      IsOptimisticPlan r C p.1 p.2.1 p.2.2.1 p.2.2.2 then hex.choose
  else (0, fun _ ↦ 0, fun _ ↦ default, fun _ _ ↦ 0)

/-- The optimistic gain of the plan committed to for a phase. -/
noncomputable def mdpOptimisticGain {S A : ℕ} [NeZero A] (r : Fin S → Fin A → ℝ)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) : ℝ :=
  (mdpOptimisticPlan r C).1

/-- The optimistic bias of the plan committed to for a phase. -/
noncomputable def mdpOptimisticBias {S A : ℕ} [NeZero A] (r : Fin S → Fin A → ℝ)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) : Fin S → ℝ :=
  (mdpOptimisticPlan r C).2.1

/-- The action map played throughout a phase: the greedy action map of the
optimistic plan committed to. -/
noncomputable def mdpOptimisticActionMap {S A : ℕ} [NeZero A]
    (r : Fin S → Fin A → ℝ) (C : Fin S → Fin A → Set (Fin S → ℝ)) :
    Fin S → Fin A :=
  (mdpOptimisticPlan r C).2.2.1

/-- The optimistic transition rows attaining equality in the Bellman equation of
the plan committed to. -/
noncomputable def mdpOptimisticRow {S A : ℕ} [NeZero A] (r : Fin S → Fin A → ℝ)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) : Fin S → Fin S → ℝ :=
  (mdpOptimisticPlan r C).2.2.2

/-- Whenever some optimistic plan for `C` exists, the four components committed
to do form one. -/
lemma isOptimisticPlan_mdpOptimisticPlan {S A : ℕ} [NeZero A]
    (r : Fin S → Fin A → ℝ) (C : Fin S → Fin A → Set (Fin S → ℝ))
    (hex : ∃ (ρ : ℝ) (v : Fin S → ℝ) (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ),
      IsOptimisticPlan r C ρ v f q) :
    IsOptimisticPlan r C (mdpOptimisticGain r C) (mdpOptimisticBias r C)
      (mdpOptimisticActionMap r C) (mdpOptimisticRow r C) := by
  classical
  obtain ⟨ρ, v, f, q, hplan⟩ := hex
  have hex' : ∃ p : ℝ × (Fin S → ℝ) × (Fin S → Fin A) × (Fin S → Fin S → ℝ),
      IsOptimisticPlan r C p.1 p.2.1 p.2.2.1 p.2.2.2 := ⟨(ρ, v, f, q), hplan⟩
  have hval : mdpOptimisticPlan r C = hex'.choose := by
    rw [mdpOptimisticPlan, dif_pos hex']
  simpa [mdpOptimisticGain, mdpOptimisticBias, mdpOptimisticActionMap,
    mdpOptimisticRow, hval] using hex'.choose_spec

/-! ### The algorithm -/

/-- The history the learner has actually seen at the start of round `t`: the
trajectory of the `t` completed rounds together with the current state, recorded
as one more round whose action is a placeholder.  Reading the counts of
`Def_UCRL2ConfidenceSets` off this object makes the transition out of round
`t - 1`, whose target is the current state, visible to the learner. -/
def mdpObservedHistory {S A t : ℕ} [NeZero A] (h : MDPTrajectory S A t)
    (s : Fin S) : MDPTrajectory S A (t + 1) :=
  Fin.snoc h (s, default)

/-- The confidence balls UCRL2 uses during the phase current at time `t`: those
of `Def_UCRL2ConfidenceSets` formed from all transitions observed strictly
before the start `τ` of that phase, so that the sample size of the ball of
`(s, a)` is the number of visits to `(s, a)` before `τ`. -/
noncomputable def mdpUCRL2ConfidenceSets {S A t : ℕ} [NeZero A] (n : ℕ) (δ : ℝ)
    (h : MDPTrajectory S A t) (s : Fin S) :
    Fin S → Fin A → Set (Fin S → ℝ) :=
  fun x a ↦
    mdpConfidenceSet (mdpObservedHistory h s) (mdpPhaseStart h t + 1) n δ x a

/-- The UCRL2 policy at horizon `n` and confidence level `δ` for the known
reward function `r` (L&S Section 38.5).  In each round it recomputes the start
of the current phase, forms the confidence balls from the transitions observed
before it, and plays the action assigned to the current state by the greedy
action map of the optimistic plan for those balls.  Since the space of
histories is finite the selection kernels are deterministic kernels, and the
policy depends only on `n`, `δ`, `r` and the observed history. -/
noncomputable def ucrl2Policy {S A : ℕ} [NeZero A] (n : ℕ) (δ : ℝ)
    (r : Fin S → Fin A → ℝ) : MDPPolicy S A where
  select t :=
    Kernel.deterministic
      (fun p : MDPTrajectory S A t × Fin S ↦
        mdpOptimisticActionMap r (mdpUCRL2ConfidenceSets n δ p.1 p.2) p.2)
      (measurable_of_countable _)
  markov _ := Kernel.isMarkovKernel_deterministic _

end BanditAlgorithm


