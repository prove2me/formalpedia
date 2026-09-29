-- Prove2me | Definitions.Def_UCRL2ConfidenceSets
-- name    : UCRL2ConfidenceSets
-- status  : Definition
-- author  : @Grace
-- created : 2026-08-02T20:41:30.943276+00:00
-- url     : https://prove2.me/theorems/5c620271-a878-4026-99f8-4dafd76b7235
-- title:
--   The confidence sets of UCRL2
-- statement:
--   A learner interacting with a finite MDP observes the whole trajectory, so from it alone it can count how often each state-action pair has been played, how often each transition has been observed, and hence form an empirical estimate of every transition row together with an $\ell^1$ ball around it.  This file records those constructions and the *good event* that the true rows lie in every ball.
--
--   Write $h$ for a trajectory of $t$ rounds, recording the state and the action of each round.
--
--   - $N_k(s,a)$, `mdpVisitCount`, is the number of rounds strictly before time $k$ at which $(s,a)$ was played.
--   - `mdpTransitionCount` counts the transitions $(s,a)\to s'$ observed strictly before time $k$.  Only rounds $i$ with $i+1<k$ contribute: the state following the last recorded round has not been seen yet.  Consequently the number of transitions observed out of a pair before time $k$ is the number of visits to it before time $k-1$, and it is this smaller count, `mdpObservedCount`, that is the honest sample size of the empirical row.
--   - `mdpEmpiricalRow` is $\hat P_a(s,\cdot)$, the observed transitions out of $(s,a)$ normalised by that sample size; before any transition out of $(s,a)$ has been seen the estimate is the point mass at $s$, so that the value is a probability vector for every history.
--   - `mdpConfidenceRadius` is $\sqrt{14S\log(2SAn/\delta)/\max(1,N)}$, the radius used at horizon $n$ and confidence level $\delta$ after $N$ observations.
--   - `mdpConfidenceSet` is the set of probability vectors within $\ell^1$ distance `mdpConfidenceRadius` of the empirical row, the radius taken at the number of transitions actually observed.
--   - `mdpConfidenceGoodEvent` is the event that at every time $k\le n$ and every pair $(s,a)$ the true transition row of $M$ lies in that ball.
--
--   Nothing here mentions the algorithm that uses these estimates: the same balls serve any optimism-based method.  The regret analysis of UCRL2 is a deterministic argument on the good event, and the statistical half of its proof bounds the probability of the complement.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5, printed pp. 524-525 / PDF pp. 533-534, Eq. (38.13) and Lemma 38.8; after Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010), Section 3, Eq. (3).

import Definitions.Def_FiniteMDPLearning
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The confidence sets of UCRL2

Lattimore and Szepesvari, *Bandit Algorithms* (CUP 2020), Section 38.5, after
Jaksch, Ortner and Auer, *Near-optimal regret bounds for reinforcement
learning*, JMLR 11 (2010), Section 3.

A learner interacting with a finite MDP observes the whole trajectory, so from
it -- and from it alone -- it can count how often each state-action pair has
been played, how often each transition has been observed, and hence form an
empirical estimate of every transition row together with an `L¹` ball around it
whose radius shrinks with the number of observations.  This file records those
constructions and the *good event* that the true transition rows lie in every
ball.  Nothing here mentions the algorithm that uses them: the same estimates
and balls serve any optimism-based method.

The trajectory of `t` rounds records the state and the action of each round, so
the transition out of round `i` is observed exactly when round `i + 1` is still
part of it.  Consequently the number of transitions observed out of a pair
before time `k` is the number of *visits* to it before time `k - 1`, and it is
this smaller count -- the honest sample size of the empirical row -- that the
confidence radius uses.
-/

open Finset
open scoped NNReal

namespace BanditAlgorithm

variable {S A : ℕ}

/-- The state reached after round `i`, when round `i + 1` is still part of the
recorded trajectory; `none` when the transition out of round `i` has not been
observed. -/
def mdpSuccessor {S A t : ℕ} (h : MDPTrajectory S A t) (i : Fin t) : Option (Fin S) :=
  if hlt : i.val + 1 < t then some (h ⟨i.val + 1, hlt⟩).1 else none

/-- `N_k(s, a)`, the number of rounds strictly before time `k` at which the pair
`(s, a)` was played. -/
def mdpVisitCount {S A t : ℕ} (h : MDPTrajectory S A t) (k : ℕ)
    (s : Fin S) (a : Fin A) : ℕ :=
  (univ.filter fun i : Fin t ↦ i.val < k ∧ h i = (s, a)).card

/-- The number of transitions `(s, a) → s'` observed strictly before time `k`.
Only rounds `i` with `i + 1 < k` contribute: the state following the last
recorded round has not been seen yet. -/
def mdpTransitionCount {S A t : ℕ} (h : MDPTrajectory S A t) (k : ℕ)
    (s : Fin S) (a : Fin A) (s' : Fin S) : ℕ :=
  (univ.filter fun i : Fin t ↦
    i.val + 1 < k ∧ h i = (s, a) ∧ mdpSuccessor h i = some s').card

/-- The total number of transitions observed out of `(s, a)` before time `k`:
the sample size of the empirical row `mdpEmpiricalRow`. -/
def mdpObservedCount {S A t : ℕ} (h : MDPTrajectory S A t) (k : ℕ)
    (s : Fin S) (a : Fin A) : ℕ :=
  ∑ s', mdpTransitionCount h k s a s'

/-- The empirical transition row `P̂_a(s, ·)` formed from the transitions
observed before time `k`.  Before any transition out of `(s, a)` has been seen
the estimate is the point mass at `s`, so that the value is a probability
vector for every history. -/
noncomputable def mdpEmpiricalRow {S A t : ℕ} (h : MDPTrajectory S A t) (k : ℕ)
    (s : Fin S) (a : Fin A) : Fin S → ℝ :=
  if mdpObservedCount h k s a = 0 then fun s' ↦ if s' = s then 1 else 0
  else fun s' ↦ (mdpTransitionCount h k s a s' : ℝ) / (mdpObservedCount h k s a : ℝ)

/-- The radius of the `L¹` confidence ball around an empirical transition row
built from `N` observed transitions, at horizon `n` and confidence level `δ`
(Jaksch--Ortner--Auer, Section 3):
`√(14 S log(2 S A n / δ) / max(1, N))`. -/
noncomputable def mdpConfidenceRadius (S A n : ℕ) (δ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (14 * S * Real.log (2 * S * A * n / δ) / ((max 1 N : ℕ) : ℝ))

/-- The confidence ball of transition rows for the pair `(s, a)` at time `k`:
the probability vectors within `L¹` distance `mdpConfidenceRadius` of the
empirical row, the radius being taken at the number of transitions actually
observed out of `(s, a)`. -/
def mdpConfidenceSet {S A t : ℕ} (h : MDPTrajectory S A t) (k n : ℕ) (δ : ℝ)
    (s : Fin S) (a : Fin A) : Set (Fin S → ℝ) :=
  {p | (∀ s', 0 ≤ p s') ∧ ∑ s', p s' = 1 ∧
    ∑ s', |p s' - mdpEmpiricalRow h k s a s'|
      ≤ mdpConfidenceRadius S A n δ (mdpObservedCount h k s a)}

/-- The good event of UCRL2: at every time `k ≤ n` the true transition rows of
`M` lie in the confidence balls built from the trajectory.  The regret analysis
is a deterministic argument on this event, and the statistical half of the proof
bounds the probability of its complement. -/
def mdpConfidenceGoodEvent {S A : ℕ} (M : FiniteMDP S A) (n : ℕ) (δ : ℝ) :
    Set (MDPTrajectory S A n) :=
  {h | ∀ k ≤ n, ∀ (s : Fin S) (a : Fin A),
    (fun s' ↦ ((M.P s a s' : ℝ))) ∈ mdpConfidenceSet h k n δ s a}

end BanditAlgorithm


