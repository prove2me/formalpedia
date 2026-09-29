-- Prove2me | Definitions.Def_mm_mixing
-- name    : mm_mixing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T15:14:20.157696+00:00
-- url     : https://prove2.me/theorems/286835c8-1e0c-4de1-9726-21caad66cd39
-- title:
--   Total variation distance, mixing time, and couplings
-- statement:
--   This file defines the yardsticks by which the whole series measures convergence, following Chapter 4 of Levin–Peres–Wilmer.
--
--   **Total variation distance.** For two mass functions $\mu,\nu$ on a finite state space $V$,
--   $$\|\mu-\nu\|_{TV}=\max_{A\subseteq V}\,\bigl|\mu(A)-\nu(A)\bigr|,$$
--   the largest discrepancy the two assign to a single event. Note there is deliberately no factor $\tfrac12$ here: the identity $\|\mu-\nu\|_{TV}=\tfrac12\sum_x|\mu(x)-\nu(x)|$ is one of the mission's theorems, not part of the definition.
--
--   **Distance to stationarity.** The row $P^t(x,\cdot)$ of the $t$-th matrix power is the distribution of the chain at time $t$ started at $x$. The worst-case distance to the stationary distribution and the worst pairwise distance are
--   $$d(t)=\max_{x\in V}\,\bigl\|P^t(x,\cdot)-\pi\bigr\|_{TV},\qquad \bar d(t)=\max_{x,y\in V}\,\bigl\|P^t(x,\cdot)-P^t(y,\cdot)\bigr\|_{TV}.$$
--
--   **Mixing time.** For a threshold $\varepsilon$,
--   $$t_{\mathrm{mix}}(\varepsilon)=\min\{t\in\mathbb N: d(t)\le\varepsilon\},\qquad t_{\mathrm{mix}}=t_{\mathrm{mix}}(1/4),$$
--   the first time the chain is within $\varepsilon$ of stationarity from every starting state. As an infimum in $\mathbb N$ it takes the junk value $0$ if no such time exists; monotonicity of $d$ is a theorem, not an assumption.
--
--   **Couplings.** A **coupling** of two mass functions $\mu$ and $\nu$ is a probability distribution $q$ on ordered pairs $V\times V$ whose marginals are $\mu$ and $\nu$:
--   $$\sum_{y}q(x,y)=\mu(x)\ \ \forall x,\qquad \sum_{x}q(x,y)=\nu(y)\ \ \forall y.$$
--   Couplings are the combinatorial device behind the characterization $\|\mu-\nu\|_{TV}=\min_q\,q\{(x,y):x\ne y\}$ proved in this mission.
--
--   **Inverse distribution.** For an increment measure $\mu$ on a group, $\hat\mu(g)=\mu(g^{-1})$ — the increment law of the reversed walk, used for random walks on groups such as card shuffles.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 4, Sections 4.1-4.6, pp. 47-56

import Definitions.Def_mm_basic
import Mathlib.Data.Real.Archimedean

/-!
Total variation distance, distance to stationarity, and mixing time,
following Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 4.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **total variation distance**
`‖μ − ν‖_TV = max_{A ⊆ Ω} |μ(A) − ν(A)|` (LPW §4.1, Eq. (4.1)). -/
def tvDist (μ ν : V → ℝ) : ℝ :=
  ⨆ A : Finset V, |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|

/-- The row `P^t(x, ·)`: the distribution after `t` steps started at `x`. -/
def rowDist (P : Matrix V V ℝ) (t : ℕ) (x : V) : V → ℝ :=
  fun y => (P ^ t) x y

/-- `d(t) = max_x ‖P^t(x,·) − π‖_TV`, the worst-case distance to the
stationary distribution after `t` steps (LPW §4.4, Eq. (4.22)). -/
def distStationary (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) : ℝ :=
  ⨆ x : V, tvDist (rowDist P t x) π

/-- `d̄(t) = max_{x,y} ‖P^t(x,·) − P^t(y,·)‖_TV` (LPW §4.4, Eq. (4.23)). -/
def distPairs (P : Matrix V V ℝ) (t : ℕ) : ℝ :=
  ⨆ p : V × V, tvDist (rowDist P t p.1) (rowDist P t p.2)

/-- The **mixing time** `t_mix(ε) = min {t : d(t) ≤ ε}` (LPW §4.5,
Eq. (4.32)). -/
def mixingTime (P : Matrix V V ℝ) (π : V → ℝ) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | distStationary P π t ≤ ε}

/-- `t_mix = t_mix(1/4)` (LPW §4.5, Eq. (4.33)). -/
def tMix (P : Matrix V V ℝ) (π : V → ℝ) : ℕ :=
  mixingTime P π (1 / 4)

/-- A **coupling** of two distributions `μ` and `ν`: a distribution on pairs
whose first marginal is `μ` and second marginal is `ν` (LPW §4.2). -/
def IsCoupling (μ ν : V → ℝ) (q : V × V → ℝ) : Prop :=
  IsDist q ∧ (∀ x : V, ∑ y, q (x, y) = μ x) ∧ ∀ y : V, ∑ x, q (x, y) = ν y

/-- The **inverse distribution** `μ̂(g) = μ(g⁻¹)` of an increment distribution
on a group; the walk with increments `μ̂` is the time reversal of the walk
with increments `μ` (LPW §4.6). -/
def invDist {G : Type*} [Group G] (μ : G → ℝ) : G → ℝ :=
  fun g => μ g⁻¹

end

end MarkovMixing


