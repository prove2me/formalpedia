-- Prove2me | Definitions.Def_markov_entanglement
-- name    : markov_entanglement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-07-12T04:21:22.123695+00:00
-- url     : https://prove2.me/theorems/c48aa1ca-acdb-4908-9dde-08a2f69285e0
-- title:
--   Markov entanglement: two-agent MDPs, agent-wise TV distance, entanglement measure
-- statement:
--   Foundational definitions for the theory of Markov entanglement in two-agent Markov decision processes (Chen and Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385): finite-state transition matrices, stationary distributions, the local ('marginalized') transition of an agent induced by a joint transition and an occupancy measure (their Eq. 2), the Bellman fixed-point equation for Q-values, total variation distance between transition matrices (their Definition 4), the plain tensor product of two local transition matrices, separability of a joint transition matrix as a linear combination of tensor products of independent local transitions (their Definition 1 combined with the linear coefficient set of Section 3.3), the agent-wise total variation distance (their Definition 5), and the corresponding measure of Markov entanglement (their Eq. 4/5) as the infimum agent-wise total variation distance to the joint transition over candidate local transition matrices.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Sections 2, 2.1, 3, 5.1, 5.2 (Eq. 2, Definitions 1, 4, 5, Eq. 4, Eq. 5), pp. 6-16

import Mathlib

open scoped BigOperators

namespace MarkovEntanglement

variable {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]

/-- A finite-state (row-)transition matrix: nonnegative entries, each row sums to one. -/
def IsTransitionMatrix {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- A strictly positive probability distribution on a finite index set. -/
def IsPositiveDist {ι : Type*} [Fintype ι] (μ : ι → ℝ) : Prop :=
  (∀ i, 0 < μ i) ∧ ∑ i, μ i = 1

/-- `μ` is a stationary distribution of the transition matrix `P`. -/
def IsStationary {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) (μ : ι → ℝ) : Prop :=
  ∀ j, ∑ i, μ i * P i j = μ j

/-- The `A`-marginal of a joint distribution on `SA × SB`. -/
def marginalA (μ : SA × SB → ℝ) (a : SA) : ℝ := ∑ b : SB, μ (a, b)

/-- The `B`-marginal of a joint distribution on `SA × SB`. -/
def marginalB (μ : SA × SB → ℝ) (b : SB) : ℝ := ∑ a : SA, μ (a, b)

/-- `P_A` is agent `A`'s local ("marginalized") transition matrix induced by the joint
transition `P_AB` under the occupancy measure `μ`, matching Eq. (2): the local transition at
`(sA, aA)` is the projection of the global transition weighted by the conditional occupancy
measure of agent `B`'s state-action pairs. Written multiplicatively (both sides scaled by the
`A`-marginal of `μ`) to avoid dividing by a marginal that could vanish outside its support. -/
def IsLocalTransitionA (P_AB : Matrix (SA × SB) (SA × SB) ℝ) (μ : SA × SB → ℝ)
    (P_A : Matrix SA SA ℝ) : Prop :=
  ∀ a a', marginalA μ a * P_A a a' =
    ∑ b : SB, μ (a, b) * (∑ b' : SB, P_AB (a, b) (a', b'))

/-- Agent `B`'s local transition matrix, symmetric to `IsLocalTransitionA`. -/
def IsLocalTransitionB (P_AB : Matrix (SA × SB) (SA × SB) ℝ) (μ : SA × SB → ℝ)
    (P_B : Matrix SB SB ℝ) : Prop :=
  ∀ b b', marginalB μ b * P_B b b' =
    ∑ a : SA, μ (a, b) * (∑ a' : SA, P_AB (a, b) (a', b'))

/-- `Q` is the fixed point of the Bellman equation for transition matrix `P`, local reward `r`,
and discount factor `γ`: `Q = r + γ * P * Q`. -/
def IsBellmanQ {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) (r : ι → ℝ) (γ : ℝ) (Q : ι → ℝ) :
    Prop :=
  ∀ i, Q i = r i + γ * ∑ j, P i j * Q j

/-- Total variation distance between two transition matrices (Definition 4): the maximum,
over rows, of the total variation distance between the corresponding row distributions. -/
noncomputable def tvDist {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℝ) : ℝ :=
  ⨆ i : ι, (1 / 2) * ∑ j, |P i j - Q i j|

/-- The plain (non-Kronecker) tensor product of two local transition matrices, i.e. the entry
of `P_A ⊗ P_B` at `((a, b), (a', b'))`. -/
def tensorProd (P_A : Matrix SA SA ℝ) (P_B : Matrix SB SB ℝ) : Matrix (SA × SB) (SA × SB) ℝ :=
  fun p q => P_A p.1 q.1 * P_B p.2 q.2

/-- A joint transition matrix on `SA × SB` is separable (Definition 1, generalized to the
linear-coefficient set `P_SEP` of §3.3) if it is a finite linear combination, with coefficients
summing to one, of tensor products of transition matrices; otherwise it is entangled. -/
def IsSeparable (P : Matrix (SA × SB) (SA × SB) ℝ) : Prop :=
  ∃ (K : ℕ) (x : Fin K → ℝ) (PAj : Fin K → Matrix SA SA ℝ) (PBj : Fin K → Matrix SB SB ℝ),
    (∀ k, IsTransitionMatrix (PAj k)) ∧ (∀ k, IsTransitionMatrix (PBj k)) ∧
    (∑ k, x k = 1) ∧
    P = ∑ k, x k • tensorProd (PAj k) (PBj k)

/-- Agent-wise total variation distance w.r.t. agent `A` (Definition 5): compares the
`B`-marginal of the joint transition's row at `(sA, aA, sB, aB)` against a candidate local
transition `P_A` at `(sA, aA)`, maximized over all joint state-action pairs. -/
noncomputable def agentTVDistA (P : Matrix (SA × SB) (SA × SB) ℝ) (P_A : Matrix SA SA ℝ) : ℝ :=
  ⨆ p : SA × SB, (1 / 2) * ∑ j : SA, |(∑ b : SB, P p (j, b)) - P_A p.1 j|

/-- Agent-wise total variation distance w.r.t. agent `B`, symmetric to `agentTVDistA`. -/
noncomputable def agentTVDistB (P : Matrix (SA × SB) (SA × SB) ℝ) (P_B : Matrix SB SB ℝ) : ℝ :=
  ⨆ p : SA × SB, (1 / 2) * ∑ j : SB, |(∑ a : SA, P p (a, j)) - P_B p.2 j|

/-- Measure of Markov entanglement w.r.t. agent `A` under the agent-wise total variation
distance (Eq. (5)): the infimum, over candidate local transitions for `A`, of the agent-wise
total variation distance to the joint transition. -/
noncomputable def entanglementA (P : Matrix (SA × SB) (SA × SB) ℝ) : ℝ :=
  ⨅ PA : {M : Matrix SA SA ℝ // IsTransitionMatrix M}, agentTVDistA P PA.1

/-- Measure of Markov entanglement w.r.t. agent `B`, symmetric to `entanglementA`. -/
noncomputable def entanglementB (P : Matrix (SA × SB) (SA × SB) ℝ) : ℝ :=
  ⨅ PB : {M : Matrix SB SB ℝ // IsTransitionMatrix M}, agentTVDistB P PB.1

end MarkovEntanglement


