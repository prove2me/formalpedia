-- Prove2me | Definitions.Def_markov_entanglement_multi_atv
-- name    : markov_entanglement_multi_atv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-07T16:11:04.695214+00:00
-- url     : https://prove2.me/theorems/920601b5-2369-465e-8d6d-b613904e0b9b
-- title:
--   Agent-wise TV distance for $N$ agents, and the agent-wise entanglement measure as a function of the distance
-- statement:
--   Completes the distance/norm correspondence of Chen and Peng for $N$ agents.
--
--   Definition 14 defines the measure of Markov entanglement as $\mathcal{E}(P_{1:N}) = \min_{P \in \mathcal{P}_{SEP}} d(P_{1:N}, P)$ with the distance $d$ left abstract, and Table 1 (p. 20) records that each choice of $d$ carries its own norm on the value-decomposition error: the unweighted total variation and agent-wise total variation distances control the error in $\|\cdot\|_\infty$, while their $\mu$-weighted counterparts control it in $\|\cdot\|_\mu$.
--
--   The existing multi-agent file realises that abstraction only at the *separable-set* level, as `entanglementWith`. The measures the theory actually uses are the *agent-wise* ones of Eq. (4)/(5), whose infimum ranges over local transitions for a single agent rather than over separable joint matrices — a different minimand, so the agent-wise measure is not an instance of `entanglementWith`. As a result the distance is baked into `entanglementN` (the $\mu$-weighted agent-wise TV distance), and the unweighted agent-wise distance exists only in the two-agent file.
--
--   This file supplies the two missing pieces. First, the **agent-wise total variation distance** for $N$ agents,
--   $$\|P_{1:N} - P_i\|_{ATV_i} = \sup_{s,a} \tfrac12 \sum_{t} \big| P_i^{\text{marg}}(t \mid s,a) - P_i(t \mid s_i,a_i)\big|,$$
--   the supremum-based counterpart of the $\mu$-weighted version and the $N$-agent form of the two-agent `agentTVDistA`/`agentTVDistB`. Second, the **agent-wise measure of Markov entanglement with respect to an arbitrary distance**, the agent-wise analogue of `entanglementWith`, defined as the infimum of $d(P_{1:N}, P_i)$ over transition matrices $P_i$ on agent $i$'s local space.
--
--   Instantiating the second with the $\mu$-weighted agent-wise distance recovers the existing `entanglementN` definitionally, so nothing downstream changes; instantiating it with the new unweighted distance gives the measure that controls the decomposition error in the supremum norm.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Definition 5 (p. 15), Eq. (4)/(5), Definition 14 (p. 40) and Table 1 (p. 20)

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators

namespace MarkovEntanglement

/-! ## Completing the distance/norm table

Definition 14 defines the measure of Markov entanglement as `min over separable P of
d(P₁:ₙ, P)` with the distance `d` left abstract, and Table 1 (p. 20) records that each
choice of `d` carries its own norm on the decomposition error: the unweighted TV and
agent-wise TV distances give bounds in `‖·‖_∞`, their `μ`-weighted counterparts give
bounds in `‖·‖_μ`.

`Def_markov_entanglement_multi` realises that abstraction at the *separable-set* level, as
`entanglementWith`.  The measures the theory actually uses, however, are the *agent-wise*
ones of Eq. (4)/(5), whose infimum ranges over local transitions `Matrix (S i) (S i)` for a
single agent rather than over separable joint matrices — a different minimand, so
`entanglementN` is not an instance of `entanglementWith`.  Consequently the distance is
baked into `entanglementN` (μ-weighted ATV) and into `entanglementA`/`entanglementB`
(unweighted ATV, two agents only).

Two additions complete the picture:

* `agentTVDistN` — the unweighted agent-wise TV distance for `N` agents, the one empty cell
  of the table.  It is the direct analogue of the two-agent `agentTVDistA`/`agentTVDistB`,
  which is what makes the sup-norm two-agent results work.
* `agentEntanglementWith` — the agent-wise counterpart of `entanglementWith`, so that the
  agent-wise measure of entanglement also takes the distance as an input.

The existing `entanglementN` is recovered definitionally, so nothing downstream changes:
`entanglementN i μ P = agentEntanglementWith i (muAgentTVDistN i μ) P` holds by `rfl`. -/

variable {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The **agent-wise total variation distance** for agent `i` (Definition 5, `N`-agent
form): the total variation distance between the joint transition marginalised onto agent
`i` and a candidate local transition, maximised over joint state-action pairs rather than
averaged with weights `μ`.  The supremum-based counterpart of `muAgentTVDistN`, and the
`N`-agent form of `agentTVDistA`/`agentTVDistB`. -/
noncomputable def agentTVDistN (i : Fin N) (P : Matrix (Joint S) (Joint S) ℝ)
    (Pi : Matrix (S i) (S i) ℝ) : ℝ :=
  ⨆ p : Joint S, (1 / 2) * ∑ t : S i, |marginalN i P p t - Pi (p i) t|

/-- The **agent-wise measure of Markov entanglement** for agent `i` with respect to an
arbitrary distance `d` between the joint transition and a candidate local transition:
how far the joint transition sits from being generated by a single local transition for
`i`, measured by `d`.  The agent-wise analogue of `entanglementWith`, following the source
in leaving the distance abstract (Eq. (4)/(5)).

Instantiate `d` with `muAgentTVDistN i μ` to recover `entanglementN` (definitionally), or
with `agentTVDistN i` for the unweighted measure that controls the error in `‖·‖_∞`. -/
noncomputable def agentEntanglementWith (i : Fin N)
    (d : Matrix (Joint S) (Joint S) ℝ → Matrix (S i) (S i) ℝ → ℝ)
    (P : Matrix (Joint S) (Joint S) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ Pi : Matrix (S i) (S i) ℝ, IsTransitionMatrix Pi ∧ r = d P Pi}

/-- The existing `μ`-weighted measure is the case `d = muAgentTVDistN i μ`, so adding the
abstraction changes nothing downstream. -/
theorem entanglementN_eq_agentEntanglementWith (i : Fin N) (μ : Joint S → ℝ)
    (P : Matrix (Joint S) (Joint S) ℝ) :
    entanglementN i μ P = agentEntanglementWith i (muAgentTVDistN i μ) P := rfl

end MarkovEntanglement


