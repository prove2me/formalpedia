-- Prove2me | Theorems.Thm_MarkovEntanglement_rmab_index_policy_decomposition_error
-- name    : MarkovEntanglement.rmab_index_policy_decomposition_error
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-28T02:24:29.596314+00:00
-- url     : https://prove2.me/theorems/e3f34fcf-82bc-40b9-8af2-b23585ae9973
-- title:
--   Index policies have sublinear value decomposition error (Cor. 1)
-- statement:
--   Consider an $N$-agent restless multi-armed bandit. The agents are homogeneous: they share one local state space $S$, one pair of local transition kernels $P_0$ (idle) and $P_1$ (activate), and one pair of local rewards. At every step a budget forces exactly $M$ of the $N$ agents to be activated, where $M = \lfloor \alpha N \rfloor$ for a fixed activation fraction $\alpha \in (0,1)$.
--
--   Fix a priority index $\nu : S \to \mathbb{R}$ and let $\pi$ be an index policy for it: activate agents in descending order of the priority of their local state until the budget is exhausted, spreading the activation uniformly over the agents that share the marginal state. Let $m \in \Delta^{|S|}$ denote the configuration of the system, $m_x$ being the fraction of agents currently in local state $x$, and let $\varphi$ be the mean-field transition map of the configuration, $\varphi(m) = \mathbb{E}[m[t+1] \mid m[t] = m, \pi]$. Note that $\varphi$ does not depend on $N$, which is exactly why the budget must be a fixed fraction of $N$ rather than a fixed count, and why the constant below may be quantified before $N$.
--
--   Assume the two standard technical conditions on index policies:
--
--   1. **Uniform global attractor property (UGAP).** There is a point $m^\ast$ with $\varphi(m^\ast) = m^\ast$ that attracts every initial configuration, uniformly in the initial point: for every $\varepsilon > 0$ there is a $T$ with $\|\varphi^t(m) - m^\ast\|_\infty < \varepsilon$ for all $t \ge T$ and all $m \in \Delta^{|S|}$.
--   2. **Non-degeneracy.** At the fixed point $m^\ast$ some local state is served only fractionally, so the limiting policy genuinely randomises there.
--
--   Let $\mu^\pi_{1:N}$ be a strictly positive stationary occupancy measure of the induced chain, let the per-agent rewards be bounded by $r_{\max}$, let $\gamma \in [0,1)$ be the discount factor, let $Q^\pi_{1:N}$ be the joint $Q$-function (the Bellman fixed point of the joint chain with the summed reward), and let each $Q^\pi_i$ be the Bellman fixed point of an agent's own local transition matrix — one attaining that agent's measure of Markov entanglement — with that agent's own reward.
--
--   Then there is a constant $C$, independent of $N$, such that
--
--   $$\Big\| Q^\pi_{1:N} - \sum_{i=1}^N Q^\pi_i \Big\|_{\mu^\pi_{1:N}} \le \frac{4 C \gamma \sqrt{N}\, r_{\max}}{(1-\gamma)^2}.$$
--
--   The point of the result is that the right-hand side grows like $\sqrt{N}$ while the joint $Q$-function itself grows like $N$: the relative decomposition error vanishes as the system grows. This is the theoretical justification for the value decompositions used in large-scale restless-bandit applications.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Section 7.1, p. 24, Corollary 1

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

/-- Corollary 1 (Chen and Peng, "Multi-agent Markov Entanglement", arXiv:2506.02385v3,
Section 7.1, p. 24).  Consider an `N`-agent restless multi-armed bandit: homogeneous agents
sharing a local state space `S` and a pair of local kernels `P0, P1`, each agent choosing
between idle and activate, and a budget that activates a fixed fraction `α` of the agents at
every step.  Fix a priority index `ν` and let `π` be an index policy for the budget
`M = ⌊α * N⌋`.  Assume the explicit mean-field map of the configuration process at the
activation fraction `α` admits `m✦` as a uniform global attractor and is non-degenerate at
`m✦` — both properties of the limit model, quantified before `C` and before `N`.

Then there is a constant `C`, **independent of `N`**, such that the error of decomposing the
joint `Q`-function of the `N`-agent chain into a sum of per-agent local `Q`-functions is
bounded, in the occupancy-weighted norm, by

`‖Q^π_{1:N} − ∑ᵢ Q^π_i‖_μ ≤ 4 * C * γ * √N * r_max / (1 − γ)^2`.

The bound is **sublinear in `N`** while the joint `Q`-function itself is of order
`N * r_max / (1 − γ)`: the relative decomposition error vanishes as the system grows.  This
is what justifies the value decompositions used in practice for large-scale restless bandits.

The activated amount is the fraction `α` of `N` rather than a fixed count precisely because
the mean-field map `φ` is independent of `N` only when the activated fraction is held fixed;
`C` is quantified before `N` for the same reason. -/
theorem rmab_index_policy_decomposition_error
    {S : Type*} [Fintype S] [DecidableEq S]
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (hUGAP : IsUniformGlobalAttractor (meanFieldMap P0 P1 ν α) mstar)
    (hnd : IsNonDegenerateMeanField ν α mstar)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (rmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ), 0 < N →
        ∀ (π : (Fin N → S) → (Fin N → Bool) → ℝ),
          IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π →
          ∀ (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ),
            IsDist μ →
            IsExchangeableDist μ →
            IsStationary (inducedTransition
              (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ →
            ∀ (r : ∀ i : Fin N, S × Bool → ℝ), (∀ i x, |r i x| ≤ rmax) →
            ∀ (Q : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
              (Pl : ∀ i : Fin N, Matrix (S × Bool) (S × Bool) ℝ)
              (Qi : ∀ i : Fin N, S × Bool → ℝ),
              IsBellmanQ (inducedTransition
                (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
                (fun p => ∑ i, r i (p i)) γ Q →
              (∀ i, IsTransitionMatrix (Pl i)) →
              (∀ i, IsLocalTransitionN i (inducedTransition
                (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ (Pl i)) →
              (∀ i, IsBellmanQ (Pl i) (r i) γ (Qi i)) →
                muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
                  ≤ 4 * C * γ * Real.sqrt (N : ℝ) * rmax / (1 - γ) ^ 2 := by
  sorry

end MarkovEntanglement
