-- Prove2me | Theorems.Thm_MarkovMixing_path_coupling
-- name    : MarkovMixing.path_coupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:25:02.533941+00:00
-- url     : https://prove2.me/theorems/62387e61-4728-4473-9b03-82d9296419b2
-- title:
--   Path coupling (Bubley--Dyer)
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$, and let a connected graph $G$ on $V$ with symmetric edge lengths $\ell\ge1$ be given. The **path metric** $\rho(x,y)$ is the least total $\ell$-length of a walk from $x$ to $y$ in $G$; a **coupling** of two distributions is a joint distribution on pairs with those marginals; and the **transportation distance** $\rho_K(\mu,\nu)$ is the infimum of $\mathbb E_q[\rho]$ over couplings $q$ of $\mu,\nu$.
--
--   The theorem (**path coupling**, Bubley–Dyer; Theorem 14.6 of Levin–Peres–Wilmer) asserts: if for some rate $\alpha>0$ every *edge* $\{x,y\}$ of $G$ admits a coupling $q$ of the one-step distributions $P(x,\cdot)$ and $P(y,\cdot)$ contracting in expectation,
--   $$\sum_{u,v}q(u,v)\,\rho(u,v)\;\le\;e^{-\alpha}\,\ell(x,y),$$
--   then one step of the chain contracts the transportation metric between **arbitrary** distributions at the same rate:
--   $$\rho_K(\mu P,\;\nu P)\;\le\;e^{-\alpha}\,\rho_K(\mu,\nu)\qquad\text{for all distributions }\mu,\nu.$$
--
--   This is the theorem that turns the coupling method into a local computation: contraction needs to be checked only across single edges of any convenient graph structure, and the metric machinery propagates it along paths to all pairs of states — no global coupling construction required.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 14.2, Theorem 14.6, pp. 191-192

import Definitions.Def_mm_transport
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MarkovMixing

/-- **Theorem 14.6, path coupling** (Bubley–Dyer; LPW): if for every edge
`{x,y}` of a connected graph structure on the state space there is a
coupling of the one-step distributions contracting the path metric by
`e^{-α}`, then one step of the chain contracts the transportation metric of
*arbitrary* distributions by `e^{-α}`. -/
theorem path_coupling {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (G : SimpleGraph V) (hconn : G.Connected)
    (ℓ : V → V → ℝ) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x)
    (α : ℝ) (hα : 0 < α)
    (hedge : ∀ x y : V, G.Adj x y →
      ∃ q : V × V → ℝ, IsCoupling (rowDist P 1 x) (rowDist P 1 y) q ∧
        ∑ p : V × V, q p * pathMetric G ℓ p.1 p.2 ≤ Real.exp (-α) * ℓ x y)
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    transportDist (pathMetric G ℓ) (Matrix.vecMul μ P) (Matrix.vecMul ν P) ≤
      Real.exp (-α) * transportDist (pathMetric G ℓ) μ ν := by
  sorry

end MarkovMixing
