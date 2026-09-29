-- Prove2me | Theorems.Thm_MarkovMixing_lamplighter_mixing
-- name    : MarkovMixing.lamplighter_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:29:00.006524+00:00
-- url     : https://prove2.me/theorems/957d874e-779d-4e21-809f-5e3bae33a679
-- title:
--   $t_{\mathrm{mix}}(G^\ast)\asymp t_{\mathrm{cov}}(G)$ for lamplighter chains
-- statement:
--   Let $(G_n)$ be any sequence of connected graphs with $|V_n|\to\infty$. The **base walk** on $G_n$ is the lazy simple random walk (hold with probability $\tfrac12$, else move to a uniform neighbour); its **cover time** $t_{\mathrm{cov}}(G_n)$ is the worst, over starting vertices, expected time to have visited every vertex (Mission VI). The **lamplighter chain** $G_n^\ast$ has states (lamp configuration in $\{0,1\}^{V_n}$, lamplighter position); one step randomizes the lamp at the current position, moves the lamplighter one base-walk step, and randomizes the lamp at the new position; its stationary distribution is uniform lamps times the base walk's stationary distribution. The **mixing time** $t_{\mathrm{mix}}(G_n^\ast)$ is the first $t$ at which the worst-case total variation distance $\max_s\|P^t(s,\cdot)-\pi\|_{TV}$ drops to $1/4$, with $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$.
--
--   The theorem (Theorem 19.2 of Levin–Peres–Wilmer) asserts: there are constants $c_1,c_2>0$ such that for all sufficiently large $n$,
--   $$c_1\,t_{\mathrm{cov}}(G_n)\;\le\;t_{\mathrm{mix}}(G_n^\ast)\;\le\;c_2\,t_{\mathrm{cov}}(G_n).$$
--
--   The lamp configuration looks uniform only once (essentially) every lamp has been touched, so the lamplighter mixes exactly when the base walk has covered the graph — the cleanest theorem converting cover times into mixing times. The upper bound couples two lamplighters after a cover-time's worth of steps; the lower bound shows that before a constant fraction of the cover time, the set of unvisited lamps betrays the starting configuration (via the separation–total-variation relation of this mission).
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 19.3, Theorem 19.2, Eq. (19.7), p. 260

import Definitions.Def_mm_cutoff

namespace MarkovMixing

/-- **Theorem 19.2** (LPW): the mixing time of the lamplighter chain is
comparable to the cover time of the underlying lazy walk: there are
constants `c₁, c₂ > 0` such that for all sufficiently large `n`,
`c₁ t_cov(G_n) ≤ t_mix(G_n⁎) ≤ c₂ t_cov(G_n)`. -/
theorem lamplighter_mixing {Vf : ℕ → Type*} [∀ n, Fintype (Vf n)]
    [∀ n, DecidableEq (Vf n)] [∀ n, Nonempty (Vf n)]
    (G : ∀ n, SimpleGraph (Vf n)) [∀ n, DecidableRel (G n).Adj]
    (hconn : ∀ n, (G n).Connected)
    (hcard : Filter.Tendsto (fun n => Fintype.card (Vf n))
      Filter.atTop Filter.atTop) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c₁ * coverTimeMax (lazy (graphWalk (G n))) ≤
        (tMix (lamplighter (G n)) (lamplighterStationary (G n)) : ℝ) ∧
      (tMix (lamplighter (G n)) (lamplighterStationary (G n)) : ℝ) ≤
        c₂ * coverTimeMax (lazy (graphWalk (G n))) := by
  sorry

end MarkovMixing
