-- Prove2me | Theorems.Thm_MarkovMixing_lamplighter_relaxation
-- name    : MarkovMixing.lamplighter_relaxation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:28:47.938254+00:00
-- url     : https://prove2.me/theorems/4a30f1cf-c5d5-431c-a3ae-7498ebb2acd4
-- title:
--   $t_{\mathrm{rel}}(G^\ast)\asymp t_{\mathrm{hit}}(G)$ for lamplighter chains
-- statement:
--   Let $(G_n)$ be any sequence of connected graphs with $|V_n|\to\infty$. Over each $G_n$ two chains are compared. The **base walk** is the lazy simple random walk on $G_n$ (hold with probability $\tfrac12$, else move to a uniform neighbour), with **maximal hitting time** $t_{\mathrm{hit}}(G_n)=\max_{x,y}\mathbb E_x(\tau_y)$, the worst expected time to reach one vertex from another (Mission VI). The **lamplighter chain** $G_n^\ast$ has states (lamp configuration in $\{0,1\}^{V_n}$, lamplighter position); one step randomizes the lamp at the current position, moves the lamplighter one step of the base walk, and randomizes the lamp at the new position. Among the eigenvalues of a chain (real $\lambda$ with $Pf=\lambda f$, $f\ne0$), $\lambda_\star$ is the largest absolute value of an eigenvalue $\ne1$, and the **relaxation time** is $t_{\mathrm{rel}}=(1-\lambda_\star)^{-1}$ (Mission VII).
--
--   The theorem (Theorem 19.1 of Levin–Peres–Wilmer) asserts: there are constants $c_1,c_2>0$ such that for all sufficiently large $n$,
--   $$c_1\,t_{\mathrm{hit}}(G_n)\;\le\;t_{\mathrm{rel}}(G_n^\ast)\;\le\;c_2\,t_{\mathrm{hit}}(G_n).$$
--
--   The lamplighter's slowest mode is governed by the base walk's worst hitting time: to decorrelate, the lamplighter must revisit far-away lamps. The lower bound tests the variational characterization of the gap (Mission VII) with an eigenfunction built from an unvisited-vertex indicator; the upper bound is a coupling-contraction estimate. Together with the companion theorem ($t_{\mathrm{mix}}\asymp t_{\mathrm{cov}}$), the lamplighter ties the hitting, cover, relaxation, and mixing parameters of the whole series into one family.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 19.2, Theorem 19.1, Eq. (19.2), p. 258

import Definitions.Def_mm_cutoff

namespace MarkovMixing

/-- **Theorem 19.1** (LPW): the relaxation time of the lamplighter chain is
comparable to the maximal hitting time of the underlying lazy walk: there
are constants `c₁, c₂ > 0` such that for all sufficiently large `n`,
`c₁ t_hit(G_n) ≤ t_rel(G_n⁎) ≤ c₂ t_hit(G_n)`. -/
theorem lamplighter_relaxation {Vf : ℕ → Type*} [∀ n, Fintype (Vf n)]
    [∀ n, DecidableEq (Vf n)] [∀ n, Nonempty (Vf n)]
    (G : ∀ n, SimpleGraph (Vf n)) [∀ n, DecidableRel (G n).Adj]
    (hconn : ∀ n, (G n).Connected)
    (hcard : Filter.Tendsto (fun n => Fintype.card (Vf n))
      Filter.atTop Filter.atTop) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c₁ * hitTimeMax (lazy (graphWalk (G n))) ≤
        relaxationTime (lamplighter (G n)) ∧
      relaxationTime (lamplighter (G n)) ≤
        c₂ * hitTimeMax (lazy (graphWalk (G n))) := by
  sorry

end MarkovMixing
