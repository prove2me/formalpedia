-- Prove2me | Theorems.Thm_MarkovMixing_lazy_return_probability_connected
-- name    : MarkovMixing.lazy_return_probability_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T23:31:21.408495+00:00
-- url     : https://prove2.me/theorems/d88faeeb-ab77-4742-bcba-164ce2ce1251
-- title:
--   Theorem 17.17 -- return probabilities of the lazy walk
-- statement:
--   Let $G$ be a finite simple graph on a non-empty vertex set $V$, **connected** (any vertex is reachable from any other along edges) and with every degree positive. Write $\deg(v)$ for the number of neighbours of $v$, $|E|$ for the number of edges, and $\Delta=\max_v\deg(v)$ for the maximal degree. Simple random walk on $G$ jumps from $x$ to a uniformly chosen neighbour, $P(x,y)=\deg(x)^{-1}$ when $x\sim y$ and $0$ otherwise; its **lazy** version $\tilde P=\tfrac12(I+P)$ stays put with probability $\tfrac12$ at each step. On a connected graph the walk has the stationary distribution $\pi(x)=\deg(x)/2|E|$.
--
--   The theorem (Theorem 17.17 of Levin–Peres–Wilmer) asserts that the return probabilities of the lazy walk converge to $\pi$ at a rate controlled by the maximal degree alone: for every vertex $x$ and every time $t\ge1$,
--   $$\Bigl|\tilde P^{\,t}(x,x)-\frac{\deg(x)}{2|E|}\Bigr|\;\le\;\frac{\sqrt2\,\Delta^{5/2}}{\sqrt t}.$$
--
--   The bound does not mention the size of the graph — only its maximal degree — which is what makes it useful for large sparse graphs, and it is proved by the evolving-set method of this mission rather than by any spectral estimate. (The dependence on $\Delta$ is not optimal; LPW remark that $c_1\Delta/\sqrt t$ also holds.)
--
--   *A note on the connectedness hypothesis.* LPW write $\pi(x)$ for the stationary distribution of the walk, which on a connected graph is $\deg(x)/2|E|$. The expression $\deg(x)/2|E|$ is of course a perfectly good number on any graph, and that is exactly what makes the omission of connectedness a falsehood rather than a vacuity: on a disconnected graph the walk started at $x$ never leaves the component of $x$, so its return probabilities converge to that component's stationary mass, which is strictly larger. On two disjoint edges every degree and the maximal degree equal $1$ and $|E|=2$; the lazy walk matrix is idempotent, so $\tilde P^{\,t}(x,x)=\tfrac12$ for every $t\ge1$ while $\deg(x)/2|E|=\tfrac14$, and at $t=100$ the claim would read $\tfrac14\le\sqrt2/10$. Positivity of the degrees rules out isolated vertices but not disconnection; it is kept alongside connectedness because a connected graph may still be the single vertex, where all three of $\deg(x)$, $\Delta$ and $|E|$ vanish.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 17.5, Theorem 17.17, Eq. (17.31), p. 239

import Definitions.Def_mm_martingale
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MarkovMixing

/-- **Theorem 17.17** (LPW): for the lazy random walk on a connected graph of
maximal degree `Δ`, the return probabilities satisfy
`|P^t(x,x) − π(x)| ≤ √2 Δ^{5/2} / √t`.

The graph is hypothesized connected.  LPW write `π(x)` for the stationary
distribution of the walk, which is `deg(x)/2|E|`; that identification needs
connectedness, since on a disconnected graph the walk started at `x` never
leaves the component of `x` and its return probabilities converge to the
component's stationary mass, which is strictly larger.  The formula
`deg(x)/2|E|` is of course defined for every graph, which is what makes the
omission a falsehood rather than a vacuity: on two disjoint edges every degree
and the maximal degree are `1` and `|E| = 2`, the lazy walk matrix is
idempotent, so `P^t(x,x) = 1/2` for all `t ≥ 1` while `deg(x)/2|E| = 1/4`, and
at `t = 100` the claim would read `1/4 ≤ √2/10`.  Positivity of the degrees
rules out isolated vertices but not disconnection; it is kept because
connectedness alone still admits the one-vertex graph, where every degree,
`Δ` and `|E|` vanish. -/
theorem lazy_return_probability_connected {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (x : V) (t : ℕ) (ht : 0 < t) :
    |((lazy (graphWalk G)) ^ t) x x -
        (G.degree x : ℝ) / (2 * G.edgeFinset.card)| ≤
      Real.sqrt 2 * (G.maxDegree : ℝ) ^ ((5 : ℝ) / 2) / Real.sqrt t := by
  sorry

end MarkovMixing
