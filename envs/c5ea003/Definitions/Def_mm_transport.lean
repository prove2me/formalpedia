-- Prove2me | Definitions.Def_mm_transport
-- name    : mm_transport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T17:24:29.486486+00:00
-- url     : https://prove2.me/theorems/91b417ce-0bdb-4f95-9b27-9192eb35a1c2
-- title:
--   The transportation metric and path metrics
-- statement:
--   This file provides the metric structure behind the path coupling method, following Chapter 14 of Levin–Peres–Wilmer, together with the colorings chain that the method's flagship application runs on.
--
--   **The transportation metric.** For a cost function $\rho$ on pairs of states of a finite space $V$ and two mass functions $\mu,\nu$ on $V$, the **transportation distance** (Kantorovich distance) is the cheapest expected cost of carrying $\mu$ onto $\nu$:
--   $$\rho_K(\mu,\nu)=\inf\Bigl\{\sum_{x,y}\rho(x,y)\,q(x,y)\;:\;q\ \text{a coupling of}\ \mu\ \text{and}\ \nu\Bigr\},$$
--   the couplings being the probability distributions on $V\times V$ with marginals $\mu$ and $\nu$. That this infimum is attained and satisfies the triangle inequality are theorems of the mission, not part of the definition.
--
--   **Path metrics.** Given a graph structure $G$ on the state space and edge lengths $\ell$, the **length of a walk** is the sum of $\ell$ over its consecutive steps, and the **path metric** is the cheapest way to travel:
--   $$\rho(x,y)=\inf\bigl\{\ \text{length of}\ w\;:\;w\ \text{a walk from}\ x\ \text{to}\ y\ \text{in}\ G\ \bigr\}.$$
--   Path coupling contracts this metric on edges and lets the graph structure propagate the contraction to all pairs.
--
--   **The Glauber dynamics on proper colorings.** A $q$-coloring of the vertices of a graph is **proper** when adjacent vertices receive distinct colors. The uniform distribution on proper colorings is presented as a mass function on *all* colorings (value $1/N$ on each of the $N$ proper colorings, $0$ elsewhere), and the **Glauber dynamics on proper colorings** is the single-site heat-bath chain of Mission II for this distribution, restricted to the proper colorings: pick a uniform vertex and re-sample its color uniformly among the colors legal there.
--
--   **Conventions.** The infima are real `sInf`s with the junk value $0$ on empty families (no coupling exists when $\mu,\nu$ are not genuine distributions; no walk exists between different components), and division is total with $r/0=0$; the theorems supply the hypotheses under which the junk cases are excluded.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 14, Sections 14.1-14.3 (and Section 3.3.1), pp. 189-193

import Definitions.Def_mm_mixing
import Definitions.Def_mm_mcmc
import Definitions.Def_mm_coupling
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
The transportation (Kantorovich) metric and path coupling, following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 14.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **transportation metric**
`ρ_K(μ,ν) = inf {E ρ(X,Y) : (X,Y) a coupling of μ and ν}` (LPW §14.1,
Eqs. (14.2)–(14.3)). -/
def transportDist (ρ : V → V → ℝ) (μ ν : V → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
    e = ∑ p : V × V, ρ p.1 p.2 * q p}

/-- The length of a walk in a graph with edge lengths `ℓ` (LPW §14.2). -/
def walkLength {G : SimpleGraph V} (ℓ : V → V → ℝ) {x y : V} (w : G.Walk x y) : ℝ :=
  (w.darts.map fun d => ℓ d.toProd.1 d.toProd.2).sum

/-- The **path metric** induced by edge lengths `ℓ` on a graph `G`
(LPW §14.2, Eq. (14.5)). -/
def pathMetric (G : SimpleGraph V) (ℓ : V → V → ℝ) (x y : V) : ℝ :=
  sInf {r : ℝ | ∃ w : G.Walk x y, r = walkLength ℓ w}

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]

/-- The uniform distribution on proper `q`-colorings, viewed as a
distribution on all of `Fin q^V` (zero off the proper colorings). -/
def properColoringDist (G : SimpleGraph Vv) [DecidableRel G.Adj] (q : ℕ) :
    (Vv → Fin q) → ℝ :=
  fun c =>
    if IsProperColoring G c then
      ((Fintype.card {c : Vv → Fin q // IsProperColoring G c} : ℝ))⁻¹
    else 0

/-- The **Glauber dynamics on proper `q`-colorings** (LPW §3.3.1, §14.3),
as a chain on the set of proper colorings. -/
def coloringGlauber (G : SimpleGraph Vv) [DecidableRel G.Adj] (q : ℕ) :
    Matrix {c : Vv → Fin q // IsProperColoring G c}
      {c : Vv → Fin q // IsProperColoring G c} ℝ :=
  subChain (glauber (properColoringDist G q)) fun c => IsProperColoring G c

end

end MarkovMixing


