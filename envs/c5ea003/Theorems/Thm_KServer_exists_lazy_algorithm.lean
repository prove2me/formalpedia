-- Prove2me | Theorems.Thm_KServer_exists_lazy_algorithm
-- name    : KServer.exists_lazy_algorithm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T01:08:21.850048+00:00
-- url     : https://prove2.me/theorems/39afec83-2a07-413d-bfc0-5684a036fa7b
-- title:
--   Laziness reduction: every online algorithm is dominated by a lazy one
-- statement:
--   Fix a metric space $M$ and a number $k$ of servers. A *deterministic online $k$-server algorithm* $A$ assigns to every finite request list $\ell$ the configuration $A(\ell)$ of the $k$ servers after serving $\ell$, subject to the service constraint that some server stands on $r$ immediately after the list $\ell$ followed by a request $r$. Its cost on a request sequence $\sigma=(r_1,\dots,r_n)$ is the total distance travelled along the induced trajectory,
--   $$\mathrm{cost}_A(\sigma)\;=\;\sum_{j=1}^{n}\mathrm{moveCost}\bigl(A(\sigma_{\le j-1}),A(\sigma_{\le j})\bigr).$$
--
--   Call an algorithm $B$ **lazy** if it serves each request by moving one single server directly onto the requested point and leaves every other server where it stood: for every list $\ell$ and every point $r$ there is a server $i$ with
--   $$B(\ell\cdot r)\;=\;B(\ell)\bigl[i\mapsto r\bigr].$$
--
--   **Statement.** For every online $k$-server algorithm $A$ there exists a lazy online $k$-server algorithm $B$ with the same initial configuration, $B(\varepsilon)=A(\varepsilon)$, whose cost never exceeds that of $A$:
--   $$\mathrm{cost}_B(\sigma)\;\le\;\mathrm{cost}_A(\sigma)\qquad\text{for every request sequence }\sigma.$$
--
--   **Role.** This is the standard *"without loss of generality the algorithm is lazy"* reduction of competitive analysis. A non-lazy algorithm may reposition servers in anticipation of future requests — the Double Coverage algorithm is the classical example — but in a metric space such anticipatory moves can be postponed until they become necessary, and merging the postponed moves can only shorten the total distance travelled, by the triangle inequality. Every argument that reasons about *the point an algorithm vacates when it serves a request* needs this reduction, because only a lazy algorithm is guaranteed to vacate exactly one point and to place its server exactly on the request. Stating it once as a standalone result makes it citable by all of them, in particular by the Manasse--McGeoch--Sleator lower bound and by upper-bound analyses on trees and on the line.
--
--   **Formalization Note** Laziness is expressed with `Function.update`: `B.conf (l ++ [r]) = Function.update (B.conf l) i r` says that the new configuration agrees with the old one off the single index `i`, whose value is the request `r`. Nothing is assumed about $k$: when $k=0$ and $M$ is nonempty the type `OnlineAlgorithm 0 M` is empty, so the statement holds vacuously.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, preprint https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf, Section 2 (Definitions), paragraph on laziness and memorylessness: "every non-lazy algorithm can be simulated by a lazy algorithm by postponing the non-lazy moves until they become necessary (and thus lazy) ... because of the triangle inequality, this can only lower the cost"; the reduction originates with Manasse--McGeoch--Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, https://doi.org/10.1016/0196-6774(90)90003-W, Section 2.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem exists_lazy_algorithm (k : ℕ) (M : Type) [MetricSpace M]
    (A : OnlineAlgorithm k M) :
    ∃ B : OnlineAlgorithm k M,
      B.conf [] = A.conf [] ∧
      (∀ σ : List M, B.cost σ ≤ A.cost σ) ∧
      (∀ (l : List M) (r : M), ∃ i : Fin k,
        B.conf (l ++ [r]) = Function.update (B.conf l) i r) := by sorry

end KServer
