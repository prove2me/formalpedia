-- Prove2me | Theorems.Thm_KServer_exists_cruel_sequence
-- name    : KServer.exists_cruel_sequence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T01:08:46.313673+00:00
-- url     : https://prove2.me/theorems/f8bb6b05-fe49-4fe4-afab-ac5c9039bf7a
-- title:
--   The cruel adversary: requesting the point the algorithm leaves uncovered
-- statement:
--   Work in a metric space $M$ with $k$ servers, and fix a set $P\subseteq M$ of exactly $k+1$ distinct points. Let $B$ be a **lazy** online $k$-server algorithm, that is, one that serves each request by moving a single server directly onto the requested point:
--   $$B(\ell\cdot r)\;=\;B(\ell)\bigl[i\mapsto r\bigr]\qquad\text{for some server }i.$$
--
--   Since $B$ commands only $k$ servers while $P$ has $k+1$ points, at every moment at least one point of $P$ carries no server. The **cruel adversary** always requests such an uncovered point. Because a lazy algorithm answers by moving one server from the point it vacates onto the requested point, the distance it travels is exactly the distance between the current request and the point it has just vacated — which the adversary can then make the next request.
--
--   **Statement.** There is a constant $E$, depending on $B$ and $P$ but *not* on the request sequence, such that for every $n$ there is a request sequence $\sigma=(r_1,\dots,r_n)$ with
--   1. all requests inside the chosen subspace, $r_j\in P$ for every $j$;
--   2. consecutive requests distinct, $r_j\neq r_{j+1}$ for every $j$; and
--   3. the total distance between consecutive requests bounded by the online cost,
--   $$\sum_{j=1}^{n-1} d(r_j,r_{j+1})\;\le\;\mathrm{cost}_B(\sigma)+E.$$
--
--   **Role.** This is the adversarial half of the Manasse--McGeoch--Sleator lower bound, isolated from the offline bookkeeping. It says the cruel sequence forces the online algorithm to pay, up to an additive constant, the whole length of the walk traced by the requests themselves. Two consequences follow immediately and are exactly what the lower bound consumes: since consecutive requests are distinct points of the finite set $P$, each term of the sum is at least the minimal separation of $P$, so the online cost grows linearly in $n$ and can be made arbitrarily large; and the same walk length is the quantity that the $k$ offline algorithms of the lower bound pay in total. The additive constant $E$ absorbs the finitely many steps at which the point vacated by the moving server is not usable as the next request — namely a server's very first move, which may start from a point outside $P$, and a move that vacates a point still occupied by a second server; a server moves for the first time at most $k$ times, and collisions between servers can only be resolved, never created, so both kinds of step occur at most $k$ times in total, whatever the length of the sequence.
--
--   **Formalization Note** Consecutive pairs of the request list are taken as `σ.zip σ.tail`, so the displayed sum is the sum of `dist p.1 p.2` over that list of pairs; for a list of length $n$ it has $n-1$ entries, and is empty when $\sigma$ is empty or a singleton. Laziness is expressed with `Function.update`, and is supplied by the companion reduction lemma `KServer.exists_lazy_algorithm`.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, preprint https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf, Section 3.1, proof of Theorem 1: "at any point in time, there is only one point of the metric space that the online algorithm does not cover and the adversary should request it next. By repeating this enough times, the online cost can become arbitrarily high."; originally Manasse--McGeoch--Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, https://doi.org/10.1016/0196-6774(90)90003-W, Theorem 6 (and Corollary 7).

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem exists_cruel_sequence (k : ℕ) (M : Type) [MetricSpace M]
    (P : Finset M) (hP : P.card = k + 1) (B : OnlineAlgorithm k M)
    (hlazy : ∀ (l : List M) (r : M), ∃ i : Fin k,
      B.conf (l ++ [r]) = Function.update (B.conf l) i r) :
    ∃ E : ℝ, ∀ n : ℕ, ∃ σ : List M,
      σ.length = n ∧
      (∀ r ∈ σ, r ∈ P) ∧
      (∀ p ∈ σ.zip σ.tail, p.1 ≠ p.2) ∧
      ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum ≤ B.cost σ + E := by sorry

end KServer
