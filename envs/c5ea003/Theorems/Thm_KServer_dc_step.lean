-- Prove2me | Theorems.Thm_KServer_dc_step
-- name    : KServer.dc_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T04:19:07.679799+00:00
-- url     : https://prove2.me/theorems/424cd9a2-a730-4cb0-8235-da59e298d712
-- title:
--   The Double Coverage step pays for itself
-- statement:
--   Work on the real line with $k\ge1$ servers, and let the algorithm's configuration $x$ be kept in sorted order. Attach to a configuration $x$ of the algorithm and a configuration $y$ of the adversary the **Double Coverage potential**
--
--   $$\Phi(x,y)\;=\;k\cdot\sum_{i=1}^{k}\bigl|x_i-y_i\bigr|\;+\;\sum_{i,j}\max\bigl(x_j-x_i,\,0\bigr),$$
--
--   whose first term is the cost of matching the two sorted configurations and whose second term is the *spread* $\sum_{i<j}(x_j-x_i)$ of the algorithm's servers.
--
--   **Statement.** For every sorted configuration $x$ and every request $r$ there is a sorted configuration $x'$ which covers $r$ and which is *amortized free*: against every sorted adversary configuration $y$ that also covers $r$,
--
--   $$\mathrm{moveCost}(x,x')\;+\;\Phi(x',y)\;\le\;\Phi(x,y).$$
--
--   **Role.** This is the whole of the Chrobak–Karloff–Payne–Vishwanathan analysis of the Double Coverage algorithm, compressed into a single step. Double Coverage serves a request lying between two of its servers by moving *both* neighbours toward it at equal speed until one arrives, and serves a request outside the span of its servers by moving the extreme server to it. The point of the potential is that this rule pays for itself: the spread term releases exactly what the two moving servers cost, and the matching term does not increase, because the adversary has a server on the request and therefore at least one of the two movers travels toward its partner.
--
--   Given this step lemma, $k$-competitiveness on the line follows by summing over the request sequence: each request contributes at most the potential it releases, while an adversary move of length $t$ raises the potential by at most $k\,t$, so the algorithm's total cost is at most $k$ times the adversary's plus the initial potential.
--
--   **Formalization Note** The spread is written as $\sum_{i,j}\max(x_j-x_i,0)$, which for a sorted $x$ equals $\sum_{i<j}(x_j-x_i)$ and is manifestly nonnegative, so the potential is bounded below without any extra hypothesis. `moveCost` is the shared model's movement cost, the sum over servers of the distance each travels. Sortedness of both configurations is stated as `Monotone`; the adversary's configuration may always be taken sorted, since re-sorting a schedule never increases its cost.
-- source:
--   Chrobak--Karloff--Payne--Vishwanathan, New results on server problems, SIAM J. Discrete Math. 4 (1991) 172-181, https://doi.org/10.1137/0404017 -- the theorem that the Double Coverage algorithm is k-competitive on the real line, and the potential k*(matching cost) + (spread) used to prove it. See also E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, Section 3.2 (description of Double Coverage).

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem dc_step (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℝ) (hx : Monotone x) (r : ℝ) :
    ∃ x' : Fin k → ℝ, Monotone x' ∧ (∃ i, x' i = r) ∧
      ∀ y : Fin k → ℝ, Monotone y → (∃ m, y m = r) →
        moveCost x x'
            + ((k : ℝ) * (∑ i, |x' i - y i|) + ∑ i, ∑ j, max (x' j - x' i) 0)
          ≤ (k : ℝ) * (∑ i, |x i - y i|) + ∑ i, ∑ j, max (x j - x i) 0 := by sorry

end KServer
