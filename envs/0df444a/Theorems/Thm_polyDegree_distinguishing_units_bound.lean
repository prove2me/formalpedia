-- Prove2me | Theorems.Thm_polyDegree_distinguishing_units_bound
-- name    : polyDegree_distinguishing_units_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-08T21:25:45.825919+00:00
-- url     : https://prove2.me/theorems/c215ba9a-fd5a-4721-9ea3-f013f0e78058
-- statement:
--   **Polynomial-degree lower bound for unit-distinguishing Boolean functions.**
--
--   For every Boolean function $g : \{0,1\}^b \to \{0,1\}$ with $b \ge 1$ that satisfies
--   $$g(\vec{0}) = 0 \qquad \text{and} \qquad g(e_i) = 1 \text{ for every } i \in \{1, \ldots, b\},$$
--   where $e_i$ is the standard basis vector with the $i$-th bit set, the polynomial degree obeys
--   $$b \;\le\; 2 \cdot \deg(g)^2.$$
--
--   This is the core polynomial-method estimate that converts a sensitivity/degree gap into a block-sensitivity bound (Nisan–Szegedy 1994, Theorem 6). The proof goes through Minsky–Papert symmetrization and a Markov-type derivative bound:
--
--   1. Take a multivariate real polynomial $p$ of total degree $d := \deg(g)$ representing $g$ on the cube.
--   2. Symmetrize $p$ over Hamming-weight classes to obtain a univariate $Q$ of degree $\le d$ with $Q(0) = 0$, $Q(1) = 1$, and $|Q(t)| \le 1$ for every integer $t \in \{0, \ldots, b\}$.
--   3. By the mean-value theorem, some $c \in (0, 1)$ satisfies $Q'(c) = 1$.
--   4. By Markov's brothers inequality on the integer grid (Ehlich–Zeller / Coppersmith–Rivlin), $|Q'(c)| \le 2 d^2 / b$ for every $c \in [0, b]$.
--   5. Combine: $1 \le 2 d^2 / b$, hence $b \le 2 d^2$.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree

/-!
# Boolean polynomial degree bound for unit-distinguishing functions

Core combinatorial step in the Nisan–Szegedy proof of `bs(f) ≤ 2 · deg(f)²`:
if a Boolean function `g : {0,1}ᵇ → {0,1}` distinguishes the all-zeros input
from each of the `b` standard basis vectors `eᵢ`, then its polynomial degree
is at least `√(b/2)` — equivalently, `b ≤ 2 · deg(g)²`.

The reduction from "block sensitivity" to this lemma is the L1 sketch
(`sketch_tal_block_sensitivity_bound`); the proof of this lemma itself
is the L2 sketch, which decomposes via Minsky–Papert symmetrization and
Markov's brothers inequality.
-/

/-- **Polynomial degree of a unit-distinguishing Boolean function.**
For every `g : {0,1}ᵇ → {0,1}` (with `b ≥ 1`) such that
`g(0) = false` and `g(eᵢ) = true` for every basis vector `eᵢ`,
the polynomial degree satisfies `b ≤ 2 · deg(g)²`. -/

theorem polyDegree_distinguishing_units_bound
    {b : ℕ} (hb : 1 ≤ b) (g : BoolFunc b)
    (h_zero : g (fun _ => false) = false)
    (h_units : ∀ i : Fin b, g (Function.update (fun _ => false) i true) = true) :
    b ≤ 2 * (polyDegree g)^2 := by sorry
