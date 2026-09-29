-- Prove2me | Theorems.Thm_weight_count_with_subset
-- name    : weight_count_with_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-09T02:11:19.261568+00:00
-- url     : https://prove2.me/theorems/94bfd770-24b5-4271-b09f-40ccc1e7dceb
-- statement:
--   **Counting weight-$t$ Boolean vectors containing a fixed subset.**
--
--   For every $S \subseteq \{1, \ldots, b\}$ and every $t \in \{0, 1, \ldots, b\}$, the number of Boolean vectors $y \in \{0,1\}^b$ with Hamming weight exactly $t$ such that $S \subseteq \mathrm{supp}(y) := \{i : y_i = 1\}$ equals
--   $$\#\!\left\{ y \in \{0,1\}^b \;:\; |y| = t, \, S \subseteq \mathrm{supp}(y) \right\}
--   \;=\; \begin{cases} \binom{b - |S|}{t - |S|} & \text{if } |S| \le t, \\ 0 & \text{otherwise.} \end{cases}$$
--
--   Proof via the bijection $y \leftrightarrow \mathrm{supp}(y)$ between $\{0,1\}^b$ and $2^{\{1,\ldots,b\}}$, which restricts to a bijection between weight-$t$ Boolean vectors containing $S$ and $t$-element subsets containing $S$, then a further bijection $T \leftrightarrow T \setminus S$ to $(t - |S|)$-subsets of $\{1,\ldots,b\} \setminus S$ (when $|S| \le t$).
-- source:
--   Folklore — counting Boolean vectors of fixed Hamming weight containing a fixed subset. Standard combinatorial fact, used as a sub-leaf in the Minsky-Papert symmetrization argument (Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313).

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

/-!
# Counting weight-`t` Boolean vectors containing a fixed subset

For every `S ⊆ Fin b` and every `t ≤ b`, the number of Boolean vectors
`y : Fin b → Bool` with Hamming weight exactly `t` such that `S` is contained
in the true-set of `y` is `(b - |S|).choose (t - |S|)` when `|S| ≤ t`, and
`0` otherwise.

Sub-leaf used in the Minsky-Papert symmetrization argument: each multi-index
`m` in the support of a multivariate polynomial contributes a count of
weight-`t` Boolean inputs whose true-set contains `m.support`.
-/

theorem weight_count_with_subset
    {b : ℕ} (S : Finset (Fin b)) (t : ℕ) :
    ((Finset.univ : Finset (Fin b → Bool)).filter
        (fun y => ((Finset.univ : Finset (Fin b)).filter (fun i => y i = true)).card = t
                    ∧ S ⊆ (Finset.univ : Finset (Fin b)).filter (fun i => y i = true))).card
      = if S.card ≤ t then (b - S.card).choose (t - S.card) else 0 := by sorry
