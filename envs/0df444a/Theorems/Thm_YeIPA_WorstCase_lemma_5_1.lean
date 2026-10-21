-- Prove2me | Theorems.Thm_YeIPA_WorstCase_lemma_5_1
-- name    : YeIPA.WorstCase.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:32.307042+00:00
-- url     : https://prove2.me/theorems/44283cd3-bcd0-4d4a-9e12-e1e1ed9e3a94
-- title:
--   Lemma 5.1 — the rank-one updating scaling stays within 10% of the iterate, and Σ|Iᵗ| ≤ 11√n Σ‖(Dᵗ⁻¹)⁻¹(xᵗ − xᵗ⁻¹)‖
-- statement:
--   Let $x^0,x^1,\dots\in\mathbb R^n$ be positive vectors, let $D^t=\operatorname{diag}(d^t)$ be the rank-one updating scaling of Section 5.1 ($d^0=x^0$; for $t\ge1$, $d^t_j=d^{t-1}_j$ if $1/1.1\le d^{t-1}_j/x^t_j\le1.1$ and $d^t_j=x^t_j$ otherwise), and let $I^t=\{i: d^{t-1}_i/x^t_i\notin[1/1.1,1.1]\}$ be the set of coordinates updated at iteration $t$. Then
--   $$\|(D^t)^{-1}(x^t-d^t)\|_\infty\le0.1\quad\text{for every } t=0,1,\dots,$$
--   and, for every $k\ge0$,
--   $$\sum_{t=1}^k|I^t|\le 11\sqrt n\sum_{t=1}^k\|(D^{t-1})^{-1}(x^t-x^{t-1})\|,$$
--   where $\|\cdot\|$ is the Euclidean norm and $|I|$ the number of elements of $I$.
--
--   The total number of rank-one updates over $k$ iterations is thus bounded by the total scaled movement of the iterates; when each scaled step has norm at most $\alpha$, it is at most $11k\alpha\sqrt n$, which is how the section saves a factor $\sqrt n$ in arithmetic operations.
--
--   **Formalization Note** The iterates are an arbitrary sequence `x : ℕ → Fin n → ℝ` with every coordinate positive; the lemma uses no other property of the algorithm. $(D^t)^{-1}v$ is written componentwise as $v_j/d^t_j$. $I^t$ has $d^{t-1}$ in the numerator, as the proof uses it; the printed definition has $d^t$, under which $I^t$ would always be empty (see the definition `YeIPA.WorstCase.RankOneUpdate`).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 149, Lemma 5.1

import Mathlib
import Definitions.Def_YeIPA_WorstCase_RankOneUpdate

namespace YeIPA.WorstCase

/-- Lemma 5.1 (Ye 1997, p. 149). Let `x⁰, x¹, … ∈ ℝⁿ` be positive, `dᵗ` the rank-one updating
scaling of p. 148 and `Iᵗ` its update sets. Then `‖(Dᵗ)⁻¹(xᵗ − dᵗ)‖_∞ ≤ 0.1` for every
`t = 0, 1, …`, and for every `k`,
`∑_{t=1}^k |Iᵗ| ≤ 11√n ∑_{t=1}^k ‖(Dᵗ⁻¹)⁻¹(xᵗ − xᵗ⁻¹)‖` (Euclidean norm). -/
theorem lemma_5_1 {n : ℕ} (x : ℕ → Fin n → ℝ) (hx : ∀ t j, 0 < x t j) :
    (∀ t : ℕ, normInf (fun j => (x t j - scaling x t j) / scaling x t j) ≤ 0.1) ∧
    ∀ k : ℕ, (∑ t ∈ Finset.Icc 1 k, ((updateSet x t).card : ℝ)) ≤
      11 * Real.sqrt n *
        ∑ t ∈ Finset.Icc 1 k, norm2 (fun j => (x t j - x (t - 1) j) / scaling x (t - 1) j) := by sorry

end YeIPA.WorstCase
