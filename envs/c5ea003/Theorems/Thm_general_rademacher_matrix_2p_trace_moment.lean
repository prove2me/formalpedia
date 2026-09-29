-- Prove2me | Theorems.Thm_general_rademacher_matrix_2p_trace_moment
-- name    : general_rademacher_matrix_2p_trace_moment
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-24T03:18:11.010559+00:00
-- url     : https://prove2.me/theorems/b6bf4feb-9ec8-413b-ad44-b912cb272862
-- statement:
--   **General Rademacher matrix $2p$-th trace moment bound (Tropp 2015, Theorem 4.1 / eq. (4.9)).** Let $\{H_c\}_{c\in\iota}$ be a finite family of real symmetric (Hermitian) $d\times d$ matrices, and let $X_\varepsilon=\sum_c \varepsilon_c H_c$ where $\varepsilon$ ranges over the Rademacher sign cube (encoded as the subset $eps\subseteq\iota$ of $+1$ coordinates, each configuration weighted by $2^{-|\iota|}$). Write $V=\sum_c H_c^2$ for the matrix variance proxy and let $\mathrm{normV}$ be any upper bound on the eigenvalues of $V$. Then the symmetric Rademacher average of the trace of the $(2p)$-th power satisfies $$\mathbb{E}_\varepsilon\big[\operatorname{tr}\big(X_\varepsilon^{2p}\big)\big]\ \le\ \frac{(2p)!}{2^{p}\,p!}\;\mathrm{normV}^{\,p}\;d,$$ where the prefactor $\frac{(2p)!}{2^p p!}=(2p-1)!!$ is the odd double factorial — the $2p$-th moment of a standard Gaussian. This is the elementary (non-NCMI) Rademacher recursion underlying the noncommutative Khintchine inequality: it is established by the summation-by-parts / GM--AM trace argument of Tropp's Sections 2 and 4 (Facts 2.2 and 2.4, eq. (4.6)), giving the one-step bound $\mathbb{E}[\operatorname{tr} X^{2k}]\le(2k-1)\,\mathrm{normV}\,\mathbb{E}[\operatorname{tr} X^{2(k-1)}]$ and iterating from $\mathbb{E}[\operatorname{tr} X^0]=d$.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1506.04711, Sections 2 and 4 (Theorem 4.1 / eq. (4.9), Facts 2.2, 2.4, eq. (4.6)).

import Mathlib
open Matrix
open scoped BigOperators

theorem general_rademacher_matrix_2p_trace_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (H : ι → Matrix (Fin d) (Fin d) ℝ)
    (hHerm : ∀ c, (H c).IsHermitian)
    (normV : ℝ) (hnormVnn : 0 ≤ normV)
    (hVHerm : (∑ c : ι, H c * H c).IsHermitian)
    (hnormV : ∀ i, hVHerm.eigenvalues i ≤ normV)
    (p : ℕ) :
    (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι)
        * Matrix.trace ((∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p)))
      ≤ ((Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ)))
          * normV ^ p * (d : ℝ) := by sorry
