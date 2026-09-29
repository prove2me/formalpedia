-- Prove2me | Theorems.Thm_E_sign_monomial
-- name    : E_sign_monomial
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T21:11:25.035818+00:00
-- url     : https://prove2.me/theorems/af297db0-7e70-45d1-b0c1-25116cd2df89
-- statement:
--   **Sign-cube (Rademacher) orthogonality.** Encode a $\pm 1$ sign assignment on the finite index set $\iota = \{1,\dots,n_1\}\times\{1,\dots,n_2\}$ by the subset $\varepsilon \subseteq \iota$ of coordinates carrying $+1$ (the complement carries $-1$): the sign of coordinate $c$ is $\sigma_c = \mathbf{1}[c\in\varepsilon] - \mathbf{1}[c\notin\varepsilon]$. Averaging the sign monomial $\prod_c \sigma_c^{\,m_c}$ uniformly over all $2^N$ assignments ($N = |\iota|$, weight $2^{-N}$ each) yields
--
--   $$\mathbb{E}\Big[\textstyle\prod_c \sigma_c^{\,m_c}\Big] = \begin{cases} 1 & \text{if every } m_c \text{ is even},\\ 0 & \text{otherwise.}\end{cases}$$
--
--   This is the classical Rademacher orthogonality $\mathbb{E}[\prod_c \varepsilon_c^{m_c}] = \prod_c \mathbb{E}[\varepsilon_c^{m_c}]$ with $\mathbb{E}[\varepsilon^m]=\mathbf{1}[m\text{ even}]$, the sign-survival step of the moment method (Buchholz, Math. Ann. 319 (2001) §2). The left-hand sum is over all subsets $\varepsilon$ of the coordinate set, i.e. the uniform expectation over the discrete cube $\{\pm1\}^N$.
-- source:
--   Buchholz, Operator Khintchine inequality in non-commutative probability, Math. Ann. 319 (2001) 1-16, section 2; CR2009 (arXiv:0805.4471) section 6.1 Lemma 6.1

import Mathlib
open scoped BigOperators

theorem E_sign_monomial {n1 n2 : Nat} (mult : (Fin n1 × Fin n2) → ℕ) :
    ((1 : ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
        ∑ eps : Finset (Fin n1 × Fin n2),
          ∏ c : (Fin n1 × Fin n2),
            (if c ∈ eps then (1 : ℝ) else -1) ^ (mult c)
      = if (∀ c, Even (mult c)) then 1 else 0 := by sorry
