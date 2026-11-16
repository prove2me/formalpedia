-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_Supplement_lemma_3_4
-- name    : ZamirInversion581.Mult.Supplement.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:50:39.894059+00:00
-- url     : https://prove2.me/theorems/b697f5b5-a727-4ed8-b8bc-03aba23ab7ce
-- title:
--   Lemma 3.4 — weighted rank-profile separation
-- statement:
--   Let $F$ be any finite field of order $q$, let $n,m\in\mathbb N$, let $0<\eta\le1$, and let $b_0,\ldots,b_n\in[0,1]^m$. Write $\pi_j=\Pr_X[\operatorname{rank}X=n-j]$ for uniform $X\in F^{n\times n}$, and set $J=\lceil\log_q(100/\eta)\rceil$. Assume $J<n$ and
--   $$
--   \sum_{j=1}^n\pi_j\|b_j-b_0\|_\infty\ge\eta.
--   $$
--   For every $1\le d\le n$ and every $d$-dimensional subspace $V\le F^n$, define $g_V(j)=\mathbb E_W[b_{j+\dim(V\cap W)}]$, where $W$ is uniform over subspaces of dimension $n-j$. Then
--   $$
--   \exists\,0\le j\le J:\quad\|g_V(j)-b_j\|_\infty>\eta/100.
--   $$
--   The constants are independent of the field and of $m$. This gives the shared separation statement for the invertibility, rank, and determinant reductions.
--
--   Differences from the source:
--   - encoding: maximum norm on vectors and the distribution K_{j,d} → finite maxima including zero and an explicit d-dimensional subspace V, with W uniform in its Grassmannian; reason: the equivalent subspace description is stated immediately before display (1); dimension zero has norm zero
--   - encoding: indices 0 through n and real base-q logarithm → Fin (n+1), a zero extension used only in total definitions, and the natural ceiling of log(100/η)/log(q); reason: all indices in the conclusion are in range, since j≤J<n and dim(V∩W)≤n-j; the logarithm is positive
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.14, Lemma 3.4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Supplement_Statistics

set_option autoImplicit false

namespace ZamirInversion581.Mult.Supplement

/-- Lemma 3.4, pp.14–15: all constants are literal and uniform in the field and vector dimension. -/
theorem lemma_3_4 (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n m : ℕ) (η : ℝ) (b : Fin (n + 1) → Fin m → ℝ)
    (hη : 0 < η) (hη₁ : η ≤ 1)
    (hb : ∀ j i, 0 ≤ b j i ∧ b j i ≤ 1)
    (hn : cutoff F η < n)
    (hsep : η ≤ ∑ j ∈ Finset.Icc 1 n,
      corankMass F n j * maxNorm (profileAt b j - profileAt b 0)) :
    ∀ d : ℕ, 1 ≤ d → d ≤ n → ∀ V : Submodule F (Fin n → F),
      Module.finrank F V = d →
      ∃ j : ℕ, j ≤ cutoff F η ∧
        η / 100 < maxNorm (maskedProfile b V j - profileAt b j) := by sorry

end ZamirInversion581.Mult.Supplement
