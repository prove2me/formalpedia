-- Prove2me | Theorems.Thm_mme_dwz_boundary_histogram_factorial_cancellation
-- name    : mme_dwz_boundary_histogram_factorial_cancellation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:39:58.269038+00:00
-- url     : https://prove2.me/theorems/6713e588-945d-48ef-9689-5bffed94d1b4
-- title:
--   Exact compatibility-ratio identity from boundary and residual histograms
-- statement:
--   Let $K,L$ be finite sets. For each coarse grade $k\in K$, let $B_k$ and $P_k$ be finite boundary and positive label sets. Let $b_{kc\ell}$ be boundary split counts, $r_{k\ell}$ residual positive split counts, $\gamma_{k\ell}$ total fine counts, and $p_{kc}$ positive outer counts, all in $\mathbb N$. Assume
--   $$
--   \gamma_{k\ell}=r_{k\ell}+\sum_{c\in B_k}b_{kc\ell},
--   \qquad
--   \sum_{\ell\in L}r_{k\ell}=\sum_{c\in P_k}p_{kc}.
--   $$
--   Write $N_k=\sum_\ell\gamma_{k\ell}$, $N^+_k=\sum_\ell r_{k\ell}$, and $n_{kc}=\sum_\ell b_{kc\ell}$ for boundary labels. Define the exact integer multinomial products
--   $$
--   R=\prod_{k,\ell}\frac{\gamma_{k\ell}!}{r_{k\ell}!\prod_{c\in B_k}b_{kc\ell}!},
--   \qquad
--   Q=\prod_k\frac{N^+_k!}{\prod_{c\in P_k}p_{kc}!},
--   $$
--   $$
--   B_{\rm typ}=\prod_k\frac{N_k!}{\prod_\ell\gamma_{k\ell}!},
--   \qquad
--   D_Z=\prod_k\frac{N_k!}{(\prod_{c\in B_k}n_{kc}!)(\prod_{c\in P_k}p_{kc}!)},
--   $$
--   $$
--   B_{\rm comp}=
--   \left(\prod_k\prod_{c\in B_k}\frac{n_{kc}!}{\prod_\ell b_{kc\ell}!}\right)
--   \left(\prod_k\frac{N^+_k!}{\prod_\ell r_{k\ell}!}\right).
--   $$
--   Then the exact division-free identity is
--   $$
--   (RQ)\,B_{\rm typ}=D_Z\,B_{\rm comp}.
--   $$
--   All displayed quotients are natural-number divisions. Their exact divisibility follows from the matching histogram sums and is proved, not assumed. Empty finite sets and zero entries are allowed.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS2, Section 6.2 and Lemma 6.7. Exact finite factorial identity connecting the compatible outer degree to the fine-word compatibility fraction.

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Ring

open BigOperators

set_option autoImplicit false

theorem mme_dwz_boundary_histogram_factorial_cancellation
    {K L : Type*} {B P : K → Type*}
    [Fintype K] [Fintype L] [∀ k, Fintype (B k)] [∀ k, Fintype (P k)]
    (b : ∀ k, B k → L → ℕ) (r gamma : K → L → ℕ) (p : ∀ k, P k → ℕ)
    (hcolumn : ∀ k l, gamma k l = r k l + ∑ c, b k c l)
    (hpositive : ∀ k, (∑ l, r k l) = ∑ c, p k c) :
    ((∏ k, ∏ l, (gamma k l).factorial /
      ((r k l).factorial * ∏ c, (b k c l).factorial)) *
      (∏ k, (∑ l, r k l).factorial / ∏ c, (p k c).factorial)) *
      (∏ k, (∑ l, gamma k l).factorial / ∏ l, (gamma k l).factorial) =
    (∏ k, (∑ l, gamma k l).factorial /
      ((∏ c, (∑ l, b k c l).factorial) * ∏ c, (p k c).factorial)) *
      ((∏ k, ∏ c, (∑ l, b k c l).factorial / ∏ l, (b k c l).factorial) *
        (∏ k, (∑ l, r k l).factorial / ∏ l, (r k l).factorial)) := by sorry
