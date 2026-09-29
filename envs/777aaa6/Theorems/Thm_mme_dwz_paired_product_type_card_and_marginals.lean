-- Prove2me | Theorems.Thm_mme_dwz_paired_product_type_card_and_marginals
-- name    : mme_dwz_paired_product_type_card_and_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T15:19:12.388238+00:00
-- url     : https://prove2.me/theorems/295ef1dd-b822-4af6-9db2-35b57834928c
-- title:
--   Exact denominator-cleared paired product types and their marginals
-- statement:
--   Let $P,S,A,B$ be finite sets, let $\kappa:P\to S$ partition paired positions into ordered pair types, and write $P_s=\{p\in P:\kappa(p)=s\}$. For each $s\in S$, choose integer tag-count vectors $\ell_s:A\to\mathbb N$ and $r_s:B\to\mathbb N$, together with $D_s^L,D_s^R,m_s\in\mathbb N$, such that
--   $$
--   \sum_{a\in A}\ell_s(a)=D_s^L,\qquad
--   \sum_{b\in B}r_s(b)=D_s^R,\qquad
--   |P_s|=n_s:=m_sD_s^LD_s^R.
--   $$
--   Define the joint counts $J_s(a,b):=m_s\ell_s(a)r_s(b)$. Let $\mathcal F$ be the set of assignments $f:P\to A\times B$ having exactly $J_s(a,b)$ occurrences of $(a,b)$ in $P_s$.
--
--   Then $\mathcal F$ is nonempty, and its cardinality is exactly
--   $$
--   |\mathcal F|
--   =\prod_{s\in S}\binom{n_s}{\bigl(J_s(a,b)\bigr)_{(a,b)\in A\times B}}
--   =\prod_{s\in S}\frac{n_s!}{\prod_{(a,b)\in A\times B}J_s(a,b)!}.
--   $$
--   For every $f=(f_L,f_R)\in\mathcal F$, the two marginal histograms satisfy
--   $$
--   |\{p\in P_s:f_L(p)=a\}|=m_s\ell_s(a)D_s^R,\qquad
--   |\{p\in P_s:f_R(p)=b\}|=m_sD_s^Lr_s(b).
--   $$
--   Moreover, for any set $T$, any type-dependent aggregate tag map $\theta:S\times(A\times B)\to T$, and any $t\in T$, the aggregate histogram is the exact pushforward of the joint counts:
--   $$
--   |\{p\in P:\theta(\kappa(p),f(p))=t\}|
--   =\sum_{s\in S}\ \sum_{\substack{(a,b)\in A\times B\\\theta(s,(a,b))=t}}J_s(a,b).
--   $$
--
--   The paired positions and their left/right orientation remain fixed throughout. The finite theorem permits zero totals; interpreting $\ell_s/D_s^L$ and $r_s/D_s^R$ as probability distributions additionally requires positive denominators. This is an exact finite counting and profile-transport result. It does not by itself assert an entropy estimate, an inverse-polynomial typical-mass bound, or a tensor restriction.
-- source:
--   Derived finite, denominator-cleared counting and profile-transport helper for Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5 . See Lemma 7.10 and its Appendix C proof, especially equation (44): prescribed joint child-tag frequencies give a sufficient condition for membership in the strongly useful and typical intersection, and the following disjoint-paired-position count factors into multinomial coefficients. This theorem formalizes that finite product-type counting mechanism and its marginal/pushforward identities; it is not a verbatim theorem from the paper and does not itself prove Lemma 7.10's asymptotic mass comparison.

import Theorems.Thm_mme_prescribed_cell_histogram_card
import Mathlib.Data.Fintype.Prod
open BigOperators
open scoped Classical
set_option autoImplicit false

theorem mme_dwz_paired_product_type_card_and_marginals
    {P S A B Tag : Type*}
    [Fintype P] [Fintype S] [Fintype A] [Fintype B]
    (cell : P → S) (l : S → A → ℕ) (r : S → B → ℕ)
    (DL DR m : S → ℕ)
    (hl : ∀ s, ∑ a, l s a = DL s) (hr : ∀ s, ∑ b, r s b = DR s)
    (hsize : ∀ s, Fintype.card {p : P // cell p = s} = m s * DL s * DR s) :
    (Fintype.card {f : P → A × B //
      MME.RecursiveYZ.Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f} =
      ∏ s, Nat.multinomial Finset.univ
        (fun ab : A × B => m s * l s ab.1 * r s ab.2)) ∧
    (∃ f : P → A × B,
      MME.RecursiveYZ.Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f) ∧
    ∀ f : P → A × B,
      MME.RecursiveYZ.Useful cell (fun s ab => m s * l s ab.1 * r s ab.2) f →
      (∀ s a, MME.RecursiveYZ.count cell (fun p => (f p).1) s a =
        m s * l s a * DR s) ∧
      (∀ s b, MME.RecursiveYZ.count cell (fun p => (f p).2) s b =
        m s * DL s * r s b) ∧
      ∀ (tag : S → A × B → Tag) (t : Tag),
        Fintype.card {p : P // tag (cell p) (f p) = t} =
          ∑ s, ∑ ab : A × B,
            if tag s ab = t then m s * l s ab.1 * r s ab.2 else 0 := by sorry
