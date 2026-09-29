-- Prove2me | Theorems.Thm_mme_dwz_boundary_compatible_assignment_card
-- name    : mme_dwz_boundary_compatible_assignment_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:34:42.323987+00:00
-- url     : https://prove2.me/theorems/ed7908ab-d487-4e7f-b7ad-19c05782ffb5
-- title:
--   Exact count of boundary-compatible outer component words
-- statement:
--   Let $A,C,K,L$ be finite sets of positions, component labels, coarse grades, and fine split labels. Fix a fine word $f:A\to K\times L$, a coarse-grade map $q:C\to K$, a boundary subset $B\subseteq C$, boundary split counts $b_{c\ell}\in\mathbb N$, and outer counts $n_c\in\mathbb N$. Write
--   $$
--   \gamma_{k\ell}=|\{a:f(a)=(k,\ell)\}|,\qquad
--   r_{k\ell}=\gamma_{k\ell}-\sum_{c\in B:q(c)=k}b_{c\ell},
--   $$
--   where the subtraction is natural-number subtraction. Define a collapsed label set $D=C\sqcup K$ and map
--   $$
--   c_*(c)=
--   \begin{cases}\mathrm{inl}(c)&c\in B,\\
--   \mathrm{inr}(q(c))&c\notin B.
--   \end{cases}
--   $$
--   For $i=(k,\ell)$, define an explicit joint histogram
--   $$
--   m_{\mathrm{inl}(c),i}=
--   \begin{cases}b_{c\ell}&c\in B,\ q(c)=k,\\0&\text{otherwise},\end{cases}
--   \qquad
--   m_{\mathrm{inr}(k'),i}=
--   \begin{cases}r_{k\ell}&k'=k,\\0&\text{otherwise}.\end{cases}
--   $$
--   Assume the numerical column and collapsed-row totals match:
--   $$
--   \sum_{d\in D}m_{d,i}=|f^{-1}(i)|,\qquad
--   \sum_{c:c_*(c)=d}n_c=\sum_{i\in K\times L}m_{d,i}.
--   $$
--   Then the number of actual words $g:A\to C$ satisfying all three conditions
--   $$
--   |g^{-1}(c)|=n_c,\qquad q(g(a))=f(a)_1,\qquad
--   |\{a:g(a)=c,\ f(a)_2=\ell\}|=b_{c\ell}\quad(c\in B)
--   $$
--   is exactly
--   $$
--   \left(\prod_{i\in K\times L}\frac{|f^{-1}(i)|!}{\prod_{d\in D}m_{d,i}!}\right)
--   \left(\prod_{d\in D}\frac{(\sum_i m_{d,i})!}{\prod_{c:c_*(c)=d}n_c!}\right).
--   $$
--   Only boundary components have individually prescribed fine split counts. Positive components are constrained by their outer counts and coarse grades, not by additional fine histograms. The conclusion includes zero bins and empty sets.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS2, Section 6.2 and Lemma 6.7. Source-faithful finite counting of compatible outer component words with individual boundary split constraints and pooled positive components.

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open BigOperators

set_option autoImplicit false

theorem mme_dwz_boundary_compatible_assignment_card
    {A C K L : Type*}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (fine : A → K × L) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary] (b : C → L → ℕ) (n : C → ℕ) :
    let collapse : C → C ⊕ K :=
      fun c ↦ if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let m : (C ⊕ K) × (K × L) → ℕ
      | (Sum.inl c, (k, l)) => if Boundary c ∧ coarse c = k then b c l else 0
      | (Sum.inr k', (k, l)) =>
          if k' = k then Fintype.card {a : A // fine a = (k, l)} -
            ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l
          else 0
    (∀ i, (∑ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, m di.1) =
      Fintype.card {a : A // fine a = i}) →
    (∀ d, (∑ c : {c : C // collapse c = d}, n c.1) = ∑ i, m (d, i)) →
    Nat.card {g : A → C //
      (∀ c, Fintype.card {a : A // g a = c} = n c) ∧
      (∀ a, coarse (g a) = (fine a).1) ∧
      ∀ c, Boundary c → ∀ l,
        Fintype.card {a : A // g a = c ∧ (fine a).2 = l} = b c l} =
      (∏ i, (Fintype.card {a : A // fine a = i}).factorial /
        ∏ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, (m di.1).factorial) *
      (∏ d, (∑ i, m (d, i)).factorial /
        ∏ c : {c : C // collapse c = d}, (n c.1).factorial) := by sorry
