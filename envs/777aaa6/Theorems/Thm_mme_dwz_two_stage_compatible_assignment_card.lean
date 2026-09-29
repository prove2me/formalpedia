-- Prove2me | Theorems.Thm_mme_dwz_two_stage_compatible_assignment_card
-- name    : mme_dwz_two_stage_compatible_assignment_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:22:25.063649+00:00
-- url     : https://prove2.me/theorems/06041991-9a5c-4eb5-8405-388e4709face
-- title:
--   Exact two-stage count of compatible component assignments
-- statement:
--   Let $A,B,D,I$ be finite sets, with a fixed fine-class map $f:A\to I$ and a collapsed-label map $c:B\to D$. Let $n_b\in\mathbb N$ prescribe the number of occurrences of each original label, and let $m_{d,i}\in\mathbb N$ prescribe the joint counts of collapsed labels and fine classes. Assume the column and row totals match:
--   $$
--   \sum_{d\in D}m_{d,i}=|f^{-1}(i)|\quad(i\in I),
--   \qquad
--   \sum_{b:c(b)=d}n_b=\sum_{i\in I}m_{d,i}\quad(d\in D).
--   $$
--   Then the number of maps $g:A\to B$ satisfying
--   $$
--   |g^{-1}(b)|=n_b\quad(b\in B),
--   \qquad
--   |\{a\in A:(c(g(a)),f(a))=(d,i)\}|=m_{d,i}\quad((d,i)\in D\times I)
--   $$
--   equals the product of two exact multinomial counts:
--   $$
--   \left(\prod_{i\in I}\frac{|f^{-1}(i)|!}{\prod_{d\in D}m_{d,i}!}\right)
--   \left(\prod_{d\in D}\frac{(\sum_{i\in I}m_{d,i})!}{\prod_{b:c(b)=d}n_b!}\right).
--   $$
--   Both quotients are natural-number divisions, as in the formal statement. The matching-total hypotheses ensure they count finite sets exactly. Empty sets, zero histogram entries, and non-surjective maps are allowed; $0!=1$.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS2, Section 6.2 and Lemma 6.7. General finite assignment-count lemma for the compatible-subfiber enumeration; not a separately numbered theorem in the paper.

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open BigOperators

set_option autoImplicit false

theorem mme_dwz_two_stage_compatible_assignment_card
    {α β δ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype δ] [DecidableEq δ] [Fintype ι] [DecidableEq ι]
    (fine : α → ι) (collapse : β → δ) (n : β → ℕ) (m : δ × ι → ℕ)
    (hFine : ∀ i, (∑ di : {di : δ × ι // di.2 = i}, m di.1) =
      Fintype.card {a : α // fine a = i})
    (hCollapsed : ∀ d, (∑ b : {b : β // collapse b = d}, n b.1) =
      ∑ i, m (d, i)) :
    Nat.card {g : α → β //
      (∀ b, Fintype.card {a : α // g a = b} = n b) ∧
      ∀ di, Fintype.card {a : α // (collapse (g a), fine a) = di} = m di} =
      (∏ i, (Fintype.card {a : α // fine a = i}).factorial /
        ∏ di : {di : δ × ι // di.2 = i}, (m di.1).factorial) *
      (∏ d, (∑ i, m (d, i)).factorial /
        ∏ b : {b : β // collapse b = d}, (n b.1).factorial) := by sorry
