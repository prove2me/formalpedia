-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter18_chapter18
-- name    : ProofsInTheBook.Chapter18.chapter18
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T15:17:17.63446+00:00
-- url     : https://prove2.me/theorems/67bd1ce2-4cb7-44f1-8ce4-e3719c7657e1
-- title:
--   The finite arithmetic–geometric mean inequality
-- statement:
--   Let $I$ be any index set, let $s\subseteq I$ be finite and nonempty, and let $z:I\to\mathbb R$ satisfy $z_i\ge0$ for every $i\in s$. Writing $n=|s|>0$, one has
--   $$\left(\prod_{i\in s}z_i\right)^{1/n}\le\frac{1}{n}\sum_{i\in s}z_i.$$
--   The exponent is a real power; zero entries are allowed. No condition is imposed on entries outside $s$.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 20, “In praise of inequalities”, pp. 143–150 (https://doi.org/10.1007/978-3-662-57265-8_20). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter18.lean#L41. The book citation identifies the topic; the selected declaration does not claim to reproduce the entire chapter.

import Mathlib

theorem ProofsInTheBook.Chapter18.chapter18 {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹) ≤ (∑ i ∈ s, z i) / s.card := by sorry
