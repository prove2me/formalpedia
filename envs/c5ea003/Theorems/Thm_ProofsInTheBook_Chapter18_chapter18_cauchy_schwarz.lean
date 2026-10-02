-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter18_chapter18_cauchy_schwarz
-- name    : ProofsInTheBook.Chapter18.chapter18_cauchy_schwarz
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T15:17:21.416349+00:00
-- url     : https://prove2.me/theorems/35465b85-75b1-4482-9cf6-03aacc27c78b
-- title:
--   The finite Cauchy–Schwarz inequality
-- statement:
--   Let $I$ be any index set, let $s\subseteq I$ be finite, and let $f,g:I\to\mathbb R$ be arbitrary. Then
--   $$\left(\sum_{i\in s}f_i g_i\right)^2\le\left(\sum_{i\in s}f_i^2\right)\left(\sum_{i\in s}g_i^2\right).$$
--   The set $s$ may be empty, and the entries need not be nonnegative.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 20, “In praise of inequalities”, pp. 143–150 (https://doi.org/10.1007/978-3-662-57265-8_20). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter18.lean#L67. The book citation identifies the topic; the selected declaration does not claim to reproduce the entire chapter.

import Mathlib

theorem ProofsInTheBook.Chapter18.chapter18_cauchy_schwarz {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by sorry
