-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximizer_of_bounded_nat__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
-- name    : WilliamsonShmoys.exists_maximizer_of_bounded_nat__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:06.676976+00:00
-- url     : https://prove2.me/theorems/a38b79a1-124e-43f5-be2e-7a1970ee2a96
-- title:
--   A bounded natural-valued size attains a maximum
-- statement:
--   Any nonempty class whose natural-number-valued size has a common upper bound contains an element with maximum size. In the parent, the class consists of drawable supergraphs of H, and the size is edge count. The parent establishes the common bound using the finite type Sym2 V. A proof route is to choose the greatest attained size among the finitely many values at most the bound, then choose an element attaining it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximizer_of_bounded_nat__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
    {α : Type} (P : α → Prop) (size : α → Nat)
    (hne : ∃ x, P x)
    (hbdd : ∃ N, ∀ x, P x → size x ≤ N) :
    ∃ x, P x ∧ ∀ y, P y → size y ≤ size x := by sorry
