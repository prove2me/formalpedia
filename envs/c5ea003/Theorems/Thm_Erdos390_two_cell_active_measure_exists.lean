-- Prove2me | Theorems.Thm_Erdos390_two_cell_active_measure_exists
-- name    : Erdos390.two_cell_active_measure_exists
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T17:46:51.441032+00:00
-- url     : https://prove2.me/theorems/bb5301fa-5abf-4fb6-8600-913b2b9805a9
-- title:
--   Exact bounded active weights on two physical cells
-- statement:
--   Let $A,B$ be disjoint nonempty finite sets of integers, and let $f$ be a real score. Suppose their average scores straddle the desired mean $\mu$:
--   $$\overline f_A<\mu<\overline f_B.$$
--   Let $q>0$ be the prescribed mass, and let $\eta$ be a coordinate bound satisfying
--   $$q\le\eta|A|,\qquad q\le\eta|B|.$$
--   There are weights $x_a$ supported on $A\cup B$, strictly positive and constant separately on each cell, such that
--   $$0\le x_a\le\eta,\qquad \sum_{a\in A\cup B}x_a=q,\qquad \sum_{a\in A\cup B}x_af(a)=q\mu.$$
--
--   For the active-measure construction, the cells share a head pattern and lie in the two physical intervals, while $f(a)=\log(a/n)$. The fixed mass on that head pattern preserves its head moments, and the interpolation realizes the desired physical logarithmic mean. The lemma proves the finite allocation; existence and quantitative size of the guarded cells are separate analytic requirements.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 8, equations smooth-head-simplex, smooth-scaled-physical-constants, smooth-scaled-physical-intervals; Lemma smooth-baseline-active-measure, equations smooth-baseline-finite-mixture and smooth-baseline-coordinate-realization. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex . This isolates and proves the finite two-physical-cell interpolation for one head pattern, with an explicit sufficient coordinate-capacity bound.

import Mathlib
open scoped BigOperators

theorem Erdos390.two_cell_active_measure_exists
    (A B : Finset ℕ) (score : ℕ → ℝ) (q μ cap : ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisjoint : Disjoint A B)
    (hq : 0 < q)
    (hlower : (∑ a ∈ A, score a) / (A.card : ℝ) < μ)
    (hupper : μ < (∑ a ∈ B, score a) / (B.card : ℝ))
    (hcapA : q ≤ cap * (A.card : ℝ))
    (hcapB : q ≤ cap * (B.card : ℝ)) :
    ∃ x : ℕ → ℝ,
      (∀ a, 0 ≤ x a ∧ x a ≤ cap) ∧
      (∀ a, a ∉ A ∪ B → x a = 0) ∧
      (∑ a ∈ A ∪ B, x a) = q ∧
      (∑ a ∈ A ∪ B, x a * score a) = q * μ ∧
      ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
        (∀ a ∈ A, x a = u) ∧ (∀ a ∈ B, x a = v) := by sorry
