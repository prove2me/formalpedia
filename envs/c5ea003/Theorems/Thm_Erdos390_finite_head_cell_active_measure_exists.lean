-- Prove2me | Theorems.Thm_Erdos390_finite_head_cell_active_measure_exists
-- name    : Erdos390.finite_head_cell_active_measure_exists
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T17:52:07.153388+00:00
-- url     : https://prove2.me/theorems/ca05ec04-6ce8-43dc-a92f-16e87e51bc34
-- title:
--   Simultaneous bounded active measure on finitely many head-cell pairs
-- statement:
--   Let $H$ be a finite family of head labels. For each $i\in H$, let $A_i,B_i$ be nonempty disjoint finite integer cells, with all numerical supports $A_i\cup B_i$ pairwise disjoint across labels. Fix a real score $f$, masses $q_i>0$, target means $\mu_i$, and a common bound $\eta\ge0$. Assume
--   $$\overline f_{A_i}<\mu_i<\overline f_{B_i},\qquad q_i\le\eta|A_i|,\quad q_i\le\eta|B_i|.$$
--   There is one weight function $x$ supported on the union of the cells, with $0\le x_a\le\eta$, strictly positive and constant on each individual cell, such that for every head label
--   $$\sum_{a\in A_i\cup B_i}x_a=q_i,\qquad \sum_{a\in A_i\cup B_i}x_af(a)=q_i\mu_i.$$
--   Consequently its total mass is $\sum_iq_i$ and its total score moment is $\sum_iq_i\mu_i$.
--
--   With $f(a)=\log(a/n)$, this is the finite simultaneous allocation step of the baseline active-measure construction. Numerical disjointness lets the individual coordinate ceilings survive when the head measures are combined. This theorem assumes the required guarded cells and capacities; it does not assert their analytic existence.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 8, equations smooth-head-simplex, smooth-scaled-physical-constants, smooth-scaled-physical-intervals; Lemma smooth-baseline-active-measure, equations smooth-baseline-finite-mixture and smooth-baseline-coordinate-realization. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex . This isolates and proves the finite two-physical-cell interpolation for one head pattern, with an explicit sufficient coordinate-capacity bound. The finite family combines the head-pattern pairs into the literal mixture of smooth-baseline-finite-mixture.

import Mathlib
open scoped BigOperators

theorem Erdos390.finite_head_cell_active_measure_exists
    {Head : Type*} [Fintype Head]
    (A B : Head → Finset ℕ) (score : ℕ → ℝ) (q μ : Head → ℝ) (cap : ℝ)
    (hcap : 0 ≤ cap)
    (hA : ∀ i, (A i).Nonempty) (hB : ∀ i, (B i).Nonempty)
    (hwithin : ∀ i, Disjoint (A i) (B i))
    (hacross : ∀ i j, i ≠ j → Disjoint (A i ∪ B i) (A j ∪ B j))
    (hq : ∀ i, 0 < q i)
    (hlower : ∀ i, (∑ a ∈ A i, score a) / ((A i).card : ℝ) < μ i)
    (hupper : ∀ i, μ i < (∑ a ∈ B i, score a) / ((B i).card : ℝ))
    (hcapA : ∀ i, q i ≤ cap * ((A i).card : ℝ))
    (hcapB : ∀ i, q i ≤ cap * ((B i).card : ℝ)) :
    ∃ x : ℕ → ℝ,
      (∀ a, 0 ≤ x a ∧ x a ≤ cap) ∧
      (∀ a, a ∉ Finset.univ.biUnion (fun i ↦ A i ∪ B i) → x a = 0) ∧
      (∑ a ∈ Finset.univ.biUnion (fun i ↦ A i ∪ B i), x a) = ∑ i, q i ∧
      (∑ a ∈ Finset.univ.biUnion (fun i ↦ A i ∪ B i), x a * score a) =
        ∑ i, q i * μ i ∧
      ∀ i,
        (∑ a ∈ A i ∪ B i, x a) = q i ∧
        (∑ a ∈ A i ∪ B i, x a * score a) = q i * μ i ∧
        ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
          (∀ a ∈ A i, x a = u) ∧ (∀ a ∈ B i, x a = v) := by sorry
