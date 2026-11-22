-- Prove2me | solution 1 for Erdos390.finite_head_cell_active_measure_exists
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-16T17:52:49.463067+00:00
-- url     : https://prove2.me/submissions/a408d92f-b91a-45a2-a89d-930fc32650b1

import Theorems.Thm_Erdos390_two_cell_active_measure_exists

open scoped BigOperators

theorem solution
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
          (∀ a ∈ A i, x a = u) ∧ (∀ a ∈ B i, x a = v) := by
  classical
  have hex (i : Head) := Erdos390.two_cell_active_measure_exists
    (A i) (B i) score (q i) (μ i) cap (hA i) (hB i) (hwithin i)
    (hq i) (hlower i) (hupper i) (hcapA i) (hcapB i)
  let xi : Head → ℕ → ℝ := fun i ↦ Classical.choose (hex i)
  have hxi (i : Head) := Classical.choose_spec (hex i)
  let x : ℕ → ℝ := fun a ↦ ∑ i, xi i a
  have hx_eq (i : Head) (a : ℕ) (ha : a ∈ A i ∪ B i) : x a = xi i a := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      apply (hxi j).2.1 a
      intro hj
      exact (Finset.disjoint_left.mp (hacross j i hji)) hj ha
    · simp
  have hbounds (a : ℕ) : 0 ≤ x a ∧ x a ≤ cap := by
    by_cases ha : ∃ i, a ∈ A i ∪ B i
    · obtain ⟨i, hi⟩ := ha
      rw [hx_eq i a hi]
      exact (hxi i).1 a
    · have hz : x a = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact (hxi i).2.1 a (fun hi ↦ ha ⟨i, hi⟩)
      rw [hz]
      exact ⟨le_rfl, hcap⟩
  have hzero (a : ℕ) (ha : a ∉ Finset.univ.biUnion (fun i ↦ A i ∪ B i)) :
      x a = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply (hxi i).2.1 a
    intro hi
    exact ha (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
  have hlocal (i : Head) :
      (∑ a ∈ A i ∪ B i, x a) = q i ∧
      (∑ a ∈ A i ∪ B i, x a * score a) = q i * μ i ∧
      ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
        (∀ a ∈ A i, x a = u) ∧ (∀ a ∈ B i, x a = v) := by
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ = ∑ a ∈ A i ∪ B i, xi i a := Finset.sum_congr rfl (hx_eq i)
        _ = _ := (hxi i).2.2.1
    · calc
        _ = ∑ a ∈ A i ∪ B i, xi i a * score a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hx_eq i a ha]
        _ = _ := (hxi i).2.2.2.1
    · obtain ⟨u, v, hu, hv, hAu, hBv⟩ := (hxi i).2.2.2.2
      refine ⟨u, v, hu, hv, ?_, ?_⟩
      · intro a ha
        rw [hx_eq i a (Finset.mem_union_left _ ha)]
        exact hAu a ha
      · intro a ha
        rw [hx_eq i a (Finset.mem_union_right _ ha)]
        exact hBv a ha
  have hpair : ((Finset.univ : Finset Head) : Set Head).PairwiseDisjoint
      (fun i ↦ A i ∪ B i) := by
    intro i _ j _ hij
    exact hacross i j hij
  refine ⟨x, hbounds, hzero, ?_, ?_, hlocal⟩
  · rw [Finset.sum_biUnion hpair]
    exact Finset.sum_congr rfl (fun i _ ↦ (hlocal i).1)
  · rw [Finset.sum_biUnion hpair]
    exact Finset.sum_congr rfl (fun i _ ↦ (hlocal i).2.1)
