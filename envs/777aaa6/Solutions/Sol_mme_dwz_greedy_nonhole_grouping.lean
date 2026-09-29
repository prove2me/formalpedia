-- Prove2me | solution 1 for mme_dwz_greedy_nonhole_grouping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:33:48.481382+00:00
-- url     : https://prove2.me/submissions/00ccaf45-87e6-49c2-b337-2a2881062ebd

import Mathlib

/-!
A finite greedy-grouping lemma for the step used in Corollary 5.11 of
Duan--Wu--Zhou.  Each entry is a fraction of non-holes, hence belongs to
`[0,1]`.  A group is closed as soon as its running total reaches `L`.
Consequently its total is below `L + 1`.
-/

private theorem exists_prefix_sum_in_window
    (weights : List ℝ)
    (h_nonneg : ∀ x ∈ weights, 0 ≤ x)
    (h_at_most_one : ∀ x ∈ weights, x ≤ 1)
    (L : ℝ) (hL : 0 < L) (h_total : L ≤ weights.sum) :
    ∃ group remainder : List ℝ,
      weights = group ++ remainder ∧
      L ≤ group.sum ∧ group.sum < L + 1 := by
  induction weights generalizing L with
  | nil =>
      simp at h_total
      linarith
  | cons x xs ih =>
      have hx_nonneg : 0 ≤ x := h_nonneg x (by simp)
      have hx_one : x ≤ 1 := h_at_most_one x (by simp)
      by_cases hx : L ≤ x
      · refine ⟨[x], xs, by simp, ?_, ?_⟩
        · simpa using hx
        · simp only [List.sum_cons, List.sum_nil, add_zero]
          linarith
      · have hx_lt : x < L := lt_of_not_ge hx
        have h_tail_total : L - x ≤ xs.sum := by
          simp only [List.sum_cons] at h_total
          linarith
        have h_tail_nonneg : ∀ y ∈ xs, 0 ≤ y := by
          intro y hy
          exact h_nonneg y (by simp [hy])
        have h_tail_one : ∀ y ∈ xs, y ≤ 1 := by
          intro y hy
          exact h_at_most_one y (by simp [hy])
        obtain ⟨group, remainder, hsplit, hlower, hupper⟩ :=
          ih h_tail_nonneg h_tail_one (L - x) (by linarith) h_tail_total
        refine ⟨x :: group, remainder, ?_, ?_, ?_⟩
        · simp [hsplit]
        · simp only [List.sum_cons]
          linarith
        · simp only [List.sum_cons]
          linarith

theorem solution
    (weights : List ℝ)
    (h_nonneg : ∀ x ∈ weights, 0 ≤ x)
    (h_at_most_one : ∀ x ∈ weights, x ≤ 1)
    (L : ℝ) (hL : 0 < L)
    (q : ℕ) (hq : (q : ℝ) * (L + 1) ≤ weights.sum) :
    ∃ groups : List (List ℝ), ∃ remainder : List ℝ,
      weights = groups.flatten ++ remainder ∧
      groups.length = q ∧
      ∀ group ∈ groups, L ≤ group.sum ∧ group.sum < L + 1 := by
  induction q generalizing weights with
  | zero =>
      exact ⟨[], weights, by simp⟩
  | succ q ih =>
      have hL_one : 0 < L + 1 := by linarith
      have h_total : L ≤ weights.sum := by
        have hq_nonneg : (0 : ℝ) ≤ q := by positivity
        norm_num [Nat.cast_add, Nat.cast_one] at hq
        nlinarith
      obtain ⟨group, rest, hsplit, hgroup_lower, hgroup_upper⟩ :=
        exists_prefix_sum_in_window weights h_nonneg h_at_most_one L hL h_total
      have hrest_nonneg : ∀ x ∈ rest, 0 ≤ x := by
        intro x hx
        apply h_nonneg x
        rw [hsplit]
        simp [hx]
      have hrest_one : ∀ x ∈ rest, x ≤ 1 := by
        intro x hx
        apply h_at_most_one x
        rw [hsplit]
        simp [hx]
      have hsum_split : weights.sum = group.sum + rest.sum := by
        rw [hsplit, List.sum_append]
      have hrest_total : (q : ℝ) * (L + 1) ≤ rest.sum := by
        norm_num [Nat.cast_add, Nat.cast_one] at hq
        nlinarith
      obtain ⟨groups, remainder, hgroups_split, hgroups_length, hgroups_bounds⟩ :=
        ih rest hrest_nonneg hrest_one hrest_total
      refine ⟨group :: groups, remainder, ?_, ?_, ?_⟩
      · rw [hsplit, hgroups_split]
        simp
      · simp [hgroups_length]
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact ⟨hgroup_lower, hgroup_upper⟩
        · exact hgroups_bounds g hg
