-- Prove2me | solution 1 for HistoryPotential.pathwise_bound_iff
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:10:26.898629+00:00
-- url     : https://prove2.me/submissions/fd00d06e-6342-4cde-a266-08fbbb8def3e

import Mathlib

set_option autoImplicit false

theorem solution (M I : Type) [Nonempty I]
    (W : List M → I → ℝ) (B : List M → ℝ) :
    (∃ Φ : List M → ℝ, Φ [] = 0 ∧
      (∀ σ : List M, Φ σ ≤ B σ) ∧
      (∀ (l : List M) (r : M) (i : I),
        W (l ++ [r]) i - W l i ≤ Φ (l ++ [r]) - Φ l)) ↔
    (∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ i : I,
        W (σ.take (t + 1)) i ≤ W (σ.take t) i + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ B σ) := by
  classical
  constructor
  · rintro ⟨Φ, hzero, hupper, hstep⟩ σ
    refine ⟨fun t => Φ (σ.take (t + 1)) - Φ (σ.take t), ?_, ?_⟩
    · intro t ht i
      have heq : σ.take (t + 1) = σ.take t ++ [σ[t]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem ht]
        rfl
      have hh := hstep (σ.take t) σ[t] i
      rw [← heq] at hh
      linarith
    · rw [Finset.sum_range_sub (fun t => Φ (σ.take t))]
      simpa only [List.take_length, List.take_zero, hzero, sub_zero] using hupper σ
  · intro H
    let E (l l' : List M) : ℝ := sSup (Set.range (fun i : I => W l' i - W l i))
    let Φ (σ : List M) : ℝ :=
      ∑ t ∈ Finset.range σ.length, E (σ.take t) (σ.take (t + 1))
    have hsum (l : List M) (r : M) : Φ (l ++ [r]) = Φ l + E l (l ++ [r]) := by
      dsimp only [Φ]
      simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
      have hs : (∑ t ∈ Finset.range l.length,
          E ((l ++ [r]).take t) ((l ++ [r]).take (t + 1))) =
          ∑ t ∈ Finset.range l.length, E (l.take t) (l.take (t + 1)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [List.take_append_of_le_length (Nat.le_of_lt (Finset.mem_range.mp ht)),
          List.take_append_of_le_length (by simpa using Finset.mem_range.mp ht : t + 1 ≤ l.length)]
      rw [hs, List.take_append_length]
      congr 2
      exact List.take_of_length_le (by simp)
    refine ⟨Φ, by simp [Φ], ?_, ?_⟩
    · intro σ
      obtain ⟨u, hstep, hu⟩ := H σ
      apply le_trans (Finset.sum_le_sum ?_) hu
      intro t ht
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      have h := hstep t (Finset.mem_range.mp ht) i
      linarith
    · intro l r i
      obtain ⟨u, hstep, _⟩ := H (l ++ [r])
      have hb : BddAbove (Set.range (fun i : I => W (l ++ [r]) i - W l i)) := by
        refine ⟨u l.length, ?_⟩
        rintro _ ⟨j, rfl⟩
        have hh := hstep l.length (by simp) j
        have htake : (l ++ [r]).take (l.length + 1) = l ++ [r] :=
          List.take_of_length_le (by simp)
        rw [htake, List.take_append_length] at hh
        linarith
      have hh : W (l ++ [r]) i - W l i ≤ E l (l ++ [r]) :=
        le_csSup hb ⟨i, rfl⟩
      rw [hsum]
      linarith

#print axioms solution
