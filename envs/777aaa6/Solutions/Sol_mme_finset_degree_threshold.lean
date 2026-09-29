-- Prove2me | solution 1 for mme_finset_degree_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:26:06.951276+00:00
-- url     : https://prove2.me/submissions/b5bbfbe9-1a67-4ebf-95df-521826e63729

import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

/-- Keeping every label whose original fiber has size at least `H` preserves
those whole fibers and gives a deterministic mass-versus-label bound. -/
theorem solution
    {α ζ : Type} [DecidableEq α] [DecidableEq ζ]
    (E : Finset α) (z : α → ζ) (H D : ℕ)
    (hmax : ∀ c ∈ E.image z,
      (E.filter (fun e => z e = c)).card ≤ D) :
    let F := E.filter (fun e =>
      H ≤ (E.filter (fun e' => z e' = z e)).card)
    F ⊆ E ∧
      (∀ c ∈ F.image z,
        H ≤ (F.filter (fun e => z e = c)).card) ∧
      E.card ≤ H * (E.image z).card + D * (F.image z).card := by
  classical
  let F := E.filter (fun e =>
    H ≤ (E.filter (fun e' => z e' = z e)).card)
  have hFE : F ⊆ E := Finset.filter_subset _ _
  have himage : F.image z ⊆ E.image z := by
    intro c hc
    obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image_of_mem z (hFE heF)
  have hfiberEq : ∀ c ∈ F.image z,
      F.filter (fun e => z e = c) = E.filter (fun e => z e = c) := by
    intro c hc
    obtain ⟨e, heF, hec⟩ := Finset.mem_image.mp hc
    apply Finset.Subset.antisymm
    · intro x hx
      exact Finset.mem_filter.mpr
        ⟨hFE (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    · intro x hx
      have hxE := (Finset.mem_filter.mp hx).1
      have hxc := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, hxc⟩
      apply Finset.mem_filter.mpr
      refine ⟨hxE, ?_⟩
      have heThreshold := (Finset.mem_filter.mp heF).2
      rw [hec] at heThreshold
      simpa [hxc] using heThreshold
  refine ⟨hFE, ?_, ?_⟩
  · intro c hc
    rw [hfiberEq c hc]
    obtain ⟨e, heF, hec⟩ := Finset.mem_image.mp hc
    have heThreshold := (Finset.mem_filter.mp heF).2
    rwa [hec] at heThreshold
  · rw [Finset.card_eq_sum_card_image z E]
    calc
      ∑ c ∈ E.image z, (E.filter (fun e => z e = c)).card ≤
          ∑ c ∈ E.image z, (H + if c ∈ F.image z then D else 0) := by
        apply Finset.sum_le_sum
        intro c hc
        by_cases hcF : c ∈ F.image z
        · have hdeg := hmax c hc
          simp only [hcF, if_true]
          omega
        · have hlt : (E.filter (fun e => z e = c)).card < H := by
            by_contra hnot
            have hge : H ≤ (E.filter (fun e => z e = c)).card :=
              Nat.le_of_not_gt hnot
            obtain ⟨e, heE, hec⟩ := Finset.mem_image.mp hc
            apply hcF
            apply Finset.mem_image.mpr
            refine ⟨e, ?_, hec⟩
            apply Finset.mem_filter.mpr
            refine ⟨heE, ?_⟩
            rwa [hec]
          simp only [hcF, if_false, add_zero]
          omega
      _ = H * (E.image z).card + D * (F.image z).card := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Nat.nsmul_eq_mul]
        have hfilter : (E.image z).filter (fun c => c ∈ F.image z) = F.image z := by
          ext c
          simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨himage h, h⟩
        have hindicator :
            (∑ c ∈ E.image z, if c ∈ F.image z then D else 0) =
              (F.image z).card * D := by
          rw [← Finset.sum_filter, hfilter]
          simp
        rw [hindicator]
        simp [Nat.mul_comm]
