-- Prove2me | solution 1 for BookSixth.rectangle_extension_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:58:51.241549+00:00
-- url     : https://prove2.me/submissions/d9761528-90d7-49cf-8eac-b88830f4352f

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n k : ℕ) (hkn : k ≤ n) (used : Fin n → Finset (Fin n))
    (hcard : ∀ i, (used i).card = k)
    (hBM : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℕ),
      (∀ i j, A i j = 0 ∨ A i j = 1) → (∀ i, ∑ j, A i j = (r i : ℝ)) →
      Matrix.permanent A ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ))) :
    ((Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∉ used i)).card : ℝ)
      ≤ ∏ _i : Fin n,
        ((((n - k).factorial : ℕ) : ℝ) ^ ((1 : ℝ) / (((n - k : ℕ)) : ℝ))) := by
  classical
  have hcardU : ∀ i, (Finset.univ.filter (fun s => s ∉ used i)).card
      = n - k := by
    intro i
    have h1 : Finset.univ.filter (fun s => s ∈ used i) = used i := by
      ext s
      simp
    have h2 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin n))) (p := fun s => s ∈ used i)
    rw [h1, hcard i, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : Finset.univ.filter (fun s => s ∉ used i)
        = Finset.univ.filter (fun a => ¬ a ∈ used i) := rfl
    omega
  have hA01 : ∀ i j, (fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) i j = 0
      ∨ (fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) i j = 1 := by
    intro i j
    by_cases hj : j ∈ used i
    · left
      show (if j ∈ used i then (0 : ℝ) else (1 : ℝ)) = 0
      exact if_pos hj
    · right
      show (if j ∈ used i then (0 : ℝ) else (1 : ℝ)) = 1
      exact if_neg hj
  have hrowsum : ∀ i, ∑ j, (fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) i j
      = (((n - k : ℕ)) : ℝ) := by
    intro i
    have e : ∀ j, (fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) i j
        = (if j ∉ used i then (1 : ℝ) else 0) := by
      intro j
      show (if j ∈ used i then (0 : ℝ) else (1 : ℝ)) = _
      by_cases hj : j ∈ used i <;> simp [hj]
    simp_rw [e]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_one, hcardU i]
  have hpermU : Matrix.permanent
        (fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ))
      = ∑ σ : Equiv.Perm (Fin n),
        ∏ i, (if i ∈ used (σ i) then (0 : ℝ) else (1 : ℝ)) := by
    rw [Matrix.permanent]
  have htermU : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, (if i ∈ used (σ i) then (0 : ℝ) else (1 : ℝ)))
        = if ∀ i, i ∉ used (σ i) then (1 : ℝ) else 0 := by
    intro σ
    by_cases h : ∀ i, i ∉ used (σ i)
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro i _
      exact if_neg (h i)
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_pos hi
  have hcardU2 : Matrix.permanent
        (fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ))
      = ((Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => ∀ i, i ∉ used (σ i))).card : ℝ) := by
    rw [hpermU]
    simp_rw [htermU]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_one]
  have hbij : (Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => ∀ i, i ∉ used (σ i))).card
      = (Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∉ used i)).card := by
    refine Finset.card_bij (s := Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => ∀ i, i ∉ used (σ i))) (t := Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∉ used i))
      (fun (σ : Equiv.Perm (Fin n)) _ => σ.symm) ?_ ?_ ?_
    · intro σ ha
      show σ.symm ∈ Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∉ used i)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun i => ?_⟩
      have hσ := (Finset.mem_filter.mp ha).2
      have h1 := hσ (σ.symm i)
      have hs : σ (σ.symm i) = i := by simp
      rw [hs] at h1
      exact h1
    · intro a₁ _ a₂ _ h
      have h2 : a₁.symm = a₂.symm := h
      rw [← Equiv.symm_symm a₁, ← Equiv.symm_symm a₂, h2]
    · intro τ hb
      have hτ := (Finset.mem_filter.mp hb).2
      refine ⟨τ.symm, ?_, Equiv.symm_symm τ⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun i => ?_⟩
      have h1 := hτ (τ.symm i)
      have hs : τ (τ.symm i) = i := by simp
      rw [hs] at h1
      exact h1
  have hBd := hBM (fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ))
    (fun _ => n - k) hA01 hrowsum
  rw [← hbij, ← hcardU2]
  exact hBd
