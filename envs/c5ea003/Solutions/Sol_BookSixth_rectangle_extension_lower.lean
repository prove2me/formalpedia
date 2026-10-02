-- Prove2me | solution 1 for BookSixth.rectangle_extension_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T03:22:23.126383+00:00
-- url     : https://prove2.me/submissions/56904acb-5c54-4cd1-acbe-6ac72de53b3c

-- repair attempt: explicit pointwise scaling matrix (avoid Matrix smul instance)
import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n k : ℕ) (hkn : k ≤ n) (used : Fin n → Finset (Fin n))
    (hcard : ∀ i, (used i).card = k)
    (hcol : ∀ s, (Finset.univ.filter (fun i => s ∈ used i)).card = k)
    (hvdW : ∀ (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, 0 ≤ A i j) → (∀ i, ∑ j, A i j = 1) → (∀ j, ∑ i, A i j = 1) →
      (n.factorial : ℝ) / (n : ℝ) ^ n ≤ Matrix.permanent A) :
    ((((n - k : ℕ)) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤
      ((Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∉ used i)).card : ℝ)) := by
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
  have hcardUcol : ∀ s, (Finset.univ.filter (fun i => s ∉ used i)).card
      = n - k := by
    intro s
    have h2 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => s ∈ used i)
    rw [hcol s, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : Finset.univ.filter (fun i => s ∉ used i)
        = Finset.univ.filter (fun a => ¬ s ∈ used a) := rfl
    omega
  have hA01 : ∀ i j, ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i j = 0
      ∨ ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i j = 1 := by
    intro i j
    by_cases hj : j ∈ used i
    · left
      show (if j ∈ used i then (0 : ℝ) else (1 : ℝ)) = 0
      exact if_pos hj
    · right
      show (if j ∈ used i then (0 : ℝ) else (1 : ℝ)) = 1
      exact if_neg hj
  have hnnA : ∀ i j, 0 ≤ ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j
    rcases hA01 i j with h | h <;> rw [h] <;> norm_num
  have hrowsum : ∀ i, ∑ j, ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i j
      = (((n - k : ℕ)) : ℝ) := by
    intro i
    have e : ∀ j, ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i j
        = (if j ∉ used i then (1 : ℝ) else 0) := by
      intro j
      show (if j ∈ used i then (0 : ℝ) else (1 : ℝ)) = _
      by_cases hj : j ∈ used i <;> simp [hj]
    simp_rw [e]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_one, hcardU i]
  have hcolsum : ∀ s, ∑ i, ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i s
      = (((n - k : ℕ)) : ℝ) := by
    intro s
    have e : ∀ i, ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i s
        = (if s ∉ used i then (1 : ℝ) else 0) := by
      intro i
      show (if s ∈ used i then (0 : ℝ) else (1 : ℝ)) = _
      by_cases hs : s ∈ used i <;> simp [hs]
    simp_rw [e]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_one, hcardUcol s]
  have hpermU : Matrix.permanent
        ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ)
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
        ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ)
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
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hkn
    subst hk0
    have hEf : Finset.univ.filter
          (fun σ : Equiv.Perm (Fin 0) => ∀ i, σ i ∉ used i) = Finset.univ :=
      Finset.filter_true_of_mem (fun σ _ i => nomatch i)
    have hEc : Fintype.card (Equiv.Perm (Fin 0)) = 1 := by
      rw [Fintype.card_perm]
      simp
    have hE1 : ((Finset.univ.filter
        (fun σ : Equiv.Perm (Fin 0) => ∀ i, σ i ∉ used i)).card : ℝ) = 1 := by
      rw [hEf, Finset.card_univ, hEc, Nat.cast_one]
    rw [hE1]
    norm_num [Nat.factorial_zero]
  · have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rcases Nat.eq_zero_or_pos (n - k) with hd0 | hdpos
    · have hD0 : ((((n - k : ℕ))) : ℝ) = 0 := by
        rw [hd0]
        norm_num
      have hA0entry : ∀ i j,
          ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i j = 0 := by
        intro i j
        have hs := hrowsum i
        rw [hd0] at hs
        simp only [Nat.cast_zero] at hs
        have hle : ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i j
            ≤ ∑ s, ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) i s :=
          Finset.single_le_sum (fun s _ => hnnA i s) (Finset.mem_univ j)
        linarith [hnnA i j]
      have hA0mat : ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ)
          = (0 : Matrix (Fin n) (Fin n) ℝ) := by
        ext i j
        simp only [Matrix.zero_apply]
        exact hA0entry i j
      have hperm0 : Matrix.permanent
          ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) = 0 := by
        rw [hA0mat, Matrix.permanent_zero]
      have hE0 : Finset.univ.filter
          (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∉ used i) = ∅ := by
        apply Finset.filter_false_of_mem
        intro σ _
        push_neg
        refine ⟨⟨0, hn⟩, ?_⟩
        by_contra hc
        have h1 := hA0entry ⟨0, hn⟩ (σ ⟨0, hn⟩)
        have h2 : ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ)
            ⟨0, hn⟩ (σ ⟨0, hn⟩) = 1 := by
          show (if σ ⟨0, hn⟩ ∈ used ⟨0, hn⟩ then (0 : ℝ) else (1 : ℝ)) = 1
          exact if_neg hc
        rw [h2] at h1
        norm_num at h1
      rw [hE0, Finset.card_empty, Nat.cast_zero, hD0, zero_pow hn.ne', zero_mul]
    · have hdR : ((((n - k : ℕ))) : ℝ) ≠ 0 := by
        exact_mod_cast hdpos.ne'
      set D : ℝ := ((((n - k : ℕ))) : ℝ) with hD
      set N : Matrix (Fin n) (Fin n) ℝ :=
        (fun i j => D⁻¹ * (if j ∈ used i then (0 : ℝ) else (1 : ℝ))) with hN
      have hM : ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ)
          = D • N := by
        rw [hN]
        ext i j
        simp only [Matrix.smul_apply, smul_eq_mul]
        exact (mul_inv_cancel_left₀ hdR _).symm
      have hNnn : ∀ i j, 0 ≤ N i j := by
        intro i j
        rw [hN]
        show 0 ≤ D⁻¹ * (if j ∈ used i then (0 : ℝ) else (1 : ℝ))
        apply mul_nonneg _ (hnnA i j)
        rw [hD]
        exact inv_nonneg.mpr (Nat.cast_nonneg _)
      have hNrow : ∀ i, ∑ j, N i j = 1 := by
        intro i
        rw [hN]
        show (∑ j, D⁻¹ * (if j ∈ used i then (0 : ℝ) else (1 : ℝ))) = 1
        rw [← Finset.mul_sum, hrowsum i]
        exact inv_mul_cancel₀ hdR
      have hNcol : ∀ j, ∑ i, N i j = 1 := by
        intro j
        rw [hN]
        show (∑ i, D⁻¹ * (if j ∈ used i then (0 : ℝ) else (1 : ℝ))) = 1
        rw [← Finset.mul_sum, hcolsum j]
        exact inv_mul_cancel₀ hdR
      have hfin : D ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n)
          ≤ Matrix.permanent
            ((fun i s => if s ∈ used i then (0 : ℝ) else (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) := by
        rw [hM, Matrix.permanent_smul, Fintype.card_fin]
        apply mul_le_mul_of_nonneg_left (hvdW N hNnn hNrow hNcol) _
        rw [hD]
        exact pow_nonneg (Nat.cast_nonneg _) _
      rw [← hbij, ← hcardU2]
      exact hfin
