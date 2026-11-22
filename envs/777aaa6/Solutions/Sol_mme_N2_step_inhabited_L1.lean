-- Prove2me | solution 1 for mme_N2_step_inhabited_L1
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-20T00:04:47.068375+00:00
-- url     : https://prove2.me/submissions/2bb71aff-b14b-4f83-ac10-fa6e8da1bc15

import Definitions.Def_mme_integer_regional_CW_recipe

set_option autoImplicit false

open MME MME.RegionRealization MME.RecursiveYZ MME.RecursiveThinSplit MME.CompleteSplit

theorem solution : exists (S : MME.RegionRealization.IntegerStep 1 2 (fun _ _ => True)), True := by
  let half : ℕ := 2
  let R : ℕ := 1
  let parent : Fin R → Fin 3 → ℕ := fun _ => ![1, 1, 2]
  let n : Fin R → ℕ := fun _ => 1
  let htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half := by
    intro r
    have hr : r = 0 := Subsingleton.elim r 0
    subst hr
    decide
  let half_eq : half = 2 * 2 ^ (1 - 1) := by decide
  let s0 : RecursiveThinSplit.Split half (parent 0) :=
    ⟨![1, 1, 0], by decide, by intro i; fin_cases i <;> decide⟩
  let sOf : ∀ r, RecursiveThinSplit.Split half (parent r) := fun r => s0
  let m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ :=
    fun r a => if a = sOf r then 1 else 0
  let N : ℕ := 0
  let hHash : Fintype.card ((r : Fin R) × Fin (n r)) = 1 := by decide
  let hashPositions : Fin (N + 1) ≃ (r : Fin R) × Fin (n r) :=
    (Fintype.equivFinOfCardEq (by decide : Fintype.card (Fin (N + 1)) = 1)).trans
      (Fintype.equivFinOfCardEq hHash).symm
  let L : ℕ := 2
  let hPos : Fintype.card (MME.RecursiveYZ.Position n) = 2 := by decide
  let positions : Fin L ≃ MME.RecursiveYZ.Position n :=
    (Fintype.equivFinOfCardEq (by decide : Fintype.card (Fin L) = 2)).trans
      (Fintype.equivFinOfCardEq hPos).symm
  let length : L * 2 ^ (1 - 1) = 2 := by decide
  let z : Fin (2 ^ (1 - 1)) := ⟨0, by decide⟩
  let mu : Fin 3 → MME.RecursiveYZ.Cell half R parent → CompleteWord 1 → ℕ :=
    fun i c w =>
      if (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1)) ∧
          (w z).val = (c.2.val i).val then 1 else 0
  have mu_eq : ∀ (i : Fin 3) (c : MME.RecursiveYZ.Cell half R parent) (w : CompleteWord 1),
      mu i c w =
        (if (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1)) ∧
            (w z).val = (c.2.val i).val then (1 : ℕ) else 0) :=
    fun i c w => rfl
  have hne : ∀ (r : Fin R) (s : RecursiveThinSplit.Split half (parent r)),
      complement (htotal r) s ≠ s := by
    intro r s h
    have h0 := congrArg
      (fun t : RecursiveThinSplit.Split half (parent r) => (t.val 0).val) h
    have hp0 : parent r 0 = 1 := by
      have hr : r = 0 := Subsingleton.elim r 0
      subst hr
      decide
    have hle := s.property.2 0
    change parent r 0 - (s.val 0).val = (s.val 0).val at h0
    omega
  let reference : MME.RecursiveYZ.Address half R parent n := fun r _ => sOf r
  have ref_eq : ∀ (r : Fin R) (t : Fin (n r)), reference r t = sOf r :=
    fun r t => rfl
  have hn1 : ∀ r : Fin R, n r = 1 := fun r => rfl
  have hval : ∀ j : Fin (2 ^ (1 - 1)), j.val = 0 := by
    intro j
    have hlt := j.isLt
    have hK : 2 ^ (1 - 1) = 1 := by decide
    omega
  have hj0 : ∀ j : Fin (2 ^ (1 - 1)), j = z := fun j => Fin.ext (by rw [hval j])
  have mu0 : ∀ (j : Fin 3) (d : MME.RecursiveYZ.Cell half R parent) (v : CompleteWord 1),
      ¬(d.2 = sOf d.1 ∨ d.2 = complement (htotal d.1) (sOf d.1)) → mu j d v = 0 := by
    intro j d v hneg
    rw [mu_eq, if_neg (fun h => hneg h.1)]
  have hcard1 : Fintype.card (Fin (2 ^ (1 - 1))) = 1 := by decide
  refine ⟨⟨half, R, parent, n, htotal, half_eq, m, N, hashPositions, L, positions, length, mu,
    ?_, ?_, ?_, reference, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial⟩
  · -- mass
    intro i c
    have hm : m c.1 c.2 + m c.1 (complement (htotal c.1) c.2) =
        (if c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1) then (1 : ℕ) else 0) := by
      by_cases h1 : c.2 = sOf c.1
      · have h2 : complement (htotal c.1) c.2 ≠ sOf c.1 := by
          rw [h1]; exact hne c.1 (sOf c.1)
        show (if c.2 = sOf c.1 then (1 : ℕ) else 0) +
          (if complement (htotal c.1) c.2 = sOf c.1 then 1 else 0) = _
        rw [if_pos h1, if_neg h2, if_pos (Or.inl h1)]
      · by_cases h2 : c.2 = complement (htotal c.1) (sOf c.1)
        · have h3 : complement (htotal c.1) c.2 = sOf c.1 := by
            rw [h2, complement_complement]
          show (if c.2 = sOf c.1 then (1 : ℕ) else 0) +
            (if complement (htotal c.1) c.2 = sOf c.1 then 1 else 0) = _
          rw [if_neg h1, if_pos h3, if_pos (Or.inr h2)]
        · have hn2 : ¬ complement (htotal c.1) c.2 = sOf c.1 := by
            intro hc2
            apply h2
            have hcc := congrArg (complement (htotal c.1)) hc2
            rw [complement_complement] at hcc
            exact hcc
          show (if c.2 = sOf c.1 then (1 : ℕ) else 0) +
            (if complement (htotal c.1) c.2 = sOf c.1 then 1 else 0) = _
          rw [if_neg h1, if_neg hn2, if_neg (fun h => h.elim h1 h2)]
    rw [hm]
    by_cases hc : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1))
    · rw [if_pos hc]
      have hu : ∀ w : CompleteWord 1, mu i c w =
          (if (w z).val = (c.2.val i).val then (1 : ℕ) else 0) := by
        intro w
        rw [mu_eq]
        by_cases hg : (w z).val = (c.2.val i).val
        · have hconj : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1)) ∧
              (w z).val = (c.2.val i).val := ⟨hc, hg⟩
          rw [if_pos hconj, if_pos hg]
        · have hneg : ¬((c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1)) ∧
              (w z).val = (c.2.val i).val) := fun h => hg h.2
          rw [if_neg hneg, if_neg hg]
      let hw₀ : CompleteWord 1 :=
        fun _ => ⟨(c.2.val i).val, by show (c.2.val i).val < 3; exact (c.2.val i).isLt⟩
      have hwz : (hw₀ z).val = (c.2.val i).val := rfl
      refine (Finset.sum_eq_single hw₀ ?_ ?_).trans ?_
      · intro b _ hb
        rw [hu b, if_neg]
        intro hcon
        apply hb
        funext j
        rw [hj0 j]
        exact Fin.ext (hcon.trans hwz)
      · intro hcon
        exact absurd (Finset.mem_univ hw₀) hcon
      · rw [hu hw₀, if_pos hwz]
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro w _
      rw [mu_eq, if_neg]
      exact fun h => hc h.1
  · -- support
    intro i c w h
    have hP : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1)) ∧
        (w z).val = (c.2.val i).val := by
      by_contra hn
      have hz : mu i c w = 0 := by rw [mu_eq, if_neg hn]
      omega
    have h1 : ∀ h : Fin (2 ^ (1 - 1)), (w h).val = (w z).val := by
      intro h
      rw [hj0 h]
    have h2 : ∑ h : Fin (2 ^ (1 - 1)), (w h).val = ∑ _h : Fin (2 ^ (1 - 1)), (w z).val :=
      Finset.sum_congr rfl (fun h _ => h1 h)
    rw [h2, Finset.sum_const, Finset.card_univ, hcard1, nsmul_eq_mul, Nat.cast_one, one_mul]
    exact hP.2
  · -- boundary
    refine ⟨?_, ?_, ?_⟩
    · intro c h2 w
      by_cases hc : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1))
      · rcases hc with h | h
        · have g1 : ((sOf c.1).val 1).val = 1 := rfl
          have g0 : ((sOf c.1).val 0).val = 1 := rfl
          have hd : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1)) ↔ True :=
            iff_of_true (Or.inl h) True.intro
          simp only [mu_eq, hd, true_and]
          rw [h]
          rw [g1, g0]
          obtain ⟨y, hy⟩ : ∃ _y : Fin 3, w z = _y := ⟨_, rfl⟩
          rw [hy]
          fin_cases y <;> decide
        · exfalso
          rw [h] at h2
          have h22 : (((complement (htotal c.1) (sOf c.1)).val 2).val : ℕ) = 2 := by rfl
          omega
      · have e1 : mu 1 c w = 0 := mu0 _ _ _ hc
        have e2 : mu 0 c (fun r : Fin (2 ^ (1 - 1)) => Fin.rev (w r)) = 0 :=
          mu0 0 c (fun r : Fin (2 ^ (1 - 1)) => Fin.rev (w r)) hc
        rw [e1, e2]
    · intro c h0 w
      by_cases hc : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1))
      · rcases hc with h | h
        · exfalso
          rw [h] at h0
          have h00 : (((sOf c.1).val 0).val : ℕ) = 1 := by rfl
          omega
        · have g2 : ((complement (htotal c.1) (sOf c.1)).val 2).val = 2 := by rfl
          have g1 : ((complement (htotal c.1) (sOf c.1)).val 1).val = 0 := by rfl
          have hd : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1)) ↔ True :=
            iff_of_true (Or.inr h) True.intro
          simp only [mu_eq, hd, true_and]
          rw [h]
          rw [g2, g1]
          obtain ⟨y, hy⟩ : ∃ _y : Fin 3, w z = _y := ⟨_, rfl⟩
          rw [hy]
          fin_cases y <;> decide
      · have e1 : mu 2 c w = 0 := mu0 _ _ _ hc
        have e2 : mu 1 c (fun r : Fin (2 ^ (1 - 1)) => Fin.rev (w r)) = 0 :=
          mu0 1 c (fun r : Fin (2 ^ (1 - 1)) => Fin.rev (w r)) hc
        rw [e1, e2]
    · intro c h1 w
      by_cases hc : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1))
      · rcases hc with h | h
        · exfalso
          rw [h] at h1
          have h11 : (((sOf c.1).val 1).val : ℕ) = 1 := by rfl
          omega
        · have g2 : ((complement (htotal c.1) (sOf c.1)).val 2).val = 2 := by rfl
          have g0 : ((complement (htotal c.1) (sOf c.1)).val 0).val = 0 := by rfl
          have hd : (c.2 = sOf c.1 ∨ c.2 = complement (htotal c.1) (sOf c.1)) ↔ True :=
            iff_of_true (Or.inr h) True.intro
          simp only [mu_eq, hd, true_and]
          rw [h]
          rw [g2, g0]
          obtain ⟨y, hy⟩ : ∃ _y : Fin 3, w z = _y := ⟨_, rfl⟩
          rw [hy]
          fin_cases y <;> decide
      · have e1 : mu 2 c w = 0 := mu0 _ _ _ hc
        have e2 : mu 0 c (fun r : Fin (2 ^ (1 - 1)) => Fin.rev (w r)) = 0 :=
          mu0 0 c (fun r : Fin (2 ^ (1 - 1)) => Fin.rev (w r)) hc
        rw [e1, e2]
  · -- reference_target
    simp only [RecursiveXHash.target, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro r a
    have hfin1 : Fintype.card (Fin (n r)) = 1 := by
      show Fintype.card (Fin 1) = 1
      exact Fintype.card_fin 1
    by_cases h : a = sOf r
    · have hcount : RecursiveThinSplit.count (reference r) a = 1 := by
        show (Finset.univ.filter (fun j => reference r j = a)).card = 1
        have hf : ∀ j : Fin (n r), reference r j = a :=
          fun j => (ref_eq r j).trans h.symm
        rw [Finset.filter_true_of_mem (fun j _ => hf j), Finset.card_univ, hfin1]
      have hm1 : m r a = 1 := by
        show (if a = sOf r then (1 : ℕ) else 0) = 1
        rw [if_pos h]
      omega
    · have hcount : RecursiveThinSplit.count (reference r) a = 0 := by
        show (Finset.univ.filter (fun j => reference r j = a)).card = 0
        have hf : ∀ j : Fin (n r), ¬ reference r j = a :=
          fun j hcon => h ((hcon.symm).trans (ref_eq r j))
        rw [Finset.filter_false_of_mem (fun j _ => hf j), Finset.card_empty]
      have hm0 : m r a = 0 := by
        show (if a = sOf r then (1 : ℕ) else 0) = 0
        rw [if_neg h]
      omega
  · exact 1
  · exact 2
  · exact Nat.zero_lt_one
  · exact one_lt_two
  · intro r
    show (1 : ℕ) ≤ n r
    rw [hn1 r]
  · intro r c
    show (1 : ℕ) ∣ m r c
    exact one_dvd _
  · exact (100 : ℝ)
  · norm_num
  · have hR1 : R = 1 := rfl
    have hC3 : Fintype.card (CompleteWord 1) = 3 := by decide
    rw [hR1, hC3]
    norm_num
  · intro i x _
    exact True.intro
