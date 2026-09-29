-- Prove2me | solution 1 for mme_boundary_profile_of_histogram_support
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:53:30.69242+00:00
-- url     : https://prove2.me/submissions/e33d513d-2591-43b0-8421-4c196cfe710c

import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false

private theorem word_grade_zero {ell : ℕ} (s : CompleteWord ell)
    (h : CWCells.grade s = 0) : s = fun _ ↦ 0 := by
  funext r
  apply Fin.ext
  have hh : ∀ r, (s r).val = 0 := by
    simpa [CWCells.grade] using (Finset.sum_eq_zero_iff_of_nonneg
      (fun r (_ : r ∈ (Finset.univ : Finset (Fin (2 ^ (ell - 1))))) ↦ Nat.zero_le (s r).val)).mp h
  exact hh r

private theorem zero_profile {ell L : ℕ} (mu : CompleteWord ell → ℕ)
    (hmass : ∑ s, mu s = L)
    (hgrade : ∀ s, 0 < mu s → CWCells.grade s = 0) :
    mu = fun s ↦ if s = (fun _ ↦ 0) then L else 0 := by
  classical
  have hs (s : CompleteWord ell) (h : s ≠ fun _ ↦ 0) : mu s = 0 := by
    by_contra hn
    exact h (word_grade_zero s (hgrade s (Nat.pos_of_ne_zero hn)))
  have hz : mu (fun _ ↦ 0) = L := by
    calc
      mu (fun _ ↦ 0) = ∑ s, mu s := (Finset.sum_eq_single (fun _ ↦ 0)
        (fun s _ h ↦ hs s h) (by simp)).symm
      _ = L := hmass
  funext s
  by_cases h : s = fun _ ↦ 0
  · simp [h, hz]
  · simp [h, hs s h]

private theorem flipLabel_eq_rev {ell : ℕ} (s : CompleteWord ell) :
    flipLabel s = fun r ↦ Fin.rev (s r) := by
  funext r
  apply Fin.ext
  simp [flipLabel, Fin.rev]

/-- An exact complementary profile is determined by mass and grade support. -/
theorem solution
    (ell L : ℕ) (shape : Fin 3 → ℕ) (mu : Fin 3 → CompleteWord ell → ℕ)
    (ht : shape 0 + shape 1 + shape 2 = 2 * 2 ^ (ell - 1))
    (hm : ∀ i, ∑ s, mu i s = L)
    (hg : ∀ i s, 0 < mu i s → grade s = shape i)
    (hboundary :
      (shape 2 = 0 → ∀ s, mu 1 s = mu 0 (fun r ↦ Fin.rev (s r))) ∧
      (shape 0 = 0 → ∀ s, mu 2 s = mu 1 (fun r ↦ Fin.rev (s r))) ∧
      (shape 1 = 0 → ∀ s, mu 2 s = mu 0 (fun r ↦ Fin.rev (s r))))
    (z : Fin 3) (hz : shape z = 0) :
    ∃ B : Boundary.Profile ell L,
      (∀ i, shape i = B.shape z i) ∧ (∀ i, mu i = B.mu z i) := by
  classical
  have hb (i : Fin 3) : shape i ≤ 2 * 2 ^ (ell - 1) := by
    fin_cases i <;> dsimp <;> omega
  have hzero : mu z = fun s ↦ if s = (fun _ ↦ 0) then L else 0 :=
    zero_profile _ (hm z) (fun s hs ↦ (hg z s hs).trans hz)
  have hrevs (s : CompleteWord ell) :
      flipLabel (flipLabel s) = s := by
    funext r
    apply Fin.ext
    simp only [flipLabel]
    have := (s r).isLt
    omega
  fin_cases z
  · let B : Boundary.Profile ell (L) :=
      ⟨shape 1, hb 1, mu 1, hm 1,
        fun s hs ↦ hg 1 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hz
      · rfl
      · change shape 2 = 2 * 2 ^ (ell - 1) - shape 1
        change shape 0 = 0 at hz
        omega
    · intro i
      fin_cases i
      · exact hzero
      · rfl
      · funext s
        change mu 2 s = mu 1 (flipLabel s)
        rw [flipLabel_eq_rev]
        exact hboundary.2.1 hz s
  · let B : Boundary.Profile ell (L) :=
      ⟨shape 2, hb 2, mu 2, hm 2,
        fun s hs ↦ hg 2 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · change shape 0 = 2 * 2 ^ (ell - 1) - shape 2
        change shape 1 = 0 at hz
        omega
      · exact hz
      · rfl
    · intro i
      fin_cases i
      · funext s
        change mu 0 s = mu 2 (flipLabel s)
        rw [hboundary.2.2 hz, ← flipLabel_eq_rev, hrevs]
      · exact hzero
      · rfl
  · let B : Boundary.Profile ell (L) :=
      ⟨shape 0, hb 0, mu 0, hm 0,
        fun s hs ↦ hg 0 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · rfl
      · change shape 1 = 2 * 2 ^ (ell - 1) - shape 0
        change shape 2 = 0 at hz
        omega
      · exact hz
    · intro i
      fin_cases i
      · rfl
      · funext s
        change mu 1 s = mu 0 (flipLabel s)
        rw [flipLabel_eq_rev]
        exact hboundary.1 hz s
      · exact hzero


#print axioms solution
