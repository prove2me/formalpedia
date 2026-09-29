-- Prove2me | solution 1 for mme_low_level_boundary_profile_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T12:28:20.813994+00:00
-- url     : https://prove2.me/submissions/89a027f5-0050-4620-8b68-7f311cda23cc

import Definitions.Def_mme_recursive_yz_boundary_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary
set_option autoImplicit false

private theorem low_word_grade_injective {ell : ℕ} (hlevel : ell ≤ 1)
    (s t : CompleteWord ell) (h : grade s = grade t) : s = t := by
  have hell : ell = 0 ∨ ell = 1 := by omega
  rcases hell with rfl | rfl
  all_goals
    have he : (s 0).val = (t 0).val := by simpa [CWCells.grade] using h
    funext r
    have hr : r = 0 := by fin_cases r; rfl
    subst r
    exact Fin.ext he

/-- At elementary depth the boundary histogram is supported on one word, so its
matrix dimension is a pure power of five exactly when the free grade is one. -/
theorem solution
    {ell L : ℕ} (B : Boundary.Profile ell L) (hlevel : ell ≤ 1) :
    B.dim = if B.index = 1 then 5 ^ L else 1 := by
  classical
  have hn : 2 ^ (ell - 1) = 1 := by simp [Nat.sub_eq_zero_of_le hlevel]
  have hi : B.index < 3 := by have := B.index_le; rw [hn] at this; omega
  let w : CompleteWord ell := fun _ ↦ ⟨B.index, hi⟩
  have hw : grade w = B.index := by simp [CWCells.grade, w, hn]
  have hz (s : CompleteWord ell) (hs : s ≠ w) : B.count s = 0 := by
    by_contra h
    exact hs (low_word_grade_injective hlevel s w ((B.supported s h).trans hw.symm))
  have hc : B.count w = L := by
    exact (Finset.sum_eq_single w (fun s _ hs ↦ hz s hs) (by simp)).symm.trans B.total
  have hp : ∏ s, (B.count s).factorial = L.factorial := by
    calc
      _ = (B.count w).factorial := by
        apply Finset.prod_eq_single w
        · intro s _ hs
          simp [hz s hs]
        · simp
      _ = L.factorial := congrArg Nat.factorial hc
  have hs : ∑ s, B.count s * ones s = L * ones w := by
    calc
      _ = B.count w * ones w := by
        apply Finset.sum_eq_single w
        · intro s _ hs
          simp [hz s hs]
        · simp
      _ = L * ones w := congrArg (fun n ↦ n * ones w) hc
  have ho : ones w = if B.index = 1 then 1 else 0 := by
    by_cases hi1 : B.index = 1
    · simp [ones, w, hi1, hn]
    · have he : (⟨B.index, hi⟩ : Fin 3) ≠ 1 := fun h ↦ hi1 (congrArg Fin.val h)
      simp [ones, w, he, hi1]
  rw [Boundary.Profile.dim, hp, hs, ho, Nat.div_self (Nat.factorial_pos L), one_mul]
  split_ifs <;> simp

#print axioms solution
