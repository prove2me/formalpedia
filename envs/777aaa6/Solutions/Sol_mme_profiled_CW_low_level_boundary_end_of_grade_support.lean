-- Prove2me | solution 1 for mme_profiled_CW_low_level_boundary_end_of_grade_support
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:53:32.157288+00:00
-- url     : https://prove2.me/submissions/5c403153-e4b9-48e0-96e0-424318cc5e58

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
theorem mme_boundary_profile_of_histogram_support
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


#print axioms mme_boundary_profile_of_histogram_support

/-- Complementary boundary histograms construct a terminal recipe interface. -/
theorem mme_profiled_CW_boundary_end_of_histogram_support
    (ell L cells : ℕ) (cell : Fin L → Fin cells)
    (part : Partition cell) (shape : Fin cells → Fin 3 → ℕ)
    (mu : Fin 3 → Fin cells → CompleteWord ell → ℕ)
    (P : Predicate (L * 2 ^ (ell - 1)))
    (ht : ∀ j, shape (part.cells j) 0 + shape (part.cells j) 1 +
      shape (part.cells j) 2 = 2 * 2 ^ (ell - 1))
    (hm : ∀ j i, ∑ s, mu i (part.cells j) s = part.size j)
    (hg : ∀ j i s, 0 < mu i (part.cells j) s → grade s = shape (part.cells j) i)
    (hboundary : ∀ j,
      (shape (part.cells j) 2 = 0 → ∀ s,
        mu 1 (part.cells j) s = mu 0 (part.cells j) (fun r ↦ Fin.rev (s r))) ∧
      (shape (part.cells j) 0 = 0 → ∀ s,
        mu 2 (part.cells j) s = mu 1 (part.cells j) (fun r ↦ Fin.rev (s r))) ∧
      (shape (part.cells j) 1 = 0 → ∀ s,
        mu 2 (part.cells j) s = mu 0 (part.cells j) (fun r ↦ Fin.rev (s r))))
    (hz : ∀ j, ∃ z, shape (part.cells j) z = 0)
    (hinside : ∀ i x,
      ((∀ p, grade (split (Equiv.refl (Fin L)) rfl x p) = shape (cell p) i) ∧
        Useful cell (mu i) (split (Equiv.refl (Fin L)) rfl x)) → P i x) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, shape (part.cells j) i = (profiles j).shape (z j) i) ∧
      (∀ j i, mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ B : BoundaryEnd ell (L * 2 ^ (ell - 1)) P,
        B.a = ∏ j, (profiles j).a (z j) ∧
        B.b = ∏ j, (profiles j).b (z j) ∧
        B.c = ∏ j, (profiles j).c (z j) := by
  classical
  choose z hz using hz
  have hex (j : Fin part.parts) := mme_boundary_profile_of_histogram_support
    ell (part.size j) (shape (part.cells j)) (fun i ↦ mu i (part.cells j))
    (ht j) (hm j) (hg j) (hboundary j) (z j) (hz j)
  choose B hshape hmu using hex
  refine ⟨z, B, hshape, hmu, {
    L := L
    cells := cells
    length := rfl
    cell := cell
    shape := shape
    mu := mu
    partition := part
    profile := B
    zeroMode := z
    shapes := fun j ↦ funext (hshape j)
    profiles := hmu
    inside := hinside }, rfl, rfl, rfl⟩

#print axioms mme_profiled_CW_boundary_end_of_histogram_support

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

private theorem low_histogram_unique {ell : ℕ} (hlevel : ell ≤ 1)
    (mu nu : CompleteWord ell → ℕ) (index : ℕ)
    (hmass : ∑ s, mu s = ∑ s, nu s)
    (hmu : ∀ s, 0 < mu s → grade s = index)
    (hnu : ∀ s, 0 < nu s → grade s = index) : mu = nu := by
  classical
  funext s
  by_cases hs : grade s = index
  · have hsum (f : CompleteWord ell → ℕ) (hf : ∀ t, 0 < f t → grade t = index) :
        ∑ t, f t = f s := by
      apply Finset.sum_eq_single s
      · intro t _ ht
        by_contra hzero
        exact ht (low_word_grade_injective hlevel t s ((hf t (Nat.pos_of_ne_zero hzero)).trans hs.symm))
      · simp
    rw [hsum mu hmu, hsum nu hnu] at hmass
    exact hmass
  · have hzero (f : CompleteWord ell → ℕ) (hf : ∀ t, 0 < f t → grade t = index) : f s = 0 := by
      by_contra hn
      exact hs (hf s (Nat.pos_of_ne_zero hn))
    rw [hzero mu hmu, hzero nu hnu]

private theorem low_grade_rev {ell : ℕ} (hlevel : ell ≤ 1) (s : CompleteWord ell) :
    grade (fun r ↦ Fin.rev (s r)) = 2 - grade s := by
  have hell : ell = 0 ∨ ell = 1 := by omega
  rcases hell with rfl | rfl <;> simp [CWCells.grade, Fin.rev]

private theorem low_complementary_histograms {ell L : ℕ} (hlevel : ell ≤ 1)
    (mu nu : CompleteWord ell → ℕ) (a b : ℕ) (hab : a + b = 2)
    (hmu : ∑ s, mu s = L) (hnu : ∑ s, nu s = L)
    (hgmu : ∀ s, 0 < mu s → grade s = a)
    (hgnu : ∀ s, 0 < nu s → grade s = b) :
    ∀ s, nu s = mu (fun r ↦ Fin.rev (s r)) := by
  let e : Equiv.Perm (CompleteWord ell) := Equiv.piCongrRight (fun _ ↦ Fin.revPerm)
  have he (s : CompleteWord ell) : e s = fun r ↦ Fin.rev (s r) := rfl
  have hmass : ∑ s, nu s = ∑ s, mu (e s) := by
    rw [Equiv.sum_comp e mu, hmu, hnu]
  have hg : ∀ s, 0 < mu (e s) → grade s = b := by
    intro s hs
    have h := hgmu (e s) hs
    rw [he, low_grade_rev hlevel] at h
    have hsbound : grade s ≤ 2 := by
      have hell : ell = 0 ∨ ell = 1 := by omega
      rcases hell with rfl | rfl
      all_goals
        have hh := (s 0).isLt
        simp [CWCells.grade]
        omega
    omega
  exact congrFun (low_histogram_unique hlevel nu (fun s ↦ mu (e s)) b hmass hgnu hg)

/-- At elementary depth, mass and grade support already give a terminal boundary interface. -/
theorem solution
    (ell L cells : ℕ) (hlevel : ell ≤ 1) (cell : Fin L → Fin cells)
    (part : Partition cell) (shape : Fin cells → Fin 3 → ℕ)
    (mu : Fin 3 → Fin cells → CompleteWord ell → ℕ)
    (P : Predicate (L * 2 ^ (ell - 1)))
    (ht : ∀ j, shape (part.cells j) 0 + shape (part.cells j) 1 +
      shape (part.cells j) 2 = 2 * 2 ^ (ell - 1))
    (hm : ∀ j i, ∑ s, mu i (part.cells j) s = part.size j)
    (hg : ∀ j i s, 0 < mu i (part.cells j) s → grade s = shape (part.cells j) i)
    (hinside : ∀ i x,
      ((∀ p, grade (split (Equiv.refl (Fin L)) rfl x p) = shape (cell p) i) ∧
        Useful cell (mu i) (split (Equiv.refl (Fin L)) rfl x)) → P i x) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, shape (part.cells j) i = (profiles j).shape (z j) i) ∧
      (∀ j i, mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ B : BoundaryEnd ell (L * 2 ^ (ell - 1)) P,
        B.a = ∏ j, (profiles j).a (z j) ∧
        B.b = ∏ j, (profiles j).b (z j) ∧
        B.c = ∏ j, (profiles j).c (z j) := by
  have ht' (j : Fin part.parts) : shape (part.cells j) 0 + shape (part.cells j) 1 +
      shape (part.cells j) 2 = 2 := by
    simpa only [Nat.sub_eq_zero_of_le hlevel, pow_zero, mul_one] using ht j
  apply mme_profiled_CW_boundary_end_of_histogram_support ell L cells cell part shape mu P ht hm hg
  · intro j
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      exact low_complementary_histograms hlevel _ _ _ _ (by have := ht' j; omega)
        (hm j 0) (hm j 1) (hg j 0) (hg j 1)
    · intro hz
      exact low_complementary_histograms hlevel _ _ _ _ (by have := ht' j; omega)
        (hm j 1) (hm j 2) (hg j 1) (hg j 2)
    · intro hz
      exact low_complementary_histograms hlevel _ _ _ _ (by have := ht' j; omega)
        (hm j 0) (hm j 2) (hg j 0) (hg j 2)
  · intro j
    have hh := ht' j
    by_contra hn
    push_neg at hn
    have h0 := hn 0
    have h1 := hn 1
    have h2 := hn 2
    omega
  · exact hinside

#print axioms solution
