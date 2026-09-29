-- Prove2me | solution 1 for mme_released_global_boundary_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T02:55:57.48609+00:00
-- url     : https://prove2.me/submissions/86e4d8a8-746e-4f82-a822-5c57f2d3b8ed

import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_released_global_frame_data

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false

private theorem row_marginal_sum (L : List (Fin 1296 × ℕ)) (i : Fin 3) (w : Word) :
    (∑ v : JointWord, if v i = w then
      (L.map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum else 0) =
      (L.map (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum := by
  classical
  induction L with
  | nil => simp
  | cons a L ih =>
    have hsum (v : JointWord) :
        (if v i = w then (if atom a.1 = v then a.2 else 0) +
          (L.map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum else 0) =
        (if v i = w then (if atom a.1 = v then a.2 else 0) else 0) +
          (if v i = w then (L.map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum
            else 0) := by
      by_cases h : v i = w <;> simp only [h, ite_true, ite_false, zero_add]
    simp only [List.map_cons, List.sum_cons]
    simp_rw [hsum]
    rw [Finset.sum_add_distrib, ih]
    have heq (v : JointWord) :
        (if v i = w then if atom a.1 = v then a.2 else 0 else 0) =
          if v = atom a.1 then (if atom a.1 i = w then a.2 else 0) else 0 := by
      by_cases hv : v = atom a.1
      · subst v; simp
      · simp [hv, Ne.symm hv]
    simp_rw [heq]
    simp

/-- The marginal of the released joint counts is the marginal of its finite
row list, multiplied by the coarse weight. This includes zero coarse weights. -/
private theorem mme_released_global_word_counts_row_marginal
    (owner : Fin 6) (c : Shape) (i : Fin 3) (w : Word) :
    wordCounts owner i c w = alpha owner (shapeEquiv.symm c) *
      ((jointRows owner (shapeEquiv.symm c)).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum := by
  classical
  unfold wordCounts jointCounts rowCounts
  rw [← row_marginal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

/-- Conditioning the global histogram center on a positive coarse cell removes
the global replication and its coarse weight, leaving the released row marginal. -/
private theorem mme_released_global_conditional_histogram_center
    (owner : Fin 6) (c : Shape) (hc : 0 < alpha owner (shapeEquiv.symm c))
    (k : ℕ) (hk : 0 < k) (i : Fin 3) (w : Word) :
    ((blocks k : ℝ) / ((k * coarseCounts owner c : ℕ) : ℝ)) *
        (profile owner).2 i ⟨0,c⟩ w =
      ((((jointRows owner (shapeEquiv.symm c)).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
          (denominator : ℝ)^4 := by
  change ((blocks k : ℝ) / ((k * coarseCounts owner c : ℕ) : ℝ)) *
    ((wordCounts owner i c w : ℝ) / (denominator : ℝ)^5) = _
  rw [mme_released_global_word_counts_row_marginal]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hcR : (alpha owner (shapeEquiv.symm c) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
  have hd : (denominator : ℝ) ≠ 0 := by norm_num [denominator]
  simp only [blocks, coarseCounts, Nat.cast_mul, Nat.cast_pow]
  field_simp


open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit

private theorem released_row_mass : ∀ (owner : Fin 6) (s : Fin 45),
    ((jointRows owner s).map Prod.snd).sum = denominator ^ 4 := by
  decide +kernel

private theorem released_row_support : ∀ (owner : Fin 6) (s : Fin 45),
    (jointRows owner s).all (fun a => decide
      (∀ i : Fin 3, CWCells.grade (atom a.1 i) = ((shapeEquiv s).val i).val)) = true := by
  decide +kernel

private theorem marginal_mass (L : List (Fin 1296 × ℕ)) (i : Fin 3) :
    (∑ w : Word, (L.map (fun a => if atom a.1 i = w then a.2 else 0)).sum) =
      (L.map Prod.snd).sum := by
  classical
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]
    simp

/-- Every released marginal has exactly the coarse cell mass. -/
private theorem mme_released_global_word_counts_mass
    (owner : Fin 6) (c : Shape) (i : Fin 3) :
    ∑ w, wordCounts owner i c w = coarseCounts owner c := by
  simp_rw [mme_released_global_word_counts_row_marginal]
  rw [← Finset.mul_sum, marginal_mass, released_row_mass]
  rfl

/-- Positive marginal counts occur only at the prescribed coarse grade. -/
private theorem mme_released_global_word_counts_grade_support
    (owner : Fin 6) (c : Shape) (i : Fin 3) (w : Word)
    (hw : 0 < wordCounts owner i c w) : CWCells.grade w = (c.val i).val := by
  classical
  by_contra hn
  have hs : ∀ a ∈ jointRows owner (shapeEquiv.symm c),
      ∀ i : Fin 3, CWCells.grade (atom a.1 i) = (c.val i).val := by
    simpa only [List.all_eq_true, decide_eq_true_eq, Equiv.apply_symm_apply] using
      released_row_support owner (shapeEquiv.symm c)
  have hz : ((jointRows owner (shapeEquiv.symm c)).map
      (fun a => if atom a.1 i = w then a.2 else 0)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have hne : atom a.1 i ≠ w := by
      intro h
      exact hn (h ▸ hs a ha i)
    simp only [if_neg hne]
  rw [mme_released_global_word_counts_row_marginal, hz, mul_zero] at hw
  exact (Nat.lt_irrefl 0) hw


private theorem atomic_boundary : ∀ a : Fin 1296,
    (CWCells.grade (atom a 2) = 0 → atom a 1 = fun r => Fin.rev (atom a 0 r)) ∧
    (CWCells.grade (atom a 0) = 0 → atom a 2 = fun r => Fin.rev (atom a 1 r)) ∧
    (CWCells.grade (atom a 1) = 0 → atom a 2 = fun r => Fin.rev (atom a 0 r)) := by
  decide +kernel

private theorem row_grade (owner : Fin 6) (c : Shape)
    (a : Fin 1296 × ℕ) (ha : a ∈ jointRows owner (shapeEquiv.symm c)) (i : Fin 3) :
    CWCells.grade (atom a.1 i) = (c.val i).val := by
  have hs : ∀ a ∈ jointRows owner (shapeEquiv.symm c),
      ∀ i : Fin 3, CWCells.grade (atom a.1 i) = (c.val i).val := by
    simpa only [List.all_eq_true, decide_eq_true_eq, Equiv.apply_symm_apply] using
      released_row_support owner (shapeEquiv.symm c)
  exact hs a ha i

private theorem marginal_reverse (L : List (Fin 1296 × ℕ)) (i j : Fin 3)
    (h : ∀ a ∈ L, atom a.1 i = fun r => Fin.rev (atom a.1 j r)) (w : Word) :
    (L.map (fun a => if atom a.1 i = w then a.2 else 0)).sum =
      (L.map (fun a => if atom a.1 j = (fun r => Fin.rev (w r)) then a.2 else 0)).sum := by
  classical
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have heq : atom a.1 i = w ↔ atom a.1 j = (fun r => Fin.rev (w r)) := by
    rw [h a ha]
    constructor
    · intro hw
      funext r
      have hh := congrArg (fun f => Fin.rev (f r)) hw
      simpa using hh
    · intro hw
      funext r
      simp only [hw, Fin.rev_rev]
  simp only [heq]

/-- Released boundary marginals satisfy the complementary-word identities in
all three zero-coordinate orientations. -/
private theorem mme_released_global_word_counts_boundary_profiles (owner : Fin 6) :
    BoundaryProfiles (fun i (c : Cell 8 1 (fun _ _ ↦ 8)) w => wordCounts owner i c.2 w) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c hz w
    dsimp only
    rw [mme_released_global_word_counts_row_marginal,
      mme_released_global_word_counts_row_marginal]
    apply congrArg (alpha owner (shapeEquiv.symm c.2) * ·)
    apply marginal_reverse
    intro a ha
    exact (atomic_boundary a.1).1 ((row_grade owner c.2 a ha 2).trans hz)
  · intro c hz w
    dsimp only
    rw [mme_released_global_word_counts_row_marginal,
      mme_released_global_word_counts_row_marginal]
    apply congrArg (alpha owner (shapeEquiv.symm c.2) * ·)
    apply marginal_reverse
    intro a ha
    exact (atomic_boundary a.1).2.1 ((row_grade owner c.2 a ha 0).trans hz)
  · intro c hz w
    dsimp only
    rw [mme_released_global_word_counts_row_marginal,
      mme_released_global_word_counts_row_marginal]
    apply congrArg (alpha owner (shapeEquiv.symm c.2) * ·)
    apply marginal_reverse
    intro a ha
    exact (atomic_boundary a.1).2.2 ((row_grade owner c.2 a ha 1).trans hz)


open MME.TensorObj MME.RecursiveYZ.Boundary
universe u

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

/-- Exact boundary profiles follow from mass, grade support, and the
boundary reversal identities, without requiring a hash stage. -/
private theorem mme_cell_boundary_profile_of_mass_support
    {half R ell L : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (c : Cell half R parent) (hhalf : half = 2 * 2 ^ (ell - 1))
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (hmass : ∀ i, ∑ s, mu i c s = L) (hboundary : BoundaryProfiles mu)
    (z : Fin 3) (hz : (c.2.val z).val = 0)
    (hg : ∀ i s, 0 < mu i c s → CWCells.grade s = (c.2.val i).val) :
    ∃ B : Boundary.Profile ell L,
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i, mu i c = B.mu z i) := by
  classical
  let cell := c
  have hm (i : Fin 3) : ∑ s, mu i cell s = L := hmass i
  have ht := cell.2.property.1.trans hhalf
  have hb (i : Fin 3) : (cell.2.val i).val ≤ 2 * 2 ^ (ell - 1) := by
    have h := (cell.2.val i).isLt
    rw [← hhalf]
    omega
  have hzero : mu z cell = fun s ↦ if s = (fun _ ↦ 0) then L else 0 :=
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
      ⟨(cell.2.val 1).val, hb 1, mu 1 cell, hm 1,
        fun s hs ↦ hg 1 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hz
      · rfl
      · change (cell.2.val 2).val = 2 * 2 ^ (ell - 1) - (cell.2.val 1).val
        change (cell.2.val 0).val = 0 at hz
        omega
    · intro i
      fin_cases i
      · exact hzero
      · rfl
      · funext s
        change mu 2 cell s = mu 1 cell (flipLabel s)
        rw [flipLabel_eq_rev]
        exact hboundary.2.1 cell hz s
  · let B : Boundary.Profile ell (L) :=
      ⟨(cell.2.val 2).val, hb 2, mu 2 cell, hm 2,
        fun s hs ↦ hg 2 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · change (cell.2.val 0).val = 2 * 2 ^ (ell - 1) - (cell.2.val 2).val
        change (cell.2.val 1).val = 0 at hz
        omega
      · exact hz
      · rfl
    · intro i
      fin_cases i
      · funext s
        change mu 0 cell s = mu 2 cell (flipLabel s)
        rw [hboundary.2.2 cell hz, ← flipLabel_eq_rev, hrevs]
      · exact hzero
      · rfl
  · let B : Boundary.Profile ell (L) :=
      ⟨(cell.2.val 0).val, hb 0, mu 0 cell, hm 0,
        fun s hs ↦ hg 0 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · rfl
      · change (cell.2.val 1).val = 2 * 2 ^ (ell - 1) - (cell.2.val 0).val
        change (cell.2.val 2).val = 0 at hz
        omega
      · exact hz
    · intro i
      fin_cases i
      · rfl
      · funext s
        change mu 1 cell s = mu 0 cell (flipLabel s)
        rw [flipLabel_eq_rev]
        exact hboundary.1 cell hz s
      · exact hzero



private theorem boundary_dim_pos {ell L : ℕ} (B : Boundary.Profile ell L) :
    0 < B.dim := by
  have hm : 0 < L.factorial / ∏ w, (B.count w).factorial := by
    simpa only [Nat.multinomial, B.total] using Nat.multinomial_pos Finset.univ B.count
  exact Nat.mul_pos hm (by positivity)

private theorem boundary_volume {ell L : ℕ} (B : Boundary.Profile ell L) (z : Fin 3) :
    B.a z * B.b z * B.c z = B.dim := by
  fin_cases z <;> simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]

private theorem global_scaled_boundary_profiles (owner : Fin 6) (k : ℕ) :
    BoundaryProfiles (fun i (c : Cell 8 1 (fun _ _ ↦ 8)) w => k * wordCounts owner i c.2 w) := by
  obtain ⟨h2, h0, h1⟩ := mme_released_global_word_counts_boundary_profiles owner
  exact ⟨fun c hc w => congrArg (k * ·) (h2 c hc w),
    fun c hc w => congrArg (k * ·) (h0 c hc w),
    fun c hc w => congrArg (k * ·) (h1 c hc w)⟩

/-- Every physical boundary cell has an exact matrix extraction at every
integer replication. Shape and histogram equalities are retained so the
result can be assembled with the interior cells. -/
theorem solution
    (owner : Fin 6) (k : ℕ) (c : Cell 8 1 (fun _ _ ↦ 8)) (z : Fin 3)
    (hz : (c.2.val z).val = 0) :
    ∃ B : Boundary.Profile 3
        (k * (coarseCounts owner c.2)),
      0 < B.dim ∧ B.a z * B.b z * B.c z = B.dim ∧
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i w, k * wordCounts owner i c.2 w = B.mu z i w) ∧
      ∀ (K : Type u) [Field K],
        TensorObj.Restrict (MMObj K (B.a z) (B.b z) (B.c z))
          (CWCells.unbroken K 5 3
            (k * (coarseCounts owner c.2))
            (Equiv.refl _) (fun _ => Unit.unit)
            (fun _ i => (c.2.val i).val)
            (fun i _ w => k * wordCounts owner i c.2 w)) := by
  have hmass (i : Fin 3) : ∑ w, k * wordCounts owner i c.2 w =
      k * (coarseCounts owner c.2) := by
    rw [← Finset.mul_sum, mme_released_global_word_counts_mass]
  have hg (i : Fin 3) (w : CompleteWord 3) (hw : 0 < k * wordCounts owner i c.2 w) :
      CWCells.grade w = (c.2.val i).val := by
    exact mme_released_global_word_counts_grade_support owner c.2 i w (Nat.pos_of_mul_pos_left hw)
  obtain ⟨B, hshape, hmu⟩ := mme_cell_boundary_profile_of_mass_support c rfl
    (fun i c w => k * wordCounts owner i c.2 w) hmass (global_scaled_boundary_profiles owner k) z hz hg
  refine ⟨B, boundary_dim_pos B, boundary_volume B z, hshape,
    fun i w => congrFun (hmu i) w, ?_⟩
  intro K _
  have h := mme_recursive_yz_boundary_actual_matrix_extraction (K := K) B z
  have hmu_point (i : Fin 3) (w : CompleteWord 3) :
      k * wordCounts owner i c.2 w = B.mu z i w := congrFun (hmu i) w
  simpa only [Boundary.Profile.tensor, hshape, hmu_point] using h


#print axioms solution
