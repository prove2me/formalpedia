-- Prove2me | solution 1 for mme_released_interior_physical_boundary_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:48:35.376752+00:00
-- url     : https://prove2.me/submissions/198222ab-75e1-4279-8027-d2ae16b338e4

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.FinCases
import Definitions.Def_mme_recursive_yz_owned_filters
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction

import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
set_option autoImplicit false
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

open MME.ReleasedInterior

/-- Every boundary child of a released interior recipe has an exact matrix
extraction at every replication scale, including empty cells and scale zero. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (k : ℕ) (c : Cell 4 6 (parent s)) (z : Fin 3)
    (hz : (c.2.val z).val = 0) :
    ∃ B : Boundary.Profile 2
        (k * (splitCount owner s c.1 c.2 +
          splitCount owner s c.1 (complement (parent_total s c.1) c.2))),
      0 < B.dim ∧ B.a z * B.b z * B.c z = B.dim ∧
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i w, k * integerProfile owner s i c w = B.mu z i w) ∧
      ∀ (K : Type u) [Field K],
        TensorObj.Restrict (MMObj K (B.a z) (B.b z) (B.c z))
          (CWCells.unbroken K 5 2
            (k * (splitCount owner s c.1 c.2 +
              splitCount owner s c.1 (complement (parent_total s c.1) c.2)))
            (Equiv.refl _) (fun _ => Unit.unit)
            (fun _ i => (c.2.val i).val)
            (fun i _ w => k * integerProfile owner s i c w)) := by
  obtain ⟨reference, href, htotal, hmass₀, hgrade₀, hboundary₀, _⟩ :=
    mme_released_interior_scaled_integer_profile_constraints_exact owner s hi 1 (by decide)
  simp only [Nat.one_mul] at hmass₀ hgrade₀ hboundary₀
  have hmass (i : Fin 3) : ∑ w, k * integerProfile owner s i c w =
      k * (splitCount owner s c.1 c.2 +
        splitCount owner s c.1 (complement (parent_total s c.1) c.2)) := by
    rw [← Finset.mul_sum, hmass₀ i c]
  have hg (i : Fin 3) (w : CompleteWord 2)
      (hw : 0 < k * integerProfile owner s i c w) :
      CWCells.grade w = (c.2.val i).val :=
    hgrade₀ i c w (Nat.pos_of_mul_pos_left hw)
  have hb : BoundaryProfiles (fun i c w => k * integerProfile owner s i c w) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c hz w
      exact congrArg (k * ·) (hboundary₀.1 c hz w)
    · intro c hz w
      exact congrArg (k * ·) (hboundary₀.2.1 c hz w)
    · intro c hz w
      exact congrArg (k * ·) (hboundary₀.2.2 c hz w)
  obtain ⟨B, hshape, hmu⟩ := mme_cell_boundary_profile_of_mass_support c rfl
    (fun i c w => k * integerProfile owner s i c w) hmass hb z hz hg
  refine ⟨B, boundary_dim_pos B, boundary_volume B z, hshape,
    fun i w => congrFun (hmu i) w, ?_⟩
  intro K _
  have h := mme_recursive_yz_boundary_actual_matrix_extraction (K := K) B z
  have hmu_point (i : Fin 3) (w : CompleteWord 2) :
      k * integerProfile owner s i c w = B.mu z i w := congrFun (hmu i) w
  simpa only [Boundary.Profile.tensor, hshape, hmu_point] using h


#print axioms solution
