-- Prove2me | solution 1 for mme_released_116_full_child_product_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:39:00.176987+00:00
-- url     : https://prove2.me/submissions/b644c709-195c-4044-89e3-cfd897c94c2d

import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_released_116_integer_profile_boundary
import Definitions.Def_mme_recursive_yz_owned_filters
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Definitions.Def_mme_recursive_yz_boundary_data
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_finite_MM_extraction_swap_double
import Theorems.Thm_mme_complete_split_112_outer_star_entropy_rate
import Theorems.Thm_mme_central_binomial_sqrt_loss_log_rate
import Definitions.Def_mme_complete_split_112_address_words
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_primary_hash_uniform_stars_joint_directional_capacity
import Theorems.Thm_mme_complete_split_112_coupled_restricted_family_certificate
import Theorems.Thm_mme_complete_split_112_canonical_profile_router
import Theorems.Thm_mme_complete_split_112_canonical_power_restricts_from_intact
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Definitions.Def_mme_mmobj_mul
universe u

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
set_option autoImplicit false

private theorem fullChild0_word_grade_zero {ell : ℕ} (s : CompleteWord ell)
    (h : CWCells.grade s = 0) : s = fun _ ↦ 0 := by
  funext r
  apply Fin.ext
  have hh : ∀ r, (s r).val = 0 := by
    simpa [CWCells.grade] using (Finset.sum_eq_zero_iff_of_nonneg
      (fun r (_ : r ∈ (Finset.univ : Finset (Fin (2 ^ (ell - 1))))) ↦ Nat.zero_le (s r).val)).mp h
  exact hh r

private theorem fullChild0_zero_profile {ell L : ℕ} (mu : CompleteWord ell → ℕ)
    (hmass : ∑ s, mu s = L)
    (hgrade : ∀ s, 0 < mu s → CWCells.grade s = 0) :
    mu = fun s ↦ if s = (fun _ ↦ 0) then L else 0 := by
  classical
  have hs (s : CompleteWord ell) (h : s ≠ fun _ ↦ 0) : mu s = 0 := by
    by_contra hn
    exact h (fullChild0_word_grade_zero s (hgrade s (Nat.pos_of_ne_zero hn)))
  have hz : mu (fun _ ↦ 0) = L := by
    calc
      mu (fun _ ↦ 0) = ∑ s, mu s := (Finset.sum_eq_single (fun _ ↦ 0)
        (fun s _ h ↦ hs s h) (by simp)).symm
      _ = L := hmass
  funext s
  by_cases h : s = fun _ ↦ 0
  · simp [h, hz]
  · simp [h, hs s h]

private theorem fullChild0_flipLabel_eq_rev {ell : ℕ} (s : CompleteWord ell) :
    flipLabel s = fun r ↦ Fin.rev (s r) := by
  funext r
  apply Fin.ext
  simp [flipLabel, Fin.rev]

/-- Exact boundary profiles follow from mass, grade support, and the
boundary reversal identities, without requiring a hash stage. -/
private theorem fullChild0_mme_cell_boundary_profile_of_mass_support
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
    fullChild0_zero_profile _ (hm z) (fun s hs ↦ (hg z s hs).trans hz)
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
        rw [fullChild0_flipLabel_eq_rev]
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
        rw [hboundary.2.2 cell hz, ← fullChild0_flipLabel_eq_rev, hrevs]
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
        rw [fullChild0_flipLabel_eq_rev]
        exact hboundary.1 cell hz s
      · exact hzero



open MME.Released116 MME.MoreAsymmetryExactSeed

/-- The child profile has exactly one count for each physical occurrence of
its split or its complementary split. -/
private theorem fullChild0_mme_released_116_integer_profile_mass :
    ∀ (i : Fin 3) (c : Cell 4 6 parent),
      ∑ w, integerProfile i c w =
        splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2) := by
  decide +kernel

/-- Positive child counts have the grade required by the integer-step interface. -/
private theorem fullChild0_mme_released_116_integer_profile_support :
    ∀ (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2),
      0 < integerProfile i c w → ∑ h, (w h).val = (c.2.val i).val := by
  decide +kernel


private theorem fullChild0_scaled_boundary_profiles (k : ℕ) :
    BoundaryProfiles (fun i c w => k * integerProfile i c w) := by
  obtain ⟨h2, h0, h1⟩ := mme_released_116_integer_profile_boundary
  exact ⟨fun c hc w => congrArg (k * ·) (h2 c hc w),
    fun c hc w => congrArg (k * ·) (h0 c hc w),
    fun c hc w => congrArg (k * ·) (h1 c hc w)⟩

private theorem fullChild0_boundary_dim_pos {ell L : ℕ} (B : Boundary.Profile ell L) :
    0 < B.dim := by
  have hm : 0 < L.factorial / ∏ w, (B.count w).factorial := by
    simpa only [Nat.multinomial, B.total] using Nat.multinomial_pos Finset.univ B.count
  exact Nat.mul_pos hm (by positivity)

private theorem fullChild0_boundary_volume {ell L : ℕ} (B : Boundary.Profile ell L) (z : Fin 3) :
    B.a z * B.b z * B.c z = B.dim := by
  fin_cases z <;> simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]

/-- Every physical boundary cell has an exact matrix extraction at every
integer replication. Shape and histogram equalities are retained so the
result can be assembled with the interior cells. -/
private theorem fullChild0_mme_released_116_physical_boundary_matrix_extraction
    (k : ℕ) (c : Cell 4 6 parent) (z : Fin 3)
    (hz : (c.2.val z).val = 0) :
    ∃ B : Boundary.Profile 2
        (k * (splitCount c.1 c.2 +
          splitCount c.1 (complement (parent_total c.1) c.2))),
      0 < B.dim ∧ B.a z * B.b z * B.c z = B.dim ∧
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i w, k * integerProfile i c w = B.mu z i w) ∧
      ∀ (K : Type u) [Field K],
        TensorObj.Restrict (MMObj K (B.a z) (B.b z) (B.c z))
          (CWCells.unbroken K 5 2
            (k * (splitCount c.1 c.2 +
              splitCount c.1 (complement (parent_total c.1) c.2)))
            (Equiv.refl _) (fun _ => Unit.unit)
            (fun _ i => (c.2.val i).val)
            (fun i _ w => k * integerProfile i c w)) := by
  have hmass (i : Fin 3) : ∑ w, k * integerProfile i c w =
      k * (splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)) := by
    rw [← Finset.mul_sum, fullChild0_mme_released_116_integer_profile_mass]
  have hg (i : Fin 3) (w : CompleteWord 2) (hw : 0 < k * integerProfile i c w) :
      CWCells.grade w = (c.2.val i).val := by
    exact fullChild0_mme_released_116_integer_profile_support i c w (Nat.pos_of_mul_pos_left hw)
  obtain ⟨B, hshape, hmu⟩ := fullChild0_mme_cell_boundary_profile_of_mass_support c rfl
    (fun i c w => k * integerProfile i c w) hmass (fullChild0_scaled_boundary_profiles k) z hz hg
  refine ⟨B, fullChild0_boundary_dim_pos B, fullChild0_boundary_volume B z, hshape,
    fun i w => congrFun (hmu i) w, ?_⟩
  intro K _
  have h := mme_recursive_yz_boundary_actual_matrix_extraction (K := K) B z
  have hmu_point (i : Fin 3) (w : CompleteWord 2) :
      k * integerProfile i c w = B.mu z i w := congrFun (hmu i) w
  simpa only [Boundary.Profile.tensor, hshape, hmu_point] using h



open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false

private theorem fullChild0_scaled_boundary_log_lower {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) (k : ℕ) (hk : 0 < k)
    (C : Profile ell (L * k)) (hcount : ∀ s, C.count s = B.count s * k) :
    (k : ℝ) * ((L : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) +
      ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5) -
      (Fintype.card (CompleteWord ell) : ℝ) *
        Real.log (6 * ((L * k + 1 : ℕ) : ℝ)) ≤ Real.log (C.dim : ℝ) := by
  classical
  have hm : 0 < ∑ s, B.count s := by rw [B.total]; exact hL
  have h := mme_dwz_multinomial_entropy_polynomial_lower B.count k hk hm
  have hc : (fun s ↦ B.count s * k) = C.count := by funext s; exact (hcount s).symm
  rw [B.total, hc] at h
  have hmulti : (0 : ℝ) < Nat.multinomial Finset.univ C.count := by
    exact_mod_cast Nat.multinomial_pos Finset.univ C.count
  have hp : (0 : ℝ) < 6 * ((L * k + 1 : ℕ) : ℝ) := by positivity
  have hl := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp, Real.log_mul (ne_of_gt (pow_pos hp _)) (ne_of_gt hmulti),
    Real.log_pow] at hl
  have hone : ∑ s, C.count s * ones s = (∑ s, B.count s * ones s) * k := by
    simp only [hcount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hd : (C.dim : ℝ) =
      (Nat.multinomial Finset.univ C.count : ℝ) *
        (5 : ℝ) ^ (∑ s, C.count s * ones s) := by
    simp only [Profile.dim, Nat.multinomial, C.total, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [hd, Real.log_mul (ne_of_gt hmulti) (by positivity), Real.log_pow, hone]
  push_cast at hl ⊢
  nlinarith only [hl]

/-- Replication of a boundary histogram attains its entropy and CW-letter rate;
the threshold is uniform over all boundary profiles with that histogram. -/
private theorem fullChild0_mme_boundary_scaled_volume_rate {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ C : Profile ell (L * k),
      (∀ s, C.count s = B.count s * k) →
      (k : ℝ) * ((L : ℝ) * Real.log 2 *
          mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) +
        ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.dim : ℝ) := by
  classical
  let a : ℝ := Fintype.card (CompleteWord ell)
  have ha : 0 ≤ a := by positivity
  have habs := mme_log_sqrt_loss_eventually_le_linear a 0
    (a * Real.log (6 * ((L : ℝ) + 1))) delta hdelta
  filter_upwards [habs, eventually_gt_atTop 0] with k hk hkpos
  intro C hcount
  have hlog := fullChild0_scaled_boundary_log_lower B hL k hkpos C hcount
  have hpoly : (6 : ℝ) * ((L * k + 1 : ℕ) : ℝ) ≤
      (6 * ((L : ℝ) + 1)) * ((k : ℝ) + 1) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L,
      show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hlogs := Real.log_le_log (by positivity : (0 : ℝ) <
    6 * ((L * k + 1 : ℕ) : ℝ)) hpoly
  rw [Real.log_mul (show (6 * ((L : ℝ) + 1)) ≠ 0 by positivity)
    (show ((k : ℝ) + 1) ≠ 0 by positivity)] at hlogs
  have hscaled := mul_le_mul_of_nonneg_left hlogs ha
  change a * Real.log ((k : ℝ) + 1) + 0 * Real.sqrt ((k : ℝ) + 1) +
    a * Real.log (6 * ((L : ℝ) + 1)) ≤ (k : ℝ) * delta at hk
  change (k : ℝ) * _ - a * _ ≤ _ at hlog
  nlinarith only [hlog, hscaled, hk]


private theorem fullChild0_released_boundary_mass_pos (c : Cell 4 6 parent) :
    0 < splitCount c.1 c.2 +
      splitCount c.1 (complement (parent_total c.1) c.2) := by
  revert c
  decide +kernel

private theorem fullChild0_boundary_count_from_mu {ell L M : ℕ}
    (B : Boundary.Profile ell L) (C : Boundary.Profile ell M)
    (z : Fin 3) (k : ℕ) (h : ∀ i w, C.mu z i w = B.mu z i w * k) :
    ∀ w, C.count w = B.count w * k := by
  intro w
  fin_cases z
  · simpa [Boundary.Profile.mu] using h 1 w
  · simpa [Boundary.Profile.mu] using h 2 w
  · simpa [Boundary.Profile.mu] using h 0 w

/-- Each released boundary cell has physical matrix extractions attaining the
entropy and CW-letter rate of its exact integer histogram. -/
private theorem fullChild0_mme_released_116_boundary_physical_volume_rate
    (c : Cell 4 6 parent) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 2
        (splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)),
      (∀ i w, integerProfile i c w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ C : Boundary.Profile 2
          (k * (splitCount c.1 c.2 +
            splitCount c.1 (complement (parent_total c.1) c.2))),
        0 < C.dim ∧ C.a z * C.b z * C.c z = C.dim ∧
        (∀ i, (c.2.val i).val = C.shape z i) ∧
        (∀ i w, k * integerProfile i c w = C.mu z i w) ∧
        (k : ℝ) *
          (((splitCount c.1 c.2 +
              splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((splitCount c.1 c.2 +
                  splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.a z * C.b z * C.c z : ℕ) ∧
        ∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K (C.a z) (C.b z) (C.c z))
            (CWCells.unbroken K 5 2
              (k * (splitCount c.1 c.2 +
                splitCount c.1 (complement (parent_total c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => k * integerProfile i c w)) := by
  have hbase := fullChild0_mme_released_116_physical_boundary_matrix_extraction.{u} 1 c z hz
  rw [Nat.one_mul] at hbase
  simp only [Nat.one_mul] at hbase
  obtain ⟨B, _, _, _, hBmu, _⟩ := hbase
  refine ⟨B, hBmu, ?_⟩
  have hrate := fullChild0_mme_boundary_scaled_volume_rate B (fullChild0_released_boundary_mass_pos c)
    delta hdelta
  have hrate' : ∀ᶠ k : ℕ in atTop,
      ∀ C : Boundary.Profile 2 (k * (splitCount c.1 c.2 +
          splitCount c.1 (complement (parent_total c.1) c.2))),
        (∀ w, C.count w = B.count w * k) →
        (k : ℝ) *
          (((splitCount c.1 c.2 +
              splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((splitCount c.1 c.2 +
                  splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.dim : ℝ) := by
    filter_upwards [hrate] with k hk
    rw [Nat.mul_comm (splitCount c.1 c.2 +
      splitCount c.1 (complement (parent_total c.1) c.2)) k] at hk
    exact hk
  filter_upwards [hrate'] with k hk
  obtain ⟨C, hpos, hvol, hshape, hmu, hextract⟩ :=
    fullChild0_mme_released_116_physical_boundary_matrix_extraction k c z hz
  have hcount := fullChild0_boundary_count_from_mu B C z k (by
    intro i w
    rw [← hmu i w, ← hBmu i w, Nat.mul_comm])
  refine ⟨C, hpos, hvol, hshape, hmu, ?_, hextract⟩
  rw [hvol]
  exact hk C hcount



open MME
set_option autoImplicit false

/-- Full symmetrization turns a matrix tensor of volume V into a square
matrix tensor with each dimension V squared. -/
private theorem fullChild0_mme_MMObj_sixSymmetrization_iso {K : Type u} [Field K] (a b c : ℕ) :
    TensorObj.Isomorphic (sixSymmetrization (MMObj K a b c))
      (MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2) ((a * b * c) ^ 2)) := by
  let V := a * b * c
  have hcyc := TensorQ.toQ_eq_iff.mpr
    (mme_MMObj_cyclicSymmetrization_iso (K := K) a b c)
  have hswap := TensorQ.toQ_eq_iff.mpr
    (mme_MMObj_permObj_swapFirstTwo (K := K) V V V)
  apply TensorQ.toQ_eq_iff.mp
  rw [sixSymmetrization, TensorQ.toQ_kron, ← TensorQ.permAut_toQ,
    hcyc, TensorQ.permAut_toQ, hswap]
  have hmul := TensorQ.toQ_eq_iff.mpr (MMObj_kron_iso (K := K) V V V V V V)
  simpa only [TensorQ.toQ_kron, pow_two] using hmul

/-- A positive matrix extraction yields a six-symmetric extraction whose tau
weight retains six times its log-volume bound, for nonnegative tau. -/
private theorem fullChild0_mme_matrix_extraction_six_volume_weight
    {K : Type u} [Field K] {T : TensorObj K 3} (a b c : ℕ)
    (hrestrict : TensorObj.Restrict (MMObj K a b c) T)
    (hpos : 0 < a * b * c) (rate tau : ℝ) (htau : 0 ≤ tau)
    (hrate : rate ≤ Real.log (a * b * c : ℕ)) :
    TensorObj.Restrict
      (MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2) ((a * b * c) ^ 2))
      (sixSymmetrization T) ∧
    Real.exp (6 * tau * rate) ≤
      ((((a * b * c) ^ 2 * (a * b * c) ^ 2 * (a * b * c) ^ 2 : ℕ) : ℝ) ^ tau) := by
  constructor
  · exact (fullChild0_mme_MMObj_sixSymmetrization_iso (K := K) a b c).2.trans
      (mme_sixSymmetrization_restrict hrestrict)
  · have hv : (0 : ℝ) < (a * b * c : ℕ) := by exact_mod_cast hpos
    have hpow : (a * b * c) ^ 2 * (a * b * c) ^ 2 * (a * b * c) ^ 2 =
        (a * b * c) ^ 6 := by ring
    rw [hpow, Nat.cast_pow, Real.rpow_def_of_pos (pow_pos hv _), Real.log_pow]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hrate (show 0 ≤ 6 * tau by positivity)]


/-- The released boundary cells supply square matrices in the full
six-symmetric physical tensor, with their entropy and letter weight. -/
private theorem fullChild0_mme_released_116_boundary_six_weight_rate
    (c : Cell 4 6 parent) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 2
        (splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)),
      (∀ i w, integerProfile i c w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K M M M)
            (sixSymmetrization (CWCells.unbroken K 5 2
              (k * (splitCount c.1 c.2 +
                splitCount c.1 (complement (parent_total c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => k * integerProfile i c w)))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (6 * tau * ((k : ℝ) *
            (((splitCount c.1 c.2 +
                splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ (B.count w : ℝ) /
                  ((splitCount c.1 c.2 +
                    splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ)) +
              ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by
  obtain ⟨B, hmu, hrate⟩ :=
    fullChild0_mme_released_116_boundary_physical_volume_rate.{u} c z hz delta hdelta
  refine ⟨B, hmu, ?_⟩
  filter_upwards [hrate] with k hk
  obtain ⟨C, hpos, hvol, _, _, hlog, hextract⟩ := hk
  have hv : 0 < C.a z * C.b z * C.c z := by rw [hvol]; exact hpos
  refine ⟨(C.a z * C.b z * C.c z) ^ 2, pow_pos hv _, ?_, ?_⟩
  · intro K _
    exact (fullChild0_mme_MMObj_sixSymmetrization_iso (K := K) (C.a z) (C.b z) (C.c z)).2.trans
      (mme_sixSymmetrization_restrict (hextract K))
  · intro tau htau
    exact (fullChild0_mme_matrix_extraction_six_volume_weight (K := ULift.{u} ℚ)
      (C.a z) (C.b z) (C.c z) (hextract (ULift.{u} ℚ)) hv _ tau htau hlog).2



open MME BigOperators
set_option autoImplicit false

private theorem fullChild0_kron_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright

private theorem fullChild0_kronFin_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d) :
    ∀ (n : ℕ) (X Y : Fin n → TensorObj K d),
      (∀ i, TensorObj.Restrict (X i) (Y i)) →
      TensorObj.Restrict (TensorObj.kronFin n X) (TensorObj.kronFin n Y) := by
  intro n
  induction n with
  | zero =>
      intro X Y h
      exact TensorObj.Restrict.refl _
  | succ n ih =>
      intro X Y h
      change TensorObj.Restrict
        (TensorObj.kron (X 0)
          (TensorObj.kronFin n (fun i ↦ X i.succ)))
        (TensorObj.kron (Y 0)
          (TensorObj.kronFin n (fun i ↦ Y i.succ)))
      exact fullChild0_kron_restrict_for_tau_product hd (h 0)
        (ih (fun i ↦ X i.succ) (fun i ↦ Y i.succ) (fun i ↦ h i.succ))

/-- Six-symmetrization commutes with finite tensor products, up to actual
mutual restrictions. -/
private theorem fullChild0_mme_sixSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i => sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, sixSymmetrization,
    cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    ← TensorQ.permAut_toQ, map_prod, map_mul, Finset.prod_mul_distrib]


/-- Finite six-symmetric square-matrix extractions combine without a loss in
exponential weight. -/
private theorem fullChild0_mme_six_square_product_weight {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (M : Fin n → ℕ) (rate : Fin n → ℝ) (tau : ℝ)
    (hextract : ∀ i, TensorObj.Restrict (MMObj K (M i) (M i) (M i))
      (sixSymmetrization (T i)))
    (hweight : ∀ i, Real.exp (rate i) ≤ ((M i * M i * M i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict (MMObj K (∏ i, M i) (∏ i, M i) (∏ i, M i))
      (sixSymmetrization (TensorObj.kronFin n T)) ∧
    Real.exp (∑ i, rate i) ≤
      ((((∏ i, M i) * (∏ i, M i) * (∏ i, M i) : ℕ) : ℝ) ^ tau) := by
  constructor
  · exact (mme_kronFin_MMObj_iso (K := K) n M M M).2.trans
      ((fullChild0_kronFin_restrict_for_tau_product (by decide) n _ _ hextract).trans
        (fullChild0_mme_sixSymmetrization_kronFin_isomorphic T).1)
  · rw [Real.exp_sum]
    have hprod := Finset.prod_le_prod
      (fun i (_ : i ∈ Finset.univ) ↦ (Real.exp_pos (rate i)).le)
      (fun i (_ : i ∈ Finset.univ) ↦ hweight i)
    calc
      ∏ i, Real.exp (rate i) ≤ ∏ i, ((M i * M i * M i : ℕ) : ℝ) ^ tau := hprod
      _ = (∏ i, ((M i * M i * M i : ℕ) : ℝ)) ^ tau := by
        rw [Real.finset_prod_rpow]
        intro i _
        positivity
      _ = _ := by
        simp only [Nat.cast_mul, Nat.cast_prod, Finset.prod_mul_distrib]


/-- Any finite family of released boundary cells has a common replication
threshold and a single square-matrix extraction with the summed weight rate. -/
private theorem mme_released_116_boundary_product_weight_rate
    (n : ℕ) (c : Fin n → Cell 4 6 parent) (z : Fin n → Fin 3)
    (hz : ∀ r, ((c r).2.val (z r)).val = 0) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : ∀ r, Boundary.Profile 2
        (splitCount (c r).1 (c r).2 +
          splitCount (c r).1 (complement (parent_total (c r).1) (c r).2)),
      (∀ r i w, integerProfile i (c r) w = (B r).mu (z r) i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K M M M)
            (sixSymmetrization (TensorObj.kronFin n (fun r ↦ CWCells.unbroken K 5 2
              (k * (splitCount (c r).1 (c r).2 +
                splitCount (c r).1 (complement (parent_total (c r).1) (c r).2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => ((c r).2.val i).val)
              (fun i _ w => k * integerProfile i (c r) w))))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (∑ r, 6 * tau * ((k : ℝ) *
            (((splitCount (c r).1 (c r).2 +
                splitCount (c r).1 (complement (parent_total (c r).1) (c r).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((splitCount (c r).1 (c r).2 +
                    splitCount (c r).1 (complement (parent_total (c r).1) (c r).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by
  classical
  have h := fun r ↦ fullChild0_mme_released_116_boundary_six_weight_rate.{u}
    (c r) (z r) (hz r) delta hdelta
  choose B hmu hrate using h
  refine ⟨B, hmu, ?_⟩
  filter_upwards [Filter.eventually_all.2 hrate] with k hk
  choose M hpos hextract hweight using hk
  refine ⟨∏ r, M r, Finset.prod_pos (fun r _ ↦ hpos r), ?_, ?_⟩
  · intro K _
    exact (fullChild0_mme_six_square_product_weight (K := K) _ M _ 0
      (fun r ↦ hextract r K) (fun r ↦ hweight r 0 le_rfl)).1
  · intro tau htau
    exact (fullChild0_mme_six_square_product_weight (K := ULift.{u} ℚ) _ M _ tau
      (fun r ↦ hextract r (ULift.{u} ℚ)) (fun r ↦ hweight r tau htau)).2



open MME MME.CompleteSplit MME.RecursiveYZ MME.Released116
open MME.MoreAsymmetryExactSeed

set_option autoImplicit false

namespace MME.Released116

/-- The released mass of either outer atom in a 112 child. -/
def child112OuterCount (r : Fin 6) : ℕ :=
  ((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
    (0, [], 0)).2.2

/-- Exact marginal counts of the released 112 child, before cell scaling. -/
def child112Marginal (r : Fin 6) (i : Fin 3) (w : CompleteWord 2) : ℕ :=
  if i = 2 then
    if w = ![0, 2] ∨ w = ![2, 0] then child112OuterCount r
    else if w = ![1, 1] then denominator - 2 * child112OuterCount r else 0
  else
    if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0

/-- All six released parameters lie strictly inside the four-atom family. -/
private theorem fullChild1_mme_released_116_child112_parameter_bounds :
    ∀ r : Fin 6, 0 < child112OuterCount r ∧
      2 * child112OuterCount r < denominator := by
  decide +kernel

/-- The integer reconstruction has uniform X and Y marginals and the exact
three-word Z marginal determined by the released outer-atom count. -/
private theorem fullChild1_mme_released_116_child112_marginal_formula :
    ∀ (r : Fin 6) (c : Split),
      (c.val 0).val = 1 → (c.val 1).val = 1 → (c.val 2).val = 2 →
      ∀ (i : Fin 3) (w : CompleteWord 2),
        childMarginal r c i w = child112Marginal r i w := by
  have h :
      ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
        childMarginal r ⟨![1, 1, 2], by decide⟩ i w =
          child112Marginal r i w := by
    decide +kernel
  intro r c h0 h1 h2 i w
  have hc : c = ⟨![1, 1, 2], by decide⟩ := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  subst c
  exact h r i w

/-- Cell multiplicity scales the same exact 112 marginal in every mode. -/
private theorem fullChild1_mme_released_116_child112_integer_profile
    (c : Cell 4 6 parent)
    (h0 : (c.2.val 0).val = 1) (h1 : (c.2.val 1).val = 1)
    (h2 : (c.2.val 2).val = 2) (i : Fin 3) (w : CompleteWord 2) :
    integerProfile i c w =
      seed.region.getD c.1.val 0 *
        (splitWeight c.1 c.2 +
          splitWeight c.1 (complement (parent_total c.1) c.2)) *
        denominator * child112Marginal c.1 i w := by
  unfold integerProfile
  rw [fullChild1_mme_released_116_child112_marginal_formula c.1 c.2 h0 h1 h2]

/-- Reversing the two elementary factors preserves every released 112 marginal. -/
private theorem fullChild1_mme_released_116_child112_marginal_reverse :
    ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
      child112Marginal r i (fun j => w (Fin.rev j)) = child112Marginal r i w := by
  decide +kernel

/-- The reconstruction is normalized before the physical cell multiplier. -/
private theorem fullChild1_mme_released_116_child112_marginal_mass :
    ∀ (r : Fin 6) (i : Fin 3),
      ∑ w : CompleteWord 2, child112Marginal r i w = denominator := by
  decide +kernel

end MME.Released116


open MME.Released116 MME.CompleteSplit112 Filter

/-- The actual six parameters satisfy the balance condition required by the
uniform induced-family construction. -/
private theorem fullChild1_mme_released_116_child112_hash_balance :
    ∀ r : Fin 6, 341 * (2 * child112OuterCount r) <
      100 * (denominator - 2 * child112OuterCount r) := by
  decide +kernel

/-- The released marginal agrees with the parametric coupled-family profile
at its own exact rational parameter. -/
private theorem fullChild1_mme_released_116_child112_parametric_probability :
    ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
      (child112Marginal r i w : ℚ) / denominator =
        profileProbability ((child112OuterCount r : ℚ) / denominator) i w := by
  decide +kernel


/-- Each released region has actual induced families on its exact integer
subsequence, retaining the separate and joint directional capacities. -/
private theorem fullChild1_mme_released_116_child112_cofinal_induced_families (r : Fin 6) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N := denominator * m
        let L := (2 * child112OuterCount r) * m
        let G := (denominator - 2 * child112OuterCount r) * m
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) := by
  let D := denominator
  let l := 2 * child112OuterCount r
  let g := D - l
  have hl : 0 < l := by
    dsimp [l]
    exact Nat.mul_pos (by decide) (fullChild1_mme_released_116_child112_parameter_bounds r).1
  have hsum : l + g = D := by
    have hlt := (fullChild1_mme_released_116_child112_parameter_bounds r).2
    dsimp [l, g, D]
    omega
  have hbalance : 341 * l < 100 * g := fullChild1_mme_released_116_child112_hash_balance r
  obtain ⟨C, hC, hlarge⟩ := mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
    (fun n => l * (n / D)) (fun n => g * (n / D))
  refine ⟨C, hC, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlarge
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with m hm
  have hmpos : 0 < m := by omega
  have hNm : N₀ ≤ D * m := by dsimp [D, denominator]; omega
  have hdiv : D * m / D = m := by dsimp [D, denominator]; omega
  have hLpos : 0 < l * m := Nat.mul_pos hl hmpos
  have hLG : l * m + g * m = D * m := by rw [← Nat.add_mul, hsum]
  have hbal : 341 * (l * m) < 100 * (g * m) := by
    simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right hbalance hmpos
  have hextract := hN₀ (D * m) hNm
  dsimp only at hextract
  simp only [hdiv] at hextract
  obtain ⟨A, H, family, hH, hA, hmiddle⟩ := hextract ⟨hLpos, hLG, hbal⟩
  rw [hdiv] at family
  have hcapacity := mme_primary_hash_uniform_stars_joint_directional_capacity
    (D * m) (l * m) (g * m) A H hLG C hA hmiddle
  have hZpos :
      (0 : ℝ) < (Nat.choose (2 * (D * m)) (l * m) *
        Nat.choose (2 * (D * m) - l * m) (l * m) : ℕ) := by
    exact_mod_cast Nat.mul_pos
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m)))
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m) - l * m))
  have hApos : (0 : ℝ) < A :=
    lt_of_lt_of_le (mul_pos hZpos (Real.exp_pos _)) hA
  exact ⟨A, H, family, by exact_mod_cast hApos, hH, hA, hcapacity.2.2⟩



/-- A family with the released counts lies in the actual exact-profile
intact 112 tensor, with its full common matrix volume. -/
private theorem fullChild1_mme_released_116_child112_intact_family_certificate
    (r : Fin 6) (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily (denominator * m)
      ((2 * child112OuterCount r) * m)
      ((denominator - 2 * child112OuterCount r) * m) A H)
    (K : Type u) [Field K] :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (CWCells.unbroken K 5 2 (2 * (denominator * m)) (Equiv.refl _)
          (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
          (fun i _ w => 2 * m * child112Marginal r i w))
        A H (5 ^ (4 * ((denominator - 2 * child112OuterCount r) * m) +
          2 * ((2 * child112OuterCount r) * m)))) := by
  let beta (i : Fin 3) : Profile 2 := {
    level_pos := by decide
    probability w := (child112Marginal r i w : ℝ) / denominator
    nonnegative w := by positivity
    sum_eq_one := by
      rw [← Finset.sum_div, ← Nat.cast_sum, fullChild1_mme_released_116_child112_marginal_mass]
      norm_num [denominator] }
  have hbeta (i : Fin 3) (w : CompleteWord 2) :
      (beta i).probability w =
        (profileProbability ((child112OuterCount r : ℚ) / denominator) i w : ℝ) := by
    dsimp [beta]
    have h := congrArg (fun x : ℚ => (x : ℝ))
      (fullChild1_mme_released_116_child112_parametric_probability r i w)
    simpa only [Rat.cast_div, Rat.cast_natCast] using h
  have hLG :
      (2 * child112OuterCount r) * m +
        (denominator - 2 * child112OuterCount r) * m = denominator * m := by
    rw [← Nat.add_mul, Nat.add_sub_of_le
      (fullChild1_mme_released_116_child112_parameter_bounds r).2.le]
  have hLp :
      (((2 * child112OuterCount r) * m : ℕ) : ℚ) =
        ((2 * (denominator * m) : ℕ) : ℚ) *
          ((child112OuterCount r : ℚ) / denominator) := by
    push_cast
    norm_num [denominator]
    ring
  obtain ⟨certificate⟩ :=
    mme_complete_split_112_coupled_restricted_family_certificate
      (K := K) 5 ((child112OuterCount r : ℚ) / denominator)
      hLG hLp family beta hbeta 0
  have hmu (i : Fin 3) (w : CompleteWord 2) :
      ((2 * m * child112Marginal r i w : ℕ) : ℝ) =
        ((2 * (denominator * m) : ℕ) : ℝ) * (beta i).probability w := by
    dsimp [beta]
    push_cast
    norm_num [denominator]
    ring
  exact ⟨{
    star := certificate.star
    restrict := certificate.restrict.trans
      ((mme_complete_split_112_canonical_profile_router K 5 beta 0
        (2 * (denominator * m))).trans
        (mme_complete_split_112_canonical_power_restricts_from_intact K 5
          (2 * (denominator * m)) beta
          (fun i w => 2 * m * child112Marginal r i w) hmu))
    certificate := certificate.certificate
  }⟩


/-- Cofinal matrix extractions from the actual released exact 112 profiles.
The induced family supplies both directional capacities and the explicit
copy bound after cyclic symmetrization. -/
private theorem fullChild1_mme_released_116_child112_cofinal_matrix_extraction (r : Fin 6) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N := denominator * m
        let L := (2 * (((seed.children.find?
          (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
        let G := (denominator - 2 * (((seed.children.find?
          (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) ∧
          ∀ (K : Type u) [Field K], ∃ (k : ℕ) (a b c : Fin k → ℕ),
            0 < k ∧
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
              (cyclicSymmetrization
                (CWCells.unbroken K 5 2 (2 * N) (Equiv.refl _)
                  (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                  (fun i _ w => 2 * m * childMarginal r ⟨![1, 1, 2], by decide⟩ i w))) ∧
            (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
                Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) ≤
              (k : ℝ) ∧
            ∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3 := by
  obtain ⟨C, hC, hfamilies⟩ := fullChild1_mme_released_116_child112_cofinal_induced_families r
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfamilies] with m hm
  obtain ⟨A, H, family, hApos, hH, hA, hAH⟩ := hm
  refine ⟨A, H, family, hApos, hH, hA, hAH, ?_⟩
  intro K _
  obtain ⟨certificate⟩ := fullChild1_mme_released_116_child112_intact_family_certificate
    r m A H family K
  obtain ⟨k, a, b, c, hrestrict, hcount, hvolume⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction certificate family.hHpos
  have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
  have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
  have hpositive : 0 < (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) := by positivity
  have hk : 0 < k := by exact_mod_cast hpositive.trans_le hcount
  refine ⟨k, a, b, c, hk, ?_, hcount, hvolume⟩
  simpa only [fullChild1_mme_released_116_child112_marginal_formula r
    ⟨![1, 1, 2], by decide⟩ rfl rfl rfl] using hrestrict

/-- The released 112 extraction retains the entropy rate of the Z marginal
and both unshared directions, with the explicit final sublinear loss. -/
private theorem fullChild1_mme_released_116_child112_cofinal_matrix_log_rate
    (r : Fin 6) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      let N := denominator * m
      let L := (2 * (((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * (((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
      let p : ℝ := ((((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2) : ℝ) / denominator
      ∃ A H : ℕ, 0 < A ∧ 0 < H ∧ H ≤ 4 ^ N ∧
        ((2 * N : ℕ) : ℝ) *
            (Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] - delta) ≤
          Real.log (A : ℝ) ∧
        ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
          Real.log ((A : ℝ) * (H : ℝ)) ∧
        ∀ (K : Type u) [Field K], ∃ (k : ℕ) (a b c : Fin k → ℕ),
          0 < k ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (cyclicSymmetrization
              (CWCells.unbroken K 5 2 (2 * N) (Equiv.refl _)
                (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => 2 * m * childMarginal r ⟨![1, 1, 2], by decide⟩ i w))) ∧
          (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
          ((2 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) -
                3 * delta) -
              100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤ Real.log (k : ℝ) := by
  obtain ⟨C, _hC, hfamilies⟩ := fullChild1_mme_released_116_child112_cofinal_matrix_extraction r
  let l := 2 * child112OuterCount r
  let g := denominator - l
  have hsum : l + g = denominator := by
    exact Nat.add_sub_of_le (fullChild1_mme_released_116_child112_parameter_bounds r).2.le
  have hD : 0 < l + g := by rw [hsum]; decide
  have hp : (l : ℝ) / (2 * (denominator : ℝ)) =
      (child112OuterCount r : ℝ) / denominator := by
    dsimp [l]
    push_cast
    norm_num [denominator]
    ring
  have he := mme_complete_split_112_outer_star_entropy_rate l g hD C delta hdelta
  simp only [hsum, hp] at he
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_central_binomial_sqrt_loss_log_rate C delta hdelta)
  filter_upwards [hfamilies, he, eventually_ge_atTop n₀]
    with m hm hme hmn
  dsimp only at hm hme ⊢
  obtain ⟨A, H, family, hApos, hH, hA, hAH, hextract⟩ := hm
  have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
  have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
  have hNm : n₀ ≤ denominator * m := by dsimp [denominator]; omega
  have hlogAH := hn₀ (denominator * m) hNm
    ((A : ℝ) * (H : ℝ)) (mul_pos hAr hHr)
    (by simpa only [mul_assoc] using hAH)
  have hlogAH' : ((2 * (denominator * m) : ℕ) : ℝ) * (Real.log 2 - delta) ≤
      Real.log ((A : ℝ) * (H : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlogAH
  have hlogA := hme (A : ℝ) hAr hA
  refine ⟨A, H, hApos, family.hHpos, hH, hlogA, hlogAH', ?_⟩
  intro K _
  obtain ⟨k, a, b, c, hk, hrestrict, hcount, hvolume⟩ := hextract K
  refine ⟨k, a, b, c, hk, hrestrict, hvolume, ?_⟩
  have hpositive : 0 < (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) := by positivity
  have hlog := Real.log_le_log hpositive hcount
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp] at hlog
  rw [Real.log_mul hAr.ne' hHr.ne'] at hlogAH'
  norm_num only [Nat.cast_ofNat] at hlog
  dsimp only [child112OuterCount] at hlogA
  nlinarith only [hlog, hlogA, hlogAH']

namespace MME.Released116

private def fullChild1_child112Split : Split := ⟨![1, 1, 2], by decide⟩

/-- The physical cell multiplier after separating one factor of the
released denominator. Even replication makes the family scale integral. -/
private def fullChild1_child112PhysicalScale (r : Fin 6) : ℕ :=
  seed.region.getD r.val 0 *
    (splitWeight r fullChild1_child112Split +
      splitWeight r (complement (parent_total r) fullChild1_child112Split)) * denominator

private theorem fullChild1_child112_physical_scale_pos :
    ∀ r : Fin 6, 0 < fullChild1_child112PhysicalScale r := by
  decide +kernel

private theorem fullChild1_child112_physical_size (r : Fin 6) (k : ℕ) :
    2 * (denominator * (k * fullChild1_child112PhysicalScale r)) =
      (2 * k) * (splitCount r fullChild1_child112Split +
        splitCount r (complement (parent_total r) fullChild1_child112Split)) := by
  unfold fullChild1_child112PhysicalScale splitCount
  ring

private theorem fullChild1_child112_physical_histogram
    (r : Fin 6) (k : ℕ) (i : Fin 3) (w : CompleteWord 2) :
    2 * (k * fullChild1_child112PhysicalScale r) * childMarginal r fullChild1_child112Split i w =
      (2 * k) * integerProfile i ⟨r, fullChild1_child112Split⟩ w := by
  unfold fullChild1_child112PhysicalScale integerProfile
  ring

end MME.Released116


/-- At every sufficiently large even replication, all six regions admit
the checked 112 extraction on their physical integer profiles. The source
length is the sum of the complementary split multiplicities. -/
private theorem fullChild1_mme_released_116_child112_simultaneous_physical_extraction
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      let s := (seed.region.getD r.val 0 *
        (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
          splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
      let N := denominator * (k * s)
      let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2) : ℝ) / denominator
      ∃ A H : ℕ, 0 < A ∧ 0 < H ∧ H ≤ 4 ^ N ∧
        ((2 * N : ℕ) : ℝ) *
            (Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] - delta) ≤
          Real.log (A : ℝ) ∧
        ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
          Real.log ((A : ℝ) * (H : ℝ)) ∧
        ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (cyclicSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount r (⟨![1, 1, 2], by decide⟩ : Split) +
                  splitCount r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))))
                (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => (2 * k) * integerProfile i ⟨r, (⟨![1, 1, 2], by decide⟩ : Split)⟩ w))) ∧
          (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
          ((2 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) -
                3 * delta) -
              100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
            Real.log (copies : ℝ) := by
  apply Filter.eventually_all.mpr
  intro r
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    (fullChild1_mme_released_116_child112_cofinal_matrix_log_rate r delta hdelta)
  filter_upwards [eventually_ge_atTop m₀] with k hk
  have hscale := fullChild1_child112_physical_scale_pos r
  have hlarge : m₀ ≤ k * fullChild1_child112PhysicalScale r := by nlinarith
  have h := hm₀ (k * fullChild1_child112PhysicalScale r) hlarge
  dsimp only at h ⊢
  obtain ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, hextract⟩ := h
  refine ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, ?_⟩
  intro K _
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hrate⟩ := hextract K
  refine ⟨copies, a, b, c, hcopies, ?_, hvolume, hrate⟩
  have hsize := fullChild1_child112_physical_size r k
  have hhist := fullChild1_child112_physical_histogram r k
  dsimp only [fullChild1_child112Split] at hsize hhist
  rw [← hsize]
  simp only [← hhist]
  exact hrestrict


open BigOperators

/-- Swapping and multiplying a cyclic extraction squares its copy count
and common volume. Its logarithmic copy bound gives a six-symmetric weight
bound without requiring the individual matrices to be square. -/
private theorem fullChild1_mme_cyclic_constant_volume_extraction_six_weight
    {K : Type u} [Field K] {T : TensorObj K 3} {k V : ℕ}
    (a b c : Fin k → ℕ) (hk : 0 < k)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (cyclicSymmetrization T))
    (hvolume : ∀ j, a j * b j * c j = V)
    (L tau : ℝ) (hlog : L ≤ Real.log (k : ℝ)) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ),
      0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization T) ∧
      (∀ j, a' j * b' j * c' j = V ^ 2) ∧
      Real.exp (2 * L) * (((V ^ 2 : ℕ) : ℝ) ^ tau) ≤
        ∑ j, (((a' j * b' j * c' j : ℕ) : ℝ) ^ tau) := by
  let a' := fun r : Fin (k * k) => a (finProdFinEquiv.symm r).1 * c (finProdFinEquiv.symm r).2
  let b' := fun r : Fin (k * k) => b (finProdFinEquiv.symm r).1 * b (finProdFinEquiv.symm r).2
  let c' := fun r : Fin (k * k) => c (finProdFinEquiv.symm r).1 * a (finProdFinEquiv.symm r).2
  have hvol (j : Fin (k * k)) : a' j * b' j * c' j = V ^ 2 := by
    dsimp only [a', b', c']
    calc
      _ = (a (finProdFinEquiv.symm j).1 * b (finProdFinEquiv.symm j).1 *
          c (finProdFinEquiv.symm j).1) *
        (a (finProdFinEquiv.symm j).2 * b (finProdFinEquiv.symm j).2 *
          c (finProdFinEquiv.symm j).2) := by ring
      _ = V ^ 2 := by rw [hvolume, hvolume]; ring
  refine ⟨k * k, a', b', c', Nat.mul_pos hk hk,
    mme_finite_MM_extraction_swap_double a b c hrestrict, hvol, ?_⟩
  simp_rw [hvol]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    Real.exp (2 * L) ≤ Real.exp (2 * Real.log (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = ((k * k : ℕ) : ℝ) := by rw [two_mul, Real.exp_add, Real.exp_log hkr]; norm_cast


private theorem fullChild1_behrend_log_loss_bound (N H : ℕ) (hH : H ≤ 4 ^ N) :
    100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      200 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
  have hp : H + 1 ≤ 4 ^ (N + 1) := by
    have hpos : 0 < 4 ^ N := by positivity
    rw [pow_succ]
    omega
  have hlog : Real.log ((H + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
      (show ((H + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) by exact_mod_cast hp)
    rw [Real.log_pow] at h
    have hfour : Real.log (4 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log 4 := h
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := mul_comm _ _
  have hl0 : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hs : Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hl0,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity),
      Real.sqrt_nonneg (Real.log ((H + 1 : ℕ) : ℝ)),
      Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  linarith


/-- The final square-root loss can be absorbed in any positive entropy
budget, uniformly across the six physical regions. -/
private theorem fullChild1_child112_physical_clean_log_rate (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      let N := denominator * (k * fullChild1_child112PhysicalScale r)
      let L := (2 * child112OuterCount r) * (k * fullChild1_child112PhysicalScale r)
      let G := (denominator - 2 * child112OuterCount r) * (k * fullChild1_child112PhysicalScale r)
      let p : ℝ := (child112OuterCount r : ℝ) / denominator
      ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
        0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
          (cyclicSymmetrization
            (CWCells.unbroken K 5 2
              ((2 * k) * (splitCount r fullChild1_child112Split +
                splitCount r (complement (parent_total r) fullChild1_child112Split)))
              (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
              (fun i _ w => (2 * k) * integerProfile i ⟨r, fullChild1_child112Split⟩ w))) ∧
        (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
        ((2 * N : ℕ) : ℝ) *
          (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) ≤
          Real.log (copies : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_log_sqrt_loss_eventually_le_linear 0 200 0 delta hdelta)
  filter_upwards [fullChild1_mme_released_116_child112_simultaneous_physical_extraction
    (delta / 6) (by positivity), eventually_ge_atTop n₀] with k hk hkn
  intro r
  have hs := fullChild1_child112_physical_scale_pos r
  have hd : 0 < denominator := by decide
  have hlarge : n₀ ≤ denominator * (k * fullChild1_child112PhysicalScale r) := by
    calc
      n₀ ≤ k := hkn
      _ ≤ k * fullChild1_child112PhysicalScale r := by nlinarith
      _ ≤ denominator * (k * fullChild1_child112PhysicalScale r) := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right (k * fullChild1_child112PhysicalScale r) (show 1 ≤ denominator from hd)
  have hbudget := hn₀ _ hlarge
  have h := hk r
  dsimp only at h ⊢
  obtain ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, hextract⟩ := h
  intro K _
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hrate⟩ := hextract K
  refine ⟨copies, a, b, c, hcopies, hrestrict, hvolume, ?_⟩
  change H ≤ 4 ^ (denominator * (k * fullChild1_child112PhysicalScale r)) at hHbound
  have hloss := fullChild1_behrend_log_loss_bound _ H hHbound
  change ((2 * (denominator * (k * fullChild1_child112PhysicalScale r)) : ℕ) : ℝ) *
    (Real.log 2 * (mme_modern_entropyBits
      ![(child112OuterCount r : ℝ) / denominator,
        (child112OuterCount r : ℝ) / denominator,
        1 - 2 * ((child112OuterCount r : ℝ) / denominator)] + 2) - 3 * (delta / 6)) -
      100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤ Real.log (copies : ℝ) at hrate
  change H ≤ 4 ^ (denominator * (k * fullChild1_child112PhysicalScale r)) at hHbound
  simp only [zero_mul, zero_add, add_zero] at hbudget
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hloss hbudget hrate ⊢
  nlinarith only [hrate, hloss, hbudget]


/-- All six released physical 112 cells attain their entropy and volume
rate after six-symmetrization, with any positive finite rate allowance. -/
private theorem fullChild1_mme_released_116_child112_simultaneous_six_weight_rate
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      let s := (seed.region.getD r.val 0 *
        (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
          splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
      let N := denominator * (k * s)
      let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let D := 4 * G + 2 * L
      let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2) : ℝ) / denominator
      ∀ (K : Type u) [Field K] (tau : ℝ),
        ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (sixSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount r (⟨![1, 1, 2], by decide⟩ : Split) +
                  splitCount r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))))
                (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => (2 * k) * integerProfile i ⟨r, (⟨![1, 1, 2], by decide⟩ : Split)⟩ w))) ∧
          (∀ j, a j * b j * c j = 5 ^ (6 * D)) ∧
          Real.exp (((4 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
            ((6 * D : ℕ) : ℝ) * tau * Real.log 5) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [fullChild1_child112_physical_clean_log_rate delta hdelta] with k hk
  intro r
  dsimp only
  intro K _ tau
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hlog⟩ := hk r K
  obtain ⟨count, a', b', c', hcount, hrestrict', hvolume', hweight⟩ :=
    fullChild1_mme_cyclic_constant_volume_extraction_six_weight a b c hcopies
      hrestrict hvolume _ tau hlog
  dsimp only [fullChild1_child112PhysicalScale, child112OuterCount, fullChild1_child112Split] at hvolume' hweight
  refine ⟨count, a', b', c', hcount, hrestrict', ?_, ?_⟩
  · intro j
    rw [hvolume', ← pow_mul, ← pow_mul]
    congr 1
    ring
  · have hweight_eq (D : ℕ) :
        (((((5 ^ D) ^ 3) ^ 2 : ℕ) : ℝ) ^ tau) =
          Real.exp (((6 * D : ℕ) : ℝ) * tau * Real.log 5) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      push_cast
      simp only [Real.log_pow]
      congr 1
      ring
    rw [hweight_eq, ← Real.exp_add] at hweight
    convert hweight using 1
    congr 1
    push_cast
    ring


/-- Six-symmetrization commutes with finite tensor products, up to actual
mutual restrictions. -/
private theorem fullChild1_mme_sixSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i => sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, sixSymmetrization,
    cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    ← TensorQ.permAut_toQ, map_prod, map_mul, Finset.prod_mul_distrib]


private theorem fullChild1_six_product_exponential_extraction
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3)
    (tau : ℝ) (rate : Fin n → ℝ)
    (hextract : ∀ i, ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (T i)) ∧
      Real.exp (rate i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ), 0 < q ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (TensorObj.kronFin n T)) ∧
      Real.exp (∑ i, rate i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨q, a, b, c, hrestrict, hweight⟩ :=
    mme_finite_MM_extractions_kronFin_tau_product
      (fun i => sixSymmetrization (T i)) tau (fun i => Real.exp (rate i))
      (fun i => (Real.exp_pos _).le) hextract
  have hweight' : Real.exp (∑ i, rate i) ≤
      ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    simpa only [Real.exp_sum] using hweight
  have hq : 0 < q := by
    by_contra h
    have hz : q = 0 := by omega
    subst q
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hweight'
    exact (Real.exp_pos _).not_ge hweight'
  exact ⟨q, a, b, c, hq,
    hrestrict.trans (fullChild1_mme_sixSymmetrization_kronFin_isomorphic T).1, hweight'⟩


/-- The six physical 112 regional cells can be extracted simultaneously
from their product, with the sum of their certified logarithmic rates. -/
private theorem mme_released_116_child112_joint_product_weight_rate
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (K : Type u) [Field K] (tau : ℝ),
      ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
          (sixSymmetrization (TensorObj.kronFin 6 (fun r =>
            CWCells.unbroken K 5 2
              ((2 * k) * (splitCount r (⟨![1, 1, 2], by decide⟩ : Split) +
                splitCount r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))))
              (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
              (fun i _ w => (2 * k) * integerProfile i ⟨r, (⟨![1, 1, 2], by decide⟩ : Split)⟩ w)))) ∧
        Real.exp (∑ r : Fin 6,
          let s := (seed.region.getD r.val 0 *
            (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
              splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
          let N := denominator * (k * s)
          let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2)) * (k * s)
          let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2)) * (k * s)
          let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2) : ℝ) / denominator
          ((4 * N : ℕ) : ℝ) *
            (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
          ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [fullChild1_mme_released_116_child112_simultaneous_six_weight_rate delta hdelta]
    with k hk
  intro K _ tau
  apply fullChild1_six_product_exponential_extraction
  intro r
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hweight⟩ := hk r K tau
  exact ⟨copies, a, b, c, hrestrict, hweight⟩



open MME MME.RecursiveYZ MME.Released116
set_option autoImplicit false

private def fullChild2_boundarySplit (i : Fin 3) : Split :=
  if i = 0 then ⟨![0, 0, 4], by decide⟩
  else if i = 1 then ⟨![0, 1, 3], by decide⟩
  else ⟨![1, 0, 3], by decide⟩

private def fullChild2_partitionCell : Fin 18 ⊕ Fin 6 → Cell 4 6 parent
  | .inl i => ⟨(finProdFinEquiv.symm i : Fin 6 × Fin 3).1,
      fullChild2_boundarySplit (finProdFinEquiv.symm i : Fin 6 × Fin 3).2⟩
  | .inr r => ⟨r, ⟨![1, 1, 2], by change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i; decide⟩⟩

private theorem fullChild2_cell_eq_iff (x y : Cell 4 6 parent) :
    x = y ↔ x.1 = y.1 ∧ ∀ i, (x.2.val i).val = (y.2.val i).val := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ ↦ rfl⟩
  · rcases x with ⟨r, x⟩
    rcases y with ⟨s, y⟩
    rintro ⟨hrs, hval⟩
    dsimp only at hrs hval
    subst s
    congr 1
    apply Subtype.ext
    funext i
    exact Fin.ext (hval i)

private theorem fullChild2_partitionCell_bijective : Function.Bijective fullChild2_partitionCell := by
  unfold Function.Bijective Function.Injective Function.Surjective
  simp only [fullChild2_cell_eq_iff]
  decide +kernel

/-- The full released child index consists of eighteen boundary cells and
six interior 112 cells. The equivalence retains each physical cell once. -/
private theorem fullChild2_mme_released_116_child_partition :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i; decide⟩⟩) := by
  refine ⟨Equiv.ofBijective fullChild2_partitionCell fullChild2_partitionCell_bijective, ?_, ?_⟩
  · change ∀ i : Fin 18, ∃ z : Fin 3, ((fullChild2_partitionCell (.inl i)).2.val z).val = 0
    decide +kernel
  · intro r
    rfl



open MME BigOperators
set_option autoImplicit false

/-- A partition of the finite factor index gives an actual tensor
isomorphism to the Kronecker product of the two indexed subproducts. -/
private theorem fullChild2_mme_kronFin_partition_isomorphic {K : Type u} [Field K] {a b : ℕ}
    (e : (Fin a ⊕ Fin b) ≃ Fin (a + b)) (T : Fin (a + b) → TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.kronFin (a + b) T)
      (TensorObj.kron
        (TensorObj.kronFin a (fun i ↦ T (e (.inl i))))
        (TensorObj.kronFin b (fun i ↦ T (e (.inr i))))) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [TensorQ.toQ_kron, mme_toQ_kronFin]
  rw [← Equiv.prod_comp e (fun i ↦ TensorQ.toQ (T i)), Fintype.prod_sum_type]


/-- The released full child tensor splits into its eighteen boundary factors
and six canonical 112 factors, independently of the original enumeration. -/
private theorem fullChild2_mme_released_116_child_tensor_partition :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
        (T : Cell 4 6 parent → TensorObj K 3),
        TensorObj.Isomorphic (TensorObj.kronFin 24 (fun i ↦ T (d i)))
          (TensorObj.kron
            (TensorObj.kronFin 18 (fun i ↦ T (e (.inl i))))
            (TensorObj.kronFin 6 (fun r ↦ T ⟨r, ⟨![1, 1, 2], by
              change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
              decide⟩⟩))) := by
  obtain ⟨e, hb, hi⟩ := fullChild2_mme_released_116_child_partition
  refine ⟨e, hb, hi, ?_⟩
  intro d K _ T
  have h := fullChild2_mme_kronFin_partition_isomorphic (K := K) (e.trans d.symm)
    (fun i ↦ T (d i))
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply, hi] using h


open MME BigOperators
set_option autoImplicit false

private theorem fullChild2_kron_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright


private theorem fullChild2_six_kron_iso {K : Type u} [Field K] (X Y : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kron (sixSymmetrization X) (sixSymmetrization Y))
      (sixSymmetrization (TensorObj.kron X Y)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, ← TensorQ.permAut_toQ, map_mul]
  ring

/-- A square boundary extraction multiplies every interior matrix dimension
without changing the number of summands or losing exponential weight. -/
private theorem fullChild2_mme_six_square_family_product_weight
    {K : Type u} [Field K] {X Y : TensorObj K 3} {q : ℕ}
    (M : ℕ) (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ)
    (hboundary : TensorObj.Restrict (MMObj K M M M) (sixSymmetrization X))
    (hinterior : TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))) (sixSymmetrization Y))
    (hboundaryWeight : Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau)
    (hinteriorWeight : Real.exp interiorRate ≤
      ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (sixSymmetrization (TensorObj.kron X Y)) ∧
    Real.exp (boundaryRate + interiorRate) ≤
      ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by
  have hdist : TensorObj.Isomorphic
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (TensorObj.kron (MMObj K M M M)
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))) := by
    rw [← TensorQ.toQ_eq_iff, TensorQ.toQ_kron, TensorQ.toQ_bigAdd,
      TensorQ.toQ_bigAdd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (TensorQ.toQ_eq_iff.mpr (MMObj_kron_iso (K := K)
      M M M (a i) (b i) (c i))).symm.trans (TensorQ.toQ_kron _ _)
  constructor
  · exact hdist.1.trans ((fullChild2_kron_restrict_for_tau_product (by decide)
      hboundary hinterior).trans (fullChild2_six_kron_iso X Y).1)
  · rw [Real.exp_add]
    have hmul := mul_le_mul hboundaryWeight hinteriorWeight
      (Real.exp_pos interiorRate).le (Real.rpow_nonneg (by positivity) tau)
    calc
      Real.exp boundaryRate * Real.exp interiorRate ≤
          ((M * M * M : ℕ) : ℝ) ^ tau *
            ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau := hmul
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        push_cast
        ring


/-- Boundary and interior extraction weights combine on the full released
child tensor, preserving the interior summands and every physical child factor. -/
private theorem mme_released_116_full_child_weight_assembly :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
        (T : Cell 4 6 parent → TensorObj K 3) (q M : ℕ)
        (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ),
        TensorObj.Restrict (MMObj K M M M)
          (sixSymmetrization (TensorObj.kronFin 18 (fun i ↦ T (e (.inl i))))) →
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          (sixSymmetrization (TensorObj.kronFin 6 (fun r ↦ T ⟨r, ⟨![1, 1, 2], by
            change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
            decide⟩⟩))) →
        Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau →
        Real.exp interiorRate ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau →
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
          (sixSymmetrization (TensorObj.kronFin 24 (fun i ↦ T (d i)))) ∧
        Real.exp (boundaryRate + interiorRate) ≤
          ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by
  obtain ⟨e, hb, hi, hpartition⟩ := fullChild2_mme_released_116_child_tensor_partition.{u}
  refine ⟨e, hb, hi, ?_⟩
  intro d K _ T q M a b c tau boundaryRate interiorRate hboundary hinterior hwB hwI
  obtain ⟨hextract, hweight⟩ := fullChild2_mme_six_square_family_product_weight
    M a b c tau boundaryRate interiorRate hboundary hinterior hwB hwI
  exact ⟨hextract.trans (mme_sixSymmetrization_restrict (hpartition d K T).2), hweight⟩



/-- The full released child tensor has cofinal, positive-copy matrix
extractions attaining the sum of the boundary and interior entropy rates. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    let mass (c : Cell 4 6 parent) :=
      splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)
    ∃ (e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent) (z : Fin 18 → Fin 3)
      (B : ∀ r : Fin 18, Boundary.Profile 2 (mass (e (.inl r)))),
      (∀ r, ((e (.inl r)).2.val (z r)).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      (∀ r i w, integerProfile i (e (.inl r)) w = (B r).mu (z r) i w) ∧
      ∀ᶠ k : ℕ in atTop,
        ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
          (tau : ℝ), 0 ≤ tau →
        ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
            (sixSymmetrization (TensorObj.kronFin 24 (fun j ↦
              CWCells.unbroken K 5 2 ((2 * k) * mass (d j))
                (Equiv.refl _) (fun _ => Unit.unit)
                (fun _ i => ((d j).2.val i).val)
                (fun i _ w => (2 * k) * integerProfile i (d j) w)))) ∧
          Real.exp ((∑ r : Fin 18, 6 * tau * (((2 * k : ℕ) : ℝ) *
            ((mass (e (.inl r)) : ℝ) * Real.log 2 * mme_modern_entropyBits
              (fun w ↦ ((B r).count w : ℝ) / (mass (e (.inl r)) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) +
            (∑ r : Fin 6,
          let s := (seed.region.getD r.val 0 *
            (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
              splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
          let N := denominator * (k * s)
          let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2)) * (k * s)
          let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2)) * (k * s)
          let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2) : ℝ) / denominator
          ((4 * N : ℕ) : ℝ) *
            (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
          ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5)) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  classical
  dsimp only
  obtain ⟨e, hb, hi, hassembly⟩ := mme_released_116_full_child_weight_assembly.{u}
  choose z hz using hb
  obtain ⟨B, hmu, hboundary⟩ := mme_released_116_boundary_product_weight_rate.{u}
    18 (fun r ↦ e (.inl r)) z hz delta hdelta
  refine ⟨e, z, B, hz, hi, hmu, ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hboundary
  filter_upwards [eventually_ge_atTop n₀,
    mme_released_116_child112_joint_product_weight_rate.{u} delta hdelta]
    with k hkn hinterior
  obtain ⟨M, hM, hrestrictB, hweightB⟩ := hn₀ (2 * k) (by omega)
  intro d K _ tau htau
  obtain ⟨copies, a, b, c, hcopies, hrestrictI, hweightI⟩ := hinterior K tau
  have hshape (i : Fin 3) : ((![1, 1, 2] : Fin 3 → Fin 5) i).val =
      (![1, 1, 2] : Fin 3 → ℕ) i := by
    fin_cases i <;> rfl
  refine ⟨copies, (fun j ↦ M * a j), (fun j ↦ M * b j),
    (fun j ↦ M * c j), hcopies, ?_⟩
  exact hassembly d K
    (fun cell ↦ CWCells.unbroken K 5 2
      ((2 * k) * (splitCount cell.1 cell.2 +
        splitCount cell.1 (complement (parent_total cell.1) cell.2)))
      (Equiv.refl _) (fun _ => Unit.unit) (fun _ i => (cell.2.val i).val)
      (fun i _ w => (2 * k) * integerProfile i cell w))
    copies M a b c tau _ _ (hrestrictB K) (by simpa only [hshape] using hrestrictI)
    (hweightB tau htau) hweightI


#print axioms solution
