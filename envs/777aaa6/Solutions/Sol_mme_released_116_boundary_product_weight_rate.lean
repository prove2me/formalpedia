-- Prove2me | solution 1 for mme_released_116_boundary_product_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:26:48.752394+00:00
-- url     : https://prove2.me/submissions/5095ac7e-933b-4b34-b0d9-a35fdbc75ece

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
universe u

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
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



open MME.Released116 MME.MoreAsymmetryExactSeed

/-- The child profile has exactly one count for each physical occurrence of
its split or its complementary split. -/
private theorem mme_released_116_integer_profile_mass :
    ∀ (i : Fin 3) (c : Cell 4 6 parent),
      ∑ w, integerProfile i c w =
        splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2) := by
  decide +kernel

/-- Positive child counts have the grade required by the integer-step interface. -/
private theorem mme_released_116_integer_profile_support :
    ∀ (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2),
      0 < integerProfile i c w → ∑ h, (w h).val = (c.2.val i).val := by
  decide +kernel


private theorem scaled_boundary_profiles (k : ℕ) :
    BoundaryProfiles (fun i c w => k * integerProfile i c w) := by
  obtain ⟨h2, h0, h1⟩ := mme_released_116_integer_profile_boundary
  exact ⟨fun c hc w => congrArg (k * ·) (h2 c hc w),
    fun c hc w => congrArg (k * ·) (h0 c hc w),
    fun c hc w => congrArg (k * ·) (h1 c hc w)⟩

private theorem boundary_dim_pos {ell L : ℕ} (B : Boundary.Profile ell L) :
    0 < B.dim := by
  have hm : 0 < L.factorial / ∏ w, (B.count w).factorial := by
    simpa only [Nat.multinomial, B.total] using Nat.multinomial_pos Finset.univ B.count
  exact Nat.mul_pos hm (by positivity)

private theorem boundary_volume {ell L : ℕ} (B : Boundary.Profile ell L) (z : Fin 3) :
    B.a z * B.b z * B.c z = B.dim := by
  fin_cases z <;> simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]

/-- Every physical boundary cell has an exact matrix extraction at every
integer replication. Shape and histogram equalities are retained so the
result can be assembled with the interior cells. -/
private theorem mme_released_116_physical_boundary_matrix_extraction
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
    rw [← Finset.mul_sum, mme_released_116_integer_profile_mass]
  have hg (i : Fin 3) (w : CompleteWord 2) (hw : 0 < k * integerProfile i c w) :
      CWCells.grade w = (c.2.val i).val := by
    exact mme_released_116_integer_profile_support i c w (Nat.pos_of_mul_pos_left hw)
  obtain ⟨B, hshape, hmu⟩ := mme_cell_boundary_profile_of_mass_support c rfl
    (fun i c w => k * integerProfile i c w) hmass (scaled_boundary_profiles k) z hz hg
  refine ⟨B, boundary_dim_pos B, boundary_volume B z, hshape,
    fun i w => congrFun (hmu i) w, ?_⟩
  intro K _
  have h := mme_recursive_yz_boundary_actual_matrix_extraction (K := K) B z
  have hmu_point (i : Fin 3) (w : CompleteWord 2) :
      k * integerProfile i c w = B.mu z i w := congrFun (hmu i) w
  simpa only [Boundary.Profile.tensor, hshape, hmu_point] using h



open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false

private theorem scaled_boundary_log_lower {ell L : ℕ}
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
private theorem mme_boundary_scaled_volume_rate {ell L : ℕ}
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
  have hlog := scaled_boundary_log_lower B hL k hkpos C hcount
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


private theorem released_boundary_mass_pos (c : Cell 4 6 parent) :
    0 < splitCount c.1 c.2 +
      splitCount c.1 (complement (parent_total c.1) c.2) := by
  revert c
  decide +kernel

private theorem boundary_count_from_mu {ell L M : ℕ}
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
private theorem mme_released_116_boundary_physical_volume_rate
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
  have hbase := mme_released_116_physical_boundary_matrix_extraction.{u} 1 c z hz
  rw [Nat.one_mul] at hbase
  simp only [Nat.one_mul] at hbase
  obtain ⟨B, _, _, _, hBmu, _⟩ := hbase
  refine ⟨B, hBmu, ?_⟩
  have hrate := mme_boundary_scaled_volume_rate B (released_boundary_mass_pos c)
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
    mme_released_116_physical_boundary_matrix_extraction k c z hz
  have hcount := boundary_count_from_mu B C z k (by
    intro i w
    rw [← hmu i w, ← hBmu i w, Nat.mul_comm])
  refine ⟨C, hpos, hvol, hshape, hmu, ?_, hextract⟩
  rw [hvol]
  exact hk C hcount



open MME
set_option autoImplicit false

/-- Full symmetrization turns a matrix tensor of volume V into a square
matrix tensor with each dimension V squared. -/
private theorem mme_MMObj_sixSymmetrization_iso {K : Type u} [Field K] (a b c : ℕ) :
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
private theorem mme_matrix_extraction_six_volume_weight
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
  · exact (mme_MMObj_sixSymmetrization_iso (K := K) a b c).2.trans
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
private theorem mme_released_116_boundary_six_weight_rate
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
    mme_released_116_boundary_physical_volume_rate.{u} c z hz delta hdelta
  refine ⟨B, hmu, ?_⟩
  filter_upwards [hrate] with k hk
  obtain ⟨C, hpos, hvol, _, _, hlog, hextract⟩ := hk
  have hv : 0 < C.a z * C.b z * C.c z := by rw [hvol]; exact hpos
  refine ⟨(C.a z * C.b z * C.c z) ^ 2, pow_pos hv _, ?_, ?_⟩
  · intro K _
    exact (mme_MMObj_sixSymmetrization_iso (K := K) (C.a z) (C.b z) (C.c z)).2.trans
      (mme_sixSymmetrization_restrict (hextract K))
  · intro tau htau
    exact (mme_matrix_extraction_six_volume_weight (K := ULift.{u} ℚ)
      (C.a z) (C.b z) (C.c z) (hextract (ULift.{u} ℚ)) hv _ tau htau hlog).2



open MME BigOperators
set_option autoImplicit false

private theorem kron_restrict_for_tau_product
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

private theorem kronFin_restrict_for_tau_product
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
      exact kron_restrict_for_tau_product hd (h 0)
        (ih (fun i ↦ X i.succ) (fun i ↦ Y i.succ) (fun i ↦ h i.succ))

/-- Six-symmetrization commutes with finite tensor products, up to actual
mutual restrictions. -/
private theorem mme_sixSymmetrization_kronFin_isomorphic
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
private theorem mme_six_square_product_weight {K : Type u} [Field K] {n : ℕ}
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
      ((kronFin_restrict_for_tau_product (by decide) n _ _ hextract).trans
        (mme_sixSymmetrization_kronFin_isomorphic T).1)
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
theorem solution
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
  have h := fun r ↦ mme_released_116_boundary_six_weight_rate.{u}
    (c r) (z r) (hz r) delta hdelta
  choose B hmu hrate using h
  refine ⟨B, hmu, ?_⟩
  filter_upwards [Filter.eventually_all.2 hrate] with k hk
  choose M hpos hextract hweight using hk
  refine ⟨∏ r, M r, Finset.prod_pos (fun r _ ↦ hpos r), ?_, ?_⟩
  · intro K _
    exact (mme_six_square_product_weight (K := K) _ M _ 0
      (fun r ↦ hextract r K) (fun r ↦ hweight r 0 le_rfl)).1
  · intro tau htau
    exact (mme_six_square_product_weight (K := ULift.{u} ℚ) _ M _ tau
      (fun r ↦ hextract r (ULift.{u} ℚ)) (fun r ↦ hweight r tau htau)).2


#print axioms solution
