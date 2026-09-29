-- Prove2me | solution 1 for mme_dwz_positive_134_scaled_profiled_tensor_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-20T20:49:52.761124+00:00
-- url     : https://prove2.me/submissions/7d46245d-2abf-4fd9-8477-e334414246b9

import Definitions.Def_mme_dwz_positive_134_scaled_extraction_data
import Theorems.Thm_mme_dwz_positive_134_integer_fine_profile_validity
import Theorems.Thm_mme_dwz_positive_134_scaled_regional_entropy_floor
import Theorems.Thm_mme_recursive_region_target_nonempty
import Theorems.Thm_mme_recursive_thin_split_marginal_joint_counts
import Theorems.Thm_mme_integer_regional_graded_source_cofinal_extraction
import Theorems.Thm_mme_regional_mass_entropy_algebra

open BigOperators MME MME.RegionRate MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ
open MME.DWZ134Scaled
open scoped Classical
universe u
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

private theorem counts_sum (k : ℕ) (r : Fin 6) : (∑ c, m k r c) = n k r := by
  simp only [m, n, ← Finset.mul_sum, mme_dwz_positive_134_integer_fine_profile_validity.1]

private theorem n_sum (k : ℕ) : (∑ r, n k r) = k ^ 2 * DWZ134Fine.totalCount := by
  simp only [n, ← Finset.mul_sum, mme_dwz_positive_134_integer_fine_profile_validity.2.2.2.2.2.2.2]

private theorem lengths (k : ℕ) : length k = (4 * DWZ134Fine.totalCount) * k ^ 2 := by
  simp only [length, blocks, Position, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    ← Finset.sum_mul, n_sum]
  ring

private theorem split_flatten (k : ℕ) (f : Position (n k) → CompleteSplit.CompleteWord 2) :
    ProfiledCW.split (positions k) (length_eq k) (ProfiledCW.flatten (positions k) (length_eq k) f) = f := by
  funext p w
  simp [ProfiledCW.split, ProfiledCW.flatten]

private theorem marginal_counts (k : ℕ) (r : Fin 6) (g : Fin 5) :
    (∑ c : {c : RecursiveThinSplit.Split 4 (DWZ134Fine.parent r) // c.val (DWZ134Fine.keptMode r) = g}, m k r c.val) =
      k ^ 2 * DWZ134Fine.weightCount r *
        (DWZPositiveComponent134.regionalProfile (DWZ134Fine.region r)).count g * DWZ134Fine.denominator := by
  have hs : (∑ c : {c : RecursiveThinSplit.Split 4 (DWZ134Fine.parent r) // c.val (DWZ134Fine.keptMode r) = g}, DWZ134Fine.m r c.val) =
      ∑ c : RecursiveThinSplit.Split 4 (DWZ134Fine.parent r),
        if c.val (DWZ134Fine.keptMode r) = g then DWZ134Fine.m r c else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun c : RecursiveThinSplit.Split 4 (DWZ134Fine.parent r) ↦ c.val (DWZ134Fine.keptMode r) = g)
      (Finset.univ.filter (fun c : RecursiveThinSplit.Split 4 (DWZ134Fine.parent r) ↦ c.val (DWZ134Fine.keptMode r) = g))
      (by intro c; simp) (DWZ134Fine.m r)).symm
  simp only [m, ← Finset.mul_sum]
  rw [hs, mme_dwz_positive_134_integer_fine_profile_validity.2.2.2.2.1 r g]
  ring

private theorem graded_source (k : ℕ) (i : Fin 3) (a : Address 4 6 DWZ134Fine.parent (n k))
    (ha : a ∈ RecursiveXHash.target (m k)) (f : Position (n k) → CompleteSplit.CompleteWord 2)
    (hf : Graded DWZ134Fine.parent_total i a f) :
    source k i (ProfiledCW.flatten (positions k) (length_eq k) f) := by
  unfold source
  rw [split_flatten]
  have ht : ∀ r, RecursiveThinSplit.HasJointCounts (a r) (m k r) := by
    simpa only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  constructor
  · intro r j
    have h0 := hf ⟨r,j,0⟩
    have h1 := hf ⟨r,j,1⟩
    change (∑ w : Fin 2, (f ⟨r,j,0⟩ w).val) = ((a r j).val i).val at h0
    change (∑ w : Fin 2, (f ⟨r,j,1⟩ w).val) = DWZ134Fine.parent r i - ((a r j).val i).val at h1
    rw [Fin.sum_univ_two, h0, h1]
    exact Nat.add_sub_of_le ((a r j).property.2 i)
  · intro r hi g
    subst i
    have hthin : ∀ r, ∃ i, DWZ134Fine.parent r i ≤ 1 := by decide +kernel
    have hmarg := ((mme_recursive_thin_split_marginal_joint_counts 4 (DWZ134Fine.parent r)
      (hthin r) (n k r) (m k r)).1 (a r)).mpr (ht r)
    have he : (Finset.univ.filter (fun j : Fin (n k r) ↦
        (∑ w : Fin 2, (f ⟨r,j,0⟩ w).val) = g.val)) =
        Finset.univ.filter (fun j : Fin (n k r) ↦ (a r j).val (DWZ134Fine.keptMode r) = g) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h0 := hf ⟨r,j,0⟩
      change (∑ w : Fin 2, (f ⟨r,j,0⟩ w).val) = ((a r j).val (DWZ134Fine.keptMode r)).val at h0
      rw [h0]
      exact Fin.ext_iff.symm
    rw [he]
    exact (hmarg (DWZ134Fine.keptMode r) g).trans (marginal_counts k r g)

private theorem scaled_mass (k : ℕ) (i : Fin 3) (c : Cell 4 6 DWZ134Fine.parent) :
    (∑ w, mu k i c w) = m k c.1 c.2 + m k c.1 (complement (DWZ134Fine.parent_total c.1) c.2) := by
  simp only [mu, m, ← Finset.mul_sum,
    mme_dwz_positive_134_integer_fine_profile_validity.2.1, mul_add]

private theorem scaled_support (k : ℕ) (i : Fin 3) (c : Cell 4 6 DWZ134Fine.parent)
    (w : CompleteSplit.CompleteWord 2) (h : 0 < mu k i c w) :
    (∑ j, (w j).val) = (c.2.val i).val := by
  exact mme_dwz_positive_134_integer_fine_profile_validity.2.2.1 i c w (Nat.pos_of_mul_pos_left h)

private theorem scaled_boundary (k : ℕ) : BoundaryProfiles (mu k) := by
  obtain ⟨h0,h1,h2⟩ := mme_dwz_positive_134_integer_fine_profile_validity.2.2.2.1
  refine ⟨?_,?_,?_⟩
  · intro c hc w; simp only [mu, h0 c hc w]
  · intro c hc w; simp only [mu, h1 c hc w]
  · intro c hc w; simp only [mu, h2 c hc w]

private theorem parent_size (k : ℕ) (r : Fin 6) : k ^ 2 ≤ n k r := by
  have hp := mme_dwz_positive_134_integer_fine_profile_validity.2.2.2.2.2.2.1 r
  exact Nat.le_mul_of_pos_right _ hp

private theorem finite_size (k : ℕ) (hk : 97200 * 2 ^ 128 ≤ k) :
    (8 * k : ℝ) * (25 * 6 * (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2) ≤
      ((k ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (-64 : ℤ)) ^ 2 := by
  have hr : (97200 * 2 ^ 128 : ℝ) ≤ k := by exact_mod_cast hk
  have hh := mul_nonneg (sub_nonneg.mpr hr) (show (0 : ℝ) ≤ k by positivity)
  norm_num [CompleteSplit.CompleteWord] at hh ⊢
  nlinarith only [hh]

private noncomputable def step (k : ℕ) (hk : 2 ≤ k) (hsize : 97200 * 2 ^ 128 ≤ k)
    (a : Address 4 6 DWZ134Fine.parent (n k)) (ha : a ∈ RecursiveXHash.target (m k)) :
    IntegerStep 2 (length k) (fun _ _ ↦ True) where
  half := 4
  R := 6
  parent := DWZ134Fine.parent
  n := n k
  total := DWZ134Fine.parent_total
  half_eq := by norm_num
  m := m k
  N := (∑ r, n k r) - 1
  hashPositions := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma]
    have hp : 0 < ∑ r, n k r := by
      rw [n_sum]
      have hN : 0 < DWZ134Fine.totalCount := by decide
      exact Nat.mul_pos (pow_pos (by omega) _) hN
    omega)
  L := blocks k
  positions := positions k
  length := length_eq k
  mu := mu k
  mass := scaled_mass k
  support := scaled_support k
  boundary := scaled_boundary k
  reference := a
  reference_target := ha
  minimum := k ^ 2
  repairScale := k
  minimum_pos := pow_pos (by omega) _
  repairScale_gt_one := by omega
  parent_size := parent_size k
  split_divisible := by intro r c; exact dvd_mul_right _ _
  epsilon := (2 : ℝ) ^ (-64 : ℤ)
  epsilon_pos := by positivity
  size_test := finite_size k hsize
  source_inside := by intros; trivial

private theorem cell_card : Fintype.card (Cell 4 6 DWZ134Fine.parent) = 48 := by
  have h : ∀ r, Fintype.card (RecursiveThinSplit.Split 4 (DWZ134Fine.parent r)) = 8 := by
    intro r
    exact (Fintype.card_congr (DWZ134Fine.splitEquiv r)).symm
  simp only [Cell, Fintype.card_sigma, h]
  norm_num

private theorem rate_lower (k : ℕ) (hk : 0 < k) :
    ((DWZ134Fine.totalCount : ℝ) * (6847993556 / 10000000000 : ℝ)) * (k : ℝ) ^ 2 ≤
      regionalRate DWZ134Fine.parent_total (n k) (m k) (mu k) -
        ((∑ r, n k r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteSplit.CompleteWord 2) ((2 : ℝ) ^ (-64 : ℤ)) := by
  have h := mme_dwz_positive_134_scaled_regional_entropy_floor (k ^ 2) (pow_pos hk _)
  simp only [Nat.cast_mul, Nat.cast_pow] at h
  dsimp only [n, m, mu]
  convert h.le using 1 <;> ring

private theorem joint_scaled (k : ℕ) :
    jointPotential (m k) = (k : ℝ) ^ 2 * jointPotential DWZ134Fine.m := by
  unfold jointPotential
  simp only [m, Nat.cast_mul, Nat.cast_pow]
  simp_rw [(mme_regional_mass_entropy_algebra (C := Unit)).1]
  rw [Finset.mul_sum]

private theorem scale_upper (k : ℕ) (hk : 0 < k) :
    scaleExponent DWZ134Fine.parent_total (n k) (m k) (mu k) ((2 : ℝ) ^ (-64 : ℤ)) ≤
      |jointPotential DWZ134Fine.m| * (k : ℝ) ^ 2 := by
  have hr := rate_lower k hk
  have hpos : 0 ≤ (DWZ134Fine.totalCount : ℝ) * (6847993556 / 10000000000 : ℝ) * (k : ℝ) ^ 2 := by positivity
  have habs := mul_le_mul_of_nonneg_left (le_abs_self (jointPotential DWZ134Fine.m)) (sq_nonneg (k : ℝ))
  calc
    scaleExponent DWZ134Fine.parent_total (n k) (m k) (mu k) ((2 : ℝ) ^ (-64 : ℤ)) =
        jointPotential (m k) - (regionalRate DWZ134Fine.parent_total (n k) (m k) (mu k) -
          ((∑ r, n k r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteSplit.CompleteWord 2) ((2 : ℝ) ^ (-64 : ℤ))) := by
      unfold scaleExponent
      ring
    _ ≤ jointPotential (m k) := sub_le_self _ (hpos.trans hr)
    _ = (k : ℝ) ^ 2 * jointPotential DWZ134Fine.m := joint_scaled k
    _ ≤ (k : ℝ) ^ 2 * |jointPotential DWZ134Fine.m| := habs
    _ = _ := mul_comm _ _

theorem solution :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ a : Address 4 6 DWZ134Fine.parent (n k), a ∈ RecursiveXHash.target (m k) ∧
        ∃ S : ExactStep 2 (length k) (source k),
          Real.exp (((DWZ134Fine.totalCount : ℝ) * (6847993555 / 10000000000 : ℝ)) * (k : ℝ) ^ 2) ≤
            (S.copies : ℝ) ∧ S.output = output k a ∧
          ∀ (K : Type u) [Field K], TensorObj.Restrict
            (TensorObj.bigAdd (fun _ : Fin S.copies ↦ tensor K (output k a))) (tensor K (source k)) := by
  have hN : (0 : ℝ) < DWZ134Fine.totalCount := by norm_num [DWZ134Fine.totalCount, DWZ134Fine.denominator]
  obtain ⟨kE,hkE⟩ := mme_integer_regional_graded_source_cofinal_extraction
    (4 * DWZ134Fine.totalCount) 4 2430 |jointPotential DWZ134Fine.m|
    ((DWZ134Fine.totalCount : ℝ) * (6847993556 / 10000000000 : ℝ))
    ((DWZ134Fine.totalCount : ℝ) * (6847993555 / 10000000000 : ℝ))
    (abs_nonneg _) (by positivity) (by nlinarith)
  refine ⟨max kE (max 2 (97200 * 2 ^ 128)), ?_⟩
  intro k hk
  have hkE' : kE ≤ k := (le_max_left _ _).trans hk
  have hk2 : 2 ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hks : 97200 * 2 ^ 128 ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hkpos : 0 < k := by omega
  obtain ⟨a,ha⟩ := mme_recursive_region_target_nonempty DWZ134Fine.parent (n k) (m k) (counts_sum k)
  let D := step k hk2 hks a ha
  have hsource : ∀ (i : Fin 3) (b : Address D.half D.R D.parent D.n),
      b ∈ RecursiveXHash.target D.m → ∀ f ∈ unbrokenWords D.total i b (D.mu i),
        source k i (ProfiledCW.flatten D.positions D.length f) := by
    intro i b hb f hf
    have hg := (Finset.mem_filter.mp hf).2.1
    exact graded_source k i b hb f hg
  obtain ⟨S,hcopies,houtput,hrestrict⟩ := hkE k hkE' (Q := source k) D rfl
    (le_of_eq (lengths k)) (by rfl) (by simpa only [D, step, cell_card] using (by norm_num : 48 ≤ 2430))
    (by norm_num [D, step]) (by norm_num [D, step, CompleteSplit.CompleteWord])
    (rate_lower k hkpos) (scale_upper k hkpos) hsource
  exact ⟨a,ha,S,hcopies,houtput,hrestrict⟩
