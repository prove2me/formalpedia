-- Prove2me | solution 1 for mme_released_level2_zero_half_boundary_recipe
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T04:29:54.579991+00:00
-- url     : https://prove2.me/submissions/a1411042-0e60-42c4-affb-f48c91d6dfcb

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_released_positive_integer_frame_data
import Theorems.Thm_mme_exact_profile_boundary_end
import Theorems.Thm_mme_nat_multinomial_log_lower_mass_entropy
import Theorems.Thm_mme_released_positive_integer_frame
import Theorems.Thm_mme_released_level2_zero_half_mass_entropy_certificate
open BigOperators Filter MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false
set_option maxRecDepth 100000

namespace C8P
open RecStage

abbrev ZC := (ρ : Fin 6) × {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) //
  ∃ j, (c.2.val j).val = 0}

/-- The unit mass `M(z)` of a zero cell. -/
def Mz (z : ZC) : ℕ :=
  m3 z.1 z.2.1.1 z.2.1.2 + m3 z.1 z.2.1.1 (complement (htotal3 z.1 z.2.1.1) z.2.1.2)

/-- The first zero coordinate of the half-grade triple. -/
def j0 (z : ZC) : Fin 3 :=
  if (z.2.1.2.val 0).val = 0 then 0 else if (z.2.1.2.val 1).val = 0 then 1 else 2

theorem j0_spec (z : ZC) : (z.2.1.2.val (j0 z)).val = 0 := by
  obtain ⟨j, hj⟩ := z.2.2
  unfold j0
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · fin_cases j
    · exact absurd hj h0
    · exact absurd hj h1
    · exact hj

theorem cert_mode (z : ZC) :
    (if (z.2.1.2.val 0).val = 0 then (1 : Fin 3) else if (z.2.1.2.val 1).val = 0 then 2 else 0) =
      j0 z + 1 := by
  unfold j0; split_ifs <;> rfl

/-- The certificate summand. -/
noncomputable def Vc (z : ZC) : ℝ :=
  MME.RegionRate.massEntropy (fun w ↦ (RecStage.mu3 z.1
      (if (z.2.1.2.val 0).val = 0 then 1 else if (z.2.1.2.val 1).val = 0 then 2 else 0)
      z.2.1 w : ℝ)) +
    ((∑ w, RecStage.mu3 z.1
      (if (z.2.1.2.val 0).val = 0 then 1 else if (z.2.1.2.val 1).val = 0 then 2 else 0)
      z.2.1 w * Boundary.ones w : ℕ) : ℝ) * Real.log 5

/-! ### Frame facts: mass, support and boundary profiles of `mu3` -/

theorem frame_facts (ρ : Fin 6) :
    (∀ i c, ∑ w, mu3 ρ i c w = m3 ρ c.1 c.2 + m3 ρ c.1 (complement (htotal3 ρ c.1) c.2)) ∧
    (∀ i c w, 0 < mu3 ρ i c w → ∑ h, (w h).val = (c.2.val i).val) ∧
    BoundaryProfiles (mu3 ρ) := by
  obtain ⟨F⟩ := mme_released_positive_integer_frame ρ 1 one_pos
  refine ⟨fun i c ↦ ?_, fun i c w h ↦ ?_, ?_⟩
  · have := F.mass i c
    simpa only [one_mul] using this
  · exact F.support i c w (by rw [one_mul]; exact h)
  · obtain ⟨b1, b2, b3⟩ := F.boundary
    refine ⟨fun c h w ↦ ?_, fun c h w ↦ ?_, fun c h w ↦ ?_⟩
    · have := b1 c h w; simpa only [one_mul] using this
    · have := b2 c h w; simpa only [one_mul] using this
    · have := b3 c h w; simpa only [one_mul] using this

theorem grade_zero_word (w : CompleteSplit.CompleteWord 2) (h : ∑ r, (w r).val = 0) :
    w = fun _ ↦ 0 := by
  funext r
  have := (Finset.sum_eq_zero_iff.mp h) r (Finset.mem_univ _)
  exact Fin.ext this

theorem F1 (z : ZC) (m : Fin 3) : ∑ w, mu3 z.1 m z.2.1 w = Mz z :=
  (frame_facts z.1).1 m z.2.1

theorem F2 (z : ZC) (m : Fin 3) (w : CompleteSplit.CompleteWord 2) (h : mu3 z.1 m z.2.1 w ≠ 0) :
    CWCells.grade w = (z.2.1.2.val m).val :=
  (frame_facts z.1).2.1 m z.2.1 w (Nat.pos_of_ne_zero h)

theorem F0 (z : ZC) (w : CompleteSplit.CompleteWord 2) :
    mu3 z.1 (j0 z) z.2.1 w = if w = (fun _ ↦ 0) then Mz z else 0 := by
  have hz : ∀ v : CompleteSplit.CompleteWord 2, v ≠ (fun _ ↦ 0) → mu3 z.1 (j0 z) z.2.1 v = 0 := by
    intro v hv
    by_contra h
    have := F2 z (j0 z) v h
    rw [j0_spec z] at this
    exact hv (grade_zero_word v this)
  split_ifs with hw
  · subst hw
    have := F1 z (j0 z)
    rw [Finset.sum_eq_single (fun _ ↦ 0)] at this
    · exact this
    · intro b _ hb; exact hz b hb
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact hz w hw

theorem flip_rev {ell : ℕ} (w : CompleteSplit.CompleteWord ell) :
    Boundary.flipLabel w = fun r ↦ Fin.rev (w r) := by
  funext r
  apply Fin.ext
  simp only [Boundary.flipLabel, Fin.val_rev]
  omega

theorem flip_flip {ell : ℕ} (w : CompleteSplit.CompleteWord ell) :
    Boundary.flipLabel (Boundary.flipLabel w) = w := by
  funext r
  apply Fin.ext
  simp only [Boundary.flipLabel]
  have := (w r).isLt
  omega

def flipEquiv (ell : ℕ) : CompleteSplit.CompleteWord ell ≃ CompleteSplit.CompleteWord ell :=
  ⟨Boundary.flipLabel, Boundary.flipLabel, flip_flip, flip_flip⟩

theorem ones_flip {ell : ℕ} (w : CompleteSplit.CompleteWord ell) :
    Boundary.ones (Boundary.flipLabel w) = Boundary.ones w := by
  unfold Boundary.ones
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Boundary.flipLabel, Fin.ext_iff]
  have := (w r).isLt
  constructor <;> intro h <;> simp only [Fin.val_one] at h ⊢ <;> omega

theorem F3 (z : ZC) (w : CompleteSplit.CompleteWord 2) :
    mu3 z.1 (j0 z + 2) z.2.1 w = mu3 z.1 (j0 z + 1) z.2.1 (Boundary.flipLabel w) := by
  obtain ⟨hb2, hb0, hb1⟩ := (frame_facts z.1).2.2
  have hj := j0_spec z
  unfold j0 at hj ⊢
  split_ifs at hj ⊢ with h0 h1
  · -- zero X coordinate: modes 2 and 1
    rw [flip_rev]; exact hb0 z.2.1 h0 w
  · -- zero Y coordinate: modes 0 and 2
    show mu3 z.1 0 z.2.1 w = mu3 z.1 2 z.2.1 (Boundary.flipLabel w)
    rw [hb1 z.2.1 h1 (Boundary.flipLabel w), ← flip_rev, flip_flip]
  · -- zero Z coordinate: modes 1 and 0
    show mu3 z.1 1 z.2.1 w = mu3 z.1 0 z.2.1 (Boundary.flipLabel w)
    rw [flip_rev]; exact hb2 z.2.1 hj w

theorem pair (j m m' : Fin 3) (h1 : m ≠ j) (h2 : m' ≠ j) (h3 : m ≠ m') :
    (m = j + 1 ∧ m' = j + 2) ∨ (m = j + 2 ∧ m' = j + 1) := by
  revert j m m'; decide

/-! ### Mass entropy bookkeeping -/

theorem ME_smul {W : Type*} [Fintype W] (a : ℝ) (x : W → ℝ) :
    MME.RegionRate.massEntropy (fun w ↦ a * x w) = a * MME.RegionRate.massEntropy x := by
  unfold MME.RegionRate.massEntropy MME.RegionRate.entropy
  rw [← Finset.mul_sum, Real.negMulLog_mul]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem ME_comp {W : Type*} [Fintype W] (x : W → ℝ) (f : W ≃ W) :
    MME.RegionRate.massEntropy (fun w ↦ x (f w)) = MME.RegionRate.massEntropy x := by
  unfold MME.RegionRate.massEntropy MME.RegionRate.entropy
  rw [Equiv.sum_comp f (fun w ↦ Real.negMulLog (x w)), Equiv.sum_comp f x]

/-- The certificate value does not depend on which non-zero mode is used. -/
theorem Vmode (z : ZC) (m : Fin 3) (hm : m ≠ j0 z) :
    MME.RegionRate.massEntropy (fun w ↦ (mu3 z.1 m z.2.1 w : ℝ)) +
      ((∑ w, mu3 z.1 m z.2.1 w * Boundary.ones w : ℕ) : ℝ) * Real.log 5 = Vc z := by
  unfold Vc
  rw [cert_mode z]
  have hcases : m = j0 z + 1 ∨ m = j0 z + 2 := by
    revert hm; generalize j0 z = j; revert m j; decide
  rcases hcases with rfl | rfl
  · rfl
  · have e1 : (fun w ↦ (mu3 z.1 (j0 z + 2) z.2.1 w : ℝ)) =
        fun w ↦ (fun v ↦ (mu3 z.1 (j0 z + 1) z.2.1 v : ℝ)) (flipEquiv 2 w) := by
      funext w; rw [F3]; rfl
    have e2 : (∑ w, mu3 z.1 (j0 z + 2) z.2.1 w * Boundary.ones w) =
        ∑ w, mu3 z.1 (j0 z + 1) z.2.1 w * Boundary.ones w := by
      rw [← Equiv.sum_comp (flipEquiv 2) (fun w ↦ mu3 z.1 (j0 z + 1) z.2.1 w * Boundary.ones w)]
      apply Finset.sum_congr rfl
      intro w _
      rw [F3]
      show _ = mu3 z.1 (j0 z + 1) z.2.1 (Boundary.flipLabel w) *
        Boundary.ones (Boundary.flipLabel w)
      rw [ones_flip]
    rw [e2, e1]
    exact congrArg (fun t ↦ t + ((∑ w, mu3 z.1 (j0 z + 1) z.2.1 w * Boundary.ones w : ℕ) : ℝ) *
      Real.log 5) (ME_comp (fun v ↦ (mu3 z.1 (j0 z + 1) z.2.1 v : ℝ)) (flipEquiv 2))

/-! ### Size bounds -/

theorem wAt_le : ∀ ρ : Fin 6, ∀ r : Fin 88, wAt ρ r ≤ 10 ^ 23 := by
  decide +kernel

theorem alpha_le : ∀ ρ : Fin 6, ∀ r : Fin 88,
    (cellsAt ρ r).all (fun x ↦ decide (x.2.1 ≤ 10 ^ 12)) = true := by
  decide +kernel

theorem cellRec_le (ρ : Fin 6) (r : Fin 88)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r)) :
    (cellRec ρ r c).1 ≤ 10 ^ 12 := by
  unfold cellRec
  split
  · rename_i x hx
    have hmem := List.mem_of_find?_eq_some hx
    have := List.all_eq_true.mp (alpha_le ρ r) x hmem
    simpa using this
  · exact Nat.zero_le _

theorem m3_le (ρ : Fin 6) (r : Fin 88)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r)) :
    m3 ρ r c ≤ 10 ^ 59 := by
  unfold m3
  have h1 := wAt_le ρ r
  have h2 := cellRec_le ρ r c
  have hD : D ^ 2 = 10 ^ 24 := rfl
  rw [hD]
  calc wAt ρ r * (cellRec ρ r c).1 * 10 ^ 24 ≤ 10 ^ 23 * 10 ^ 12 * 10 ^ 24 :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) le_rfl
    _ = 10 ^ 59 := by norm_num

theorem Mz_le (z : ZC) : Mz z ≤ 10 ^ 60 := by
  unfold Mz
  have := m3_le z.1 z.2.1.1 z.2.1.2
  have := m3_le z.1 z.2.1.1 (complement (htotal3 z.1 z.2.1.1) z.2.1.2)
  omega

theorem card_split (P : Fin 3 → ℕ) :
    Fintype.card (RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) P) ≤ 125 := by
  refine (Fintype.card_subtype_le _).trans ?_
  simp

theorem card_ZC : Fintype.card ZC ≤ 66000 := by
  rw [Fintype.card_sigma]
  calc ∑ ρ : Fin 6, Fintype.card {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) //
          ∃ j, (c.2.val j).val = 0}
      ≤ ∑ _ρ : Fin 6, 11000 := by
        apply Finset.sum_le_sum
        intro ρ _
        refine (Fintype.card_subtype_le _).trans ?_
        rw [Fintype.card_sigma]
        calc ∑ r : Fin 88, Fintype.card (RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r))
            ≤ ∑ _r : Fin 88, 125 := Finset.sum_le_sum (fun r _ ↦ card_split _)
          _ = 11000 := by simp
    _ = 66000 := by simp

theorem log_loss (K M : ℕ) (hK : 1 ≤ K) (hM : M ≤ 10 ^ 60) :
    9 * Real.log (6 * (((K * M : ℕ) : ℝ) + 1)) ≤ 4950 * K := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hnat : 6 * (K * M + 1) ≤ 10 ^ 61 * K := by
    have : K * M ≤ K * 10 ^ 60 := Nat.mul_le_mul le_rfl hM
    nlinarith
  have hpos : (0 : ℝ) < 6 * (((K * M : ℕ) : ℝ) + 1) := by positivity
  have h1 : 6 * (((K * M : ℕ) : ℝ) + 1) ≤ (10 : ℝ) ^ 61 * K := by exact_mod_cast hnat
  have h2 : Real.log (6 * (((K * M : ℕ) : ℝ) + 1)) ≤ Real.log ((10 : ℝ) ^ 61 * K) :=
    Real.log_le_log hpos h1
  have h3 : Real.log ((10 : ℝ) ^ 61 * K) = 61 * Real.log 10 + Real.log K := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  rw [h3] at h2
  have h10 : Real.log 10 ≤ 10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hlK : Real.log K ≤ K - 1 := Real.log_le_sub_one_of_pos (by linarith)
  push_cast at h2 ⊢
  linarith

/-! ### Multinomial lower bound, as in the unit boundary certificate -/

theorem gen {C : Type} [Fintype C] (z : C → CompleteSplit.CompleteWord 2 → ℕ) :
    ∑ c : C, (MME.RegionRate.massEntropy (fun s ↦ (z c s : ℝ)) +
        ((∑ s, z c s * Boundary.ones s : ℕ) : ℝ) * Real.log 5) -
      ∑ c : C, 9 * Real.log (6 * (((∑ s, z c s : ℕ) : ℝ) + 1)) ≤
    Real.log ((∏ c : C,
      ((∑ s, z c s).factorial / ∏ s, (z c s).factorial) *
      5 ^ (∑ s, z c s * Boundary.ones s) : ℕ) : ℝ) := by
  have hcard : (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) = 9 := by
    simp [CompleteSplit.CompleteWord]
  have hpos : ∀ c : C, 0 < ((∑ s, z c s).factorial / ∏ s, (z c s).factorial) := by
    intro c
    have := Nat.multinomial_pos (Finset.univ : Finset (CompleteSplit.CompleteWord 2))
      (fun s ↦ z c s)
    simpa [Nat.multinomial] using this
  rw [Nat.cast_prod, Real.log_prod]
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro c _
    have hl := mme_nat_multinomial_log_lower_mass_entropy (z c)
    rw [hcard] at hl
    have hM : (0:ℝ) < (((∑ s, z c s).factorial / ∏ s, (z c s).factorial : ℕ) : ℝ) := by
      exact_mod_cast hpos c
    rw [Nat.cast_mul, Real.log_mul hM.ne' (by positivity), Nat.cast_pow, Real.log_pow]
    push_cast at hl ⊢
    linarith
  · intro c _
    have := hpos c
    positivity

theorem count_comp {L : ℕ} {C C' W : Type*} (zc : Fin L → C) (e : C ≃ C')
    (f : Fin L → W) (z : C) (w : W) :
    RecursiveYZ.count (fun p ↦ e (zc p)) f (e z) w = RecursiveYZ.count zc f z w := by
  unfold RecursiveYZ.count
  congr 1
  ext p
  simp [e.injective.eq_iff]

end C8P

set_option maxHeartbeats 4000000 in
open C8P RecStage in
theorem solution :
    ∃ C : ℕ, ∀ᶠ K : ℕ in atTop, ∀ (L : ℕ)
      (zc : Fin L → (ρ : Fin 6) × {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) //
        ∃ j, (c.2.val j).val = 0}),
      (∀ z, Fintype.card {p : Fin L // zc p = z} =
        K * (RecStage.m3 z.1 z.2.1.1 z.2.1.2 +
          RecStage.m3 z.1 z.2.1.1 (complement (RecStage.htotal3 z.1 z.2.1.1) z.2.1.2))) →
      ∃ R : LogJointRecipeG (L * 2 ^ (2 - 1)) 2 (fun i x ↦
          (∀ p, CWCells.grade (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl x p) =
            ((zc p).2.1.2.val ((ReleasedJointInterior.roleEquiv (zc p).1).symm i)).val) ∧
          Useful zc (fun z w ↦ K * RecStage.mu3 z.1
              ((ReleasedJointInterior.roleEquiv z.1).symm i) z.2.1 w)
            (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl x)),
        1 ≤ R.inputs ∧ R.inputs ≤ (K + 1) ^ C ∧ 0 ≤ R.logOutputs ∧ 1 ≤ R.a * R.b * R.c ∧
        ((209101632051 * 6 * 10 ^ 49 : ℕ) : ℝ) * K ≤
          Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  classical
  refine ⟨0, Filter.eventually_atTop.2 ⟨1, fun K hK L zc hcard ↦ ?_⟩⟩
  -- indexing of the zero cells
  set e : ZC ≃ Fin (Fintype.card ZC) := Fintype.equivFin ZC with he
  let σ : ZC → Equiv.Perm (Fin 3) := fun z ↦ ReleasedJointInterior.roleEquiv z.1
  let cellF : Fin L → Fin (Fintype.card ZC) := fun p ↦ e (zc p)
  let zero : Fin (Fintype.card ZC) → Fin 3 := fun k ↦ σ (e.symm k) (j0 (e.symm k))
  let grd : Fin (Fintype.card ZC) → Fin 3 → ℕ := fun k i ↦
    ((e.symm k).2.1.2.val ((σ (e.symm k)).symm i)).val
  let mode : ZC → Fin 3 := fun z ↦ (σ z).symm (σ z (j0 z) + 1)
  let cnt : Fin (Fintype.card ZC) → CompleteSplit.CompleteWord 2 → ℕ := fun k w ↦
    K * mu3 (e.symm k).1 (mode (e.symm k)) (e.symm k).2.1 w
  have hmode : ∀ z, mode z ≠ j0 z := by
    intro z h
    have h' : σ z (j0 z) + 1 = σ z (j0 z) := by
      have := congrArg (σ z) h
      simpa [mode] using this
    revert h'; generalize σ z (j0 z) = a; revert a; decide
  have hcardF : ∀ k, Fintype.card {p : Fin L // cellF p = k} = K * Mz (e.symm k) := by
    intro k
    rw [show K * Mz (e.symm k) = Fintype.card {p : Fin L // zc p = e.symm k} from
      (hcard (e.symm k)).symm]
    refine Fintype.card_congr (Equiv.subtypeEquivRight (fun p ↦ ?_))
    show e (zc p) = k ↔ zc p = e.symm k
    exact e.apply_eq_iff_eq_symm_apply
  have htot : ∀ k, grd k 0 + grd k 1 + grd k 2 = 2 * 2 ^ (2 - 1) := by
    intro k
    have h1 := (e.symm k).2.1.2.property.1
    have h2 := Equiv.sum_comp (σ (e.symm k)).symm (fun j ↦ ((e.symm k).2.1.2.val j).val)
    simp only [Fin.sum_univ_three] at h2
    simp only [grd]
    omega
  have hzero : ∀ k, grd k (zero k) = 0 := by
    intro k
    simp only [grd, zero, Equiv.symm_apply_apply]
    exact j0_spec _
  have hcount : ∀ k, ∑ s, cnt k s = Fintype.card {p : Fin L // cellF p = k} := by
    intro k
    rw [hcardF, ← F1 (e.symm k) (mode (e.symm k)), Finset.mul_sum]
  have hsupport : ∀ k s, cnt k s ≠ 0 → CWCells.grade s = grd k (zero k + 1) := by
    intro k s h
    have h' : mu3 (e.symm k).1 (mode (e.symm k)) (e.symm k).2.1 s ≠ 0 := by
      intro h0; apply h; simp [cnt, h0]
    exact F2 _ _ _ h'
  obtain ⟨B, hB⟩ := mme_exact_profile_boundary_end (ell := 2) (N := L * 2 ^ (2 - 1)) (L := L)
    (K := Fintype.card ZC) rfl cellF zero grd htot hzero cnt hcount hsupport
  -- the boundary source lies inside the target source
  have incl : ∀ i x,
      ((∀ p, CWCells.grade (ProfiledCW.split (Equiv.refl (Fin L)) rfl x p) = grd (cellF p) i) ∧
        Useful cellF (fun c s ↦
          if i = zero c then (if s = (fun _ ↦ 0) then Fintype.card {p : Fin L // cellF p = c} else 0)
          else if i = zero c + 1 then cnt c s else cnt c (Boundary.flipLabel s))
          (ProfiledCW.split (Equiv.refl (Fin L)) rfl x)) →
      ((∀ p, CWCells.grade (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl x p) =
          ((zc p).2.1.2.val ((ReleasedJointInterior.roleEquiv (zc p).1).symm i)).val) ∧
        Useful zc (fun z w ↦ K * RecStage.mu3 z.1
            ((ReleasedJointInterior.roleEquiv z.1).symm i) z.2.1 w)
          (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl x)) := by
    intro i x ⟨hg, hu⟩
    refine ⟨fun p ↦ ?_, fun z w ↦ ?_⟩
    · rw [hg p]
      have key : ∀ z' : ZC, z' = zc p → (z'.2.1.2.val ((σ z').symm i)).val =
          ((zc p).2.1.2.val ((ReleasedJointInterior.roleEquiv (zc p).1).symm i)).val := by
        rintro z' rfl; rfl
      exact key _ (e.symm_apply_apply _)
    · have h1 := hu (e z) w
      rw [count_comp zc e] at h1
      rw [h1]
      beta_reduce
      rw [hcardF (e z)]
      have key : ∀ z' : ZC, z' = z →
          (if i = σ z' (j0 z') then (if w = (fun _ ↦ 0) then K * Mz z' else 0)
            else if i = σ z' (j0 z') + 1 then K * mu3 z'.1 (mode z') z'.2.1 w
            else K * mu3 z'.1 (mode z') z'.2.1 (Boundary.flipLabel w)) =
          K * mu3 z.1 ((σ z).symm i) z.2.1 w := by
        rintro z' rfl
        split_ifs with hi0 hw hi1
        · subst hi0; subst hw
          rw [Equiv.symm_apply_apply, F0]; simp
        · subst hi0
          rw [Equiv.symm_apply_apply, F0, if_neg hw, mul_zero]
        · subst hi1; rfl
        · have hm1 : (σ z').symm i ≠ j0 z' := by
            intro h; apply hi0; rw [← h]; simp
          have hm3 : (σ z').symm i ≠ mode z' := by
            intro h; apply hi1
            have := congrArg (σ z') h
            simpa [mode] using this
          rcases pair (j0 z') ((σ z').symm i) (mode z') hm1 (hmode z') hm3 with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [ha, hb, F3, C8P.flip_flip]
          · rw [ha, hb, F3]
      exact key _ (e.symm_apply_apply z)
  let B' : ProfiledCW.BoundaryEnd 2 (L * 2 ^ (2 - 1)) (fun i x ↦
      (∀ p, CWCells.grade (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl x p) =
        ((zc p).2.1.2.val ((ReleasedJointInterior.roleEquiv (zc p).1).symm i)).val) ∧
      Useful zc (fun z w ↦ K * RecStage.mu3 z.1
          ((ReleasedJointInterior.roleEquiv z.1).symm i) z.2.1 w)
        (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl x)) :=
    { B with inside := fun i x h ↦ incl i x (B.inside i x h) }
  have hdims : (LogJointRecipeG.base (LogRecipe.boundary B')).a *
      (LogJointRecipeG.base (LogRecipe.boundary B')).b *
      (LogJointRecipeG.base (LogRecipe.boundary B')).c = B.a * B.b * B.c := rfl
  -- the dimension product in terms of the counts
  have hB' : B.a * B.b * B.c = ∏ k : Fin (Fintype.card ZC),
      ((∑ s, cnt k s).factorial / ∏ s, (cnt k s).factorial) *
        5 ^ (∑ s, cnt k s * Boundary.ones s) := by
    rw [hB]
    apply Finset.prod_congr rfl
    intro k _
    rw [hcount k]
  have hlog := gen cnt
  rw [← hB'] at hlog
  -- the entropy terms
  have hterm : ∀ k, MME.RegionRate.massEntropy (fun s ↦ (cnt k s : ℝ)) +
      ((∑ s, cnt k s * Boundary.ones s : ℕ) : ℝ) * Real.log 5 = K * Vc (e.symm k) := by
    intro k
    rw [← Vmode (e.symm k) (mode (e.symm k)) (hmode _)]
    have h1 : (fun s ↦ (cnt k s : ℝ)) =
        fun s ↦ (K : ℝ) * (mu3 (e.symm k).1 (mode (e.symm k)) (e.symm k).2.1 s : ℝ) := by
      funext s; simp [cnt]
    have h2 : (∑ s, cnt k s * Boundary.ones s) =
        K * ∑ s, mu3 (e.symm k).1 (mode (e.symm k)) (e.symm k).2.1 s * Boundary.ones s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [cnt]; ring
    rw [h1, ME_smul, h2, Nat.cast_mul]
    ring
  have hsum1 : ∑ k : Fin (Fintype.card ZC), (MME.RegionRate.massEntropy (fun s ↦ (cnt k s : ℝ)) +
      ((∑ s, cnt k s * Boundary.ones s : ℕ) : ℝ) * Real.log 5) = K * ∑ z : ZC, Vc z := by
    rw [Finset.sum_congr rfl (fun k _ ↦ hterm k), ← Finset.mul_sum, Equiv.sum_comp e.symm Vc]
  have hcert : ((12546098100 * 10 ^ 51 : ℕ) : ℝ) ≤ ∑ z : ZC, Vc z :=
    mme_released_level2_zero_half_mass_entropy_certificate
  have hloss : ∑ k : Fin (Fintype.card ZC), 9 * Real.log (6 * (((∑ s, cnt k s : ℕ) : ℝ) + 1)) ≤
      (66000 * 4950 : ℝ) * K := by
    have hk : ∀ k : Fin (Fintype.card ZC),
        9 * Real.log (6 * (((∑ s, cnt k s : ℕ) : ℝ) + 1)) ≤ 4950 * K := by
      intro k
      rw [hcount k, hcardF k]
      exact log_loss K _ hK (Mz_le _)
    calc _ ≤ ∑ _k : Fin (Fintype.card ZC), (4950 * K : ℝ) := Finset.sum_le_sum (fun k _ ↦ hk k)
      _ = (Fintype.card ZC : ℝ) * (4950 * K) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 66000 * (4950 * K) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_ZC
      _ = _ := by ring
  refine ⟨LogJointRecipeG.base (LogRecipe.boundary B'), le_rfl, by simp [LogJointRecipeG.inputs,
    LogRecipe.inputs], by simp [LogJointRecipeG.logOutputs, LogRecipe.logOutputs], ?_, ?_⟩
  · rw [hdims, hB']
    apply Finset.one_le_prod'
    intro k _
    have hpos : 0 < ((∑ s, cnt k s).factorial / ∏ s, (cnt k s).factorial) := by
      have := Nat.multinomial_pos (Finset.univ : Finset (CompleteSplit.CompleteWord 2))
        (fun s ↦ cnt k s)
      simpa [Nat.multinomial] using this
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hpos.ne' (pow_ne_zero _ (by norm_num)))
  · rw [hdims]
    rw [hsum1] at hlog
    have hKr : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hnum : ((209101632051 * 6 * 10 ^ 49 : ℕ) : ℝ) + 66000 * 4950 ≤
        ((12546098100 * 10 ^ 51 : ℕ) : ℝ) := by
      have : (209101632051 * 6 * 10 ^ 49 + 66000 * 4950 : ℕ) ≤ 12546098100 * 10 ^ 51 := by
        norm_num
      exact_mod_cast this
    generalize ((209101632051 * 6 * 10 ^ 49 : ℕ) : ℝ) = T at hnum ⊢
    generalize ((12546098100 * 10 ^ 51 : ℕ) : ℝ) = C0 at hnum hcert
    generalize (∑ z : ZC, Vc z) = V at hcert hlog
    generalize Real.log (((B.a * B.b * B.c : ℕ) : ℝ)) = Lg at hlog ⊢
    generalize (∑ k : Fin (Fintype.card ZC), 9 * Real.log (6 * (((∑ s, cnt k s : ℕ) : ℝ) + 1))) = E at hloss hlog
    have h3 := mul_le_mul_of_nonneg_left hcert hKr
    have h4 := mul_le_mul_of_nonneg_left hnum hKr
    rw [mul_add] at h4
    have h5 : T * K = K * T := mul_comm _ _
    rw [h5]
    linarith only [h3, h4, hloss, hlog, hKr]
