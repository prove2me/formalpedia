-- Prove2me | solution 1 for mme_released_recursive_level2_structure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T20:38:45.371249+00:00
-- url     : https://prove2.me/submissions/e221de64-c7c7-4cdd-bfad-865de4ebb6f6

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_yz_compatibility
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_released_recursive_stage_structure_valid
open BigOperators MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization MME.RecStage
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.RecStage

theorem word1_zero (z : Fin (2 ^ (1 - 1))) : z = 0 := by
  have h1 := z.isLt
  simp only [pow_zero] at h1
  exact Fin.ext (by omega)

theorem hmass2 (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2) :
    ∑ w, mu2 i c w = m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2) :=
  mme_released_recursive_stage_structure_valid.2.1 i c

/-- At level two the histogram of a half is the indicator of its own grade. -/
theorem mu2_eq (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2) (w : CompleteSplit.CompleteWord 1) :
    mu2 i c w = if (w 0).val = (c.2.val i).val then m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2) else 0 :=
  rfl

/-- Every part of the compatibility partition is supported on a single word, so its potential
vanishes. -/
theorem compat_zero (i : Fin 2) :
    RegionRealization.potential (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i))) = 0 := by
  classical
  unfold RegionRealization.potential
  refine Finset.sum_eq_zero (fun s _ ↦ ?_)
  -- every part is concentrated on one letter
  obtain ⟨g, hg⟩ : ∃ g : ℕ, ∀ w : CompleteSplit.CompleteWord 1,
      partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i)) s w ≠ 0 → (w 0).val = g := by
    rcases s with c | ⟨r, j⟩
    · exact ⟨(c.1.2.val (yzMode i)).val, by
        intro w hw
        unfold partCount at hw
        simp only [mu2] at hw
        split_ifs at hw with h
        · exact h
        · exact absurd rfl hw⟩
    · refine ⟨j.val, ?_⟩
      intro w hw
      unfold partCount at hw
      have : ∃ c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2,
          (¬ yzBoundary i c ∧ modeGroup (yzMode i) c = (r, j)) ∧ mu2 (yzMode i) c w ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hw (Finset.sum_eq_zero (fun c _ ↦ by
          by_cases hcond : ¬ yzBoundary i c ∧ modeGroup (yzMode i) c = (r, j)
          · rw [if_pos hcond]
            exact hc c hcond
          · rw [if_neg hcond]))
      obtain ⟨c, ⟨-, hmode⟩, hne⟩ := this
      simp only [mu2] at hne
      split_ifs at hne with h
      · rw [h]
        have : modeGroup (yzMode i) c = (c.1, c.2.val (yzMode i)) := rfl
        rw [this] at hmode
        exact congrArg Fin.val (congrArg Prod.snd hmode)
      · exact absurd rfl hne
  set S := (∑ w, partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i)) s w : ℕ) with hS
  by_cases hzero : S = 0
  · rw [hS] at hzero
    have : ∀ w, partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i)) s w = 0 := by
      intro w
      have := Finset.sum_eq_zero_iff.mp hzero w (Finset.mem_univ w)
      exact this
    simp [hS, hzero, mme_modern_entropyBits, entropy, Real.negMulLog, this]
  · -- one letter carries all the mass, so every frequency is 0 or 1
    have hfreq : ∀ w : CompleteSplit.CompleteWord 1,
        Real.negMulLog ((partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i)) s w : ℝ) / (S : ℝ)) = 0 := by
      intro w
      by_cases hw : partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i)) s w = 0
      · simp [hw, Real.negMulLog]
      · have hall : ∀ v : CompleteSplit.CompleteWord 1,
            partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i)) s v ≠ 0 → v = w := by
          intro v hv
          have h1 := hg v hv
          have h2 := hg w hw
          funext z
          rw [word1_zero z]
          exact Fin.ext (by omega)
        have hsum : S = partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i)) s w := by
          rw [hS]
          refine Finset.sum_eq_single w (fun v _ hv ↦ ?_) (fun h ↦ absurd (Finset.mem_univ w) h)
          by_contra hne
          exact hv (hall v hne)
        rw [← hsum]
        have hSpos : (0 : ℝ) < S := by
          have : 0 < S := Nat.pos_of_ne_zero hzero
          exact_mod_cast this
        rw [div_self hSpos.ne']
        simp [Real.negMulLog]
    simp only [mme_modern_entropyBits, entropy]
    rw [Finset.sum_congr rfl (fun w _ ↦ hfreq w)]
    simp

/-- Cell frequencies at level two are indicators of the cell's grade. -/
theorem cellFreq2 (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2)
    (w : CompleteSplit.CompleteWord 1) :
    cellFrequency (mu2 i) c w =
      if (w 0).val = (c.2.val i).val then
        (if m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2) = 0 then 0 else 1) else 0 := by
  classical
  unfold cellFrequency
  rw [hmass2 i c, mu2_eq]
  set M := m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2) with hM
  by_cases hz : M = 0
  · simp [hz]
  · have hMpos : (0 : ℝ) < M := by
      have : 0 < M := Nat.pos_of_ne_zero hz
      exact_mod_cast this
    by_cases hw : (w 0).val = (c.2.val i).val
    · rw [if_pos hw, if_pos hw, if_neg hz, div_self hMpos.ne']
    · rw [if_neg hw, if_neg hw]
      simp

/-- One-letter words are their letter. -/
def word1Equiv : CompleteSplit.CompleteWord 1 ≃ Fin 3 where
  toFun w := w 0
  invFun a := fun _ ↦ a
  left_inv := by
    intro w
    funext z
    rw [word1_zero z]
  right_inv := fun _ ↦ rfl

/-- Sum over pairs of level-1 words as a double sum over the two grades. -/
theorem sum_word1_pair (f : ℕ → ℕ → ℝ) :
    ∑ w : Fin 2 → CompleteSplit.CompleteWord 1, f (w 0 0).val (w 1 0).val =
      ∑ a : Fin 3, ∑ b : Fin 3, f a.val b.val := by
  classical
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((finTwoArrowEquiv _).trans (Equiv.prodCongr word1Equiv word1Equiv))
    _ _ (fun w ↦ rfl)

/-- The parent mixture at level two is the mode-`i` marginal of the split distribution. -/
theorem mix2 (i : Fin 3) (r : Fin 1104) (w : Fin 2 → CompleteSplit.CompleteWord 1) :
    parentMixture htotal2 n2 m2 (mu2 i) r w =
      (∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        (if (w 0 0).val = (c.val i).val ∧
            (w 1 0).val = ((complement (htotal2 r) c).val i).val then (m2 r c : ℝ) else 0)) /
        (n2 r : ℝ) := by
  classical
  unfold parentMixture
  congr 1
  refine Finset.sum_congr rfl (fun c _ ↦ ?_)
  rw [cellFreq2 i ⟨r, c⟩, cellFreq2 i ⟨r, complement (htotal2 r) c⟩]
  by_cases hz : m2 r c = 0
  · have : (m2 r c : ℝ) = 0 := by exact_mod_cast hz
    rw [this]
    simp
  · have hmass : m2 r c + m2 r (complement (htotal2 r) c) ≠ 0 := by omega
    have hmass' : m2 r (complement (htotal2 r) c) +
        m2 r (complement (htotal2 r) (complement (htotal2 r) c)) ≠ 0 := by
      rw [complement_complement]
      omega
    simp only [hmass, hmass', if_false, ite_not]
    by_cases h0 : (w 0 0).val = (c.val i).val <;>
      by_cases h1 : (w 1 0).val = ((complement (htotal2 r) c).val i).val <;>
      simp [h0, h1]

end MME.RecStage

theorem solution :
    (∀ i : Fin 2, RegionRealization.potential
        (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i))) = 0) ∧
    ∀ (i : Fin 3) (r : Fin 1104) (w : Fin 2 → CompleteSplit.CompleteWord 1),
      parentMixture htotal2 n2 m2 (mu2 i) r w =
        (∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
          (if (w 0 0).val = (c.val i).val ∧
              (w 1 0).val = ((complement (htotal2 r) c).val i).val then (m2 r c : ℝ) else 0)) /
          (n2 r : ℝ) :=
  ⟨MME.RecStage.compat_zero, MME.RecStage.mix2⟩
