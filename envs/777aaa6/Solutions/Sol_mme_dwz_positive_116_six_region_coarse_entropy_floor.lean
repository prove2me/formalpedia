-- Prove2me | solution 1 for mme_dwz_positive_116_six_region_coarse_entropy_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T16:03:31.648518+00:00
-- url     : https://prove2.me/submissions/63029038-9e32-40e0-afaf-b702476dc320

import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_dwz_positive_116_regional_profile_data
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Cast.Order
open BigOperators

open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace MME.DWZC1Exact116

def alphaCount : Fin 3 → Fin 4 → ℕ := ![
  ![3673632995,499996326693770,499996326693633,3672979602],
  ![21608826818,499978391473154,499978390836412,21608863616],
  ![21608826778,499978390836387,499978390836816,21609500019]]

def regionWeightCount : Fin 3 → ℕ :=
  ![333199364706116,333400336186257,333400299107627]

def alpha (r : Fin 3) (s : Fin 4) : ℚ := alphaCount r s / 1000000000000000

def leftShape : Fin 3 → Fin 4 → Fin 3 → Fin 5 := ![
  ![![0,0,4],![0,1,3],![1,0,3],![1,1,2]],
  ![![0,4,0],![1,3,0],![0,3,1],![1,2,1]],
  ![![4,0,0],![3,0,1],![3,1,0],![2,1,1]]]

def objectId : Fin 3 → Fin 4 → ℕ :=
  ![![7,8,12,76],![11,15,10,77],![21,19,20,78]]

/-- Actual proved child Z frequencies. The 112 frequency is intentionally
the accepted canonical profile, not the old object-76 raw frequency. -/
def childProfile : Fin 3 → Fin 4 → Fin 3 → ℚ := ![
  ![![0,0,1],
    ![0,249999999930157/500000000000000,250000000069843/500000000000000],
    ![0,499999999026019/1000000000000000,500000000973981/1000000000000000],
    ![1/10,4/5,1/10]],
  ![![1,0,0],![1,0,0],
    ![249999999930157/500000000000000,250000000069843/500000000000000,0],
    ![1/2,1/2,0]],
  ![![1,0,0],
    ![499999999026019/1000000000000000,500000000973981/1000000000000000,0],
    ![1,0,0],![1/2,1/2,0]]]

def originalRegionalCounts : Fin 3 → Fin 5 → ℕ := ![
  ![0,0,3672979602,999992653387403,3673632995],
  ![0,0,21608863616,999956782309566,21608826818],
  ![0,0,21609500019,999956781673203,21608826778]]

def originalParentCounts : Fin 5 → ℕ :=
  ![0,0,15632850634043171218716057,999968734317748997496639110491,
    15632831616959332142173452]

def rotatedCoarseCounts : Fin 3 → Fin 5 → ℕ := ![
  ![0,0,3672979602,999992653387403,3673632995],
  ![500000000299972,499999999700028,0,0,0],
  ![499999999663594,500000000336406,0,0,0]]

def positiveSlot : Fin 3 → Fin 5 → Option (Fin 4) := ![
  ![none,none,some 3,none,none],
  ![some 1,some 3,none,none,none],
  ![some 2,some 3,none,none,none]]

theorem positive_slot_exact : ∀ r g s,
    (0 < (leftShape r s 0).val ∧ 0 < (leftShape r s 1).val ∧ leftShape r s 2 = g) ↔
      positiveSlot r g = some s := by
  decide +kernel

theorem original_parent_counts_preserved :
    (∀ r g, (∑ s : Fin 4, if leftShape 0 s 2 = g then alphaCount r s else 0) =
      originalRegionalCounts r g) ∧
    (∀ g, (∑ r : Fin 3, regionWeightCount r * originalRegionalCounts r g) =
      originalParentCounts g) ∧
    (∑ r : Fin 3, regionWeightCount r) = 1000000000000000 ∧
    (∀ r g, (∑ s : Fin 4, if leftShape r s 2 = g then alphaCount r s else 0) =
      rotatedCoarseCounts r g) := by
  decide +kernel

theorem exact_finite_data :
    (∀ r s, 0 < alpha r s) ∧
    (∀ r, ∑ s, alpha r s = 1) ∧
    (∀ r s a, 0 ≤ childProfile r s a) ∧
    (∀ r s, ∑ a, childProfile r s a = 1) ∧
    (∀ r s a, childProfile r s a ≠ 0 →
      ∃ b : Fin 3, a.val + b.val = (leftShape r s 2).val) ∧
    (∀ r s t, (0 < (leftShape r s 0).val ∧ 0 < (leftShape r s 1).val) →
      (0 < (leftShape r t 0).val ∧ 0 < (leftShape r t 1).val) →
      leftShape r s 2 = leftShape r t 2 → s = t) ∧
    (∀ r s, (leftShape r s 2).val + (leftShape r (Fin.rev s) 2).val =
      ![6,1,1] r) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro r s
    fin_cases r <;> fin_cases s <;> norm_num [alpha,alphaCount]
  · intro r
    fin_cases r <;> norm_num [alpha,alphaCount,Fin.sum_univ_succ]
  · intro r s a
    fin_cases r <;> fin_cases s <;> fin_cases a <;> norm_num [childProfile]
  · intro r s
    fin_cases r <;> fin_cases s <;> norm_num [childProfile,Fin.sum_univ_succ]
  · intro r s a
    fin_cases r <;> fin_cases s <;> fin_cases a <;>
      norm_num [childProfile,leftShape,Fin.exists_fin_succ]
    all_goals decide +kernel
  · decide +kernel
  · decide +kernel

end MME.DWZC1Exact116

namespace MME.DWZC1Exact116
noncomputable def entropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)
end MME.DWZC1Exact116

open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MME.DWZC1Exact116
theorem coarse_log_bounds :
    Real.log (500000001 / 1000000000 : ℝ) ≤ -(693146 / 1000000 : ℝ) ∧
    Real.log (3674 / 1000000000 : ℝ) ≤ -(1251 / 100 : ℝ) ∧
    Real.log (2161 / 100000000 : ℝ) ≤ -(537 / 50 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := mme_log_interval_of_exact_rational_series_certificate
      (500000001 / 1000000000) (1 / 1000000001) (-100) (-693146 / 1000000) 1 6
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    simpa only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat,neg_div] using h.2
  · have h := mme_log_interval_of_exact_rational_series_certificate
      (3674 / 1000000000) ((3674 / 1000000000 * 2^19 - 1) /
        (3674 / 1000000000 * 2^19 + 1)) (-100) (-1251 / 100) 19 6
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    simpa only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat,neg_div] using h.2
  · have h := mme_log_interval_of_exact_rational_series_certificate
      (2161 / 100000000) ((2161 / 100000000 * 2^16 - 1) /
        (2161 / 100000000 * 2^16 + 1)) (-100) (-537 / 50) 16 6
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    simpa only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat,neg_div] using h.2


end MME.DWZC1Exact116



open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MME.DWZC1Exact116

def rationalMarginal (r i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ s : Fin 4, if leftShape 0 s i=g then alpha r s else 0

def rareMax (r : Fin 3) : ℚ := if r=0 then 3674/1000000000 else 2161/100000000
def rareLog (r : Fin 3) : ℚ := if r=0 then 1251/100 else 537/50
def rareFloor (r : Fin 3) : ℚ := if r=0 then 99/1000000 else 507/1000000

theorem rational_binary_certificate : ∀ (r i : Fin 3), i≠2 →
    (∀ g, 0 ≤ rationalMarginal r i g ∧ rationalMarginal r i g ≤ 500000001/1000000000) ∧
    (∑ g, rationalMarginal r i g)=1 := by
  decide +kernel

theorem rational_rare_certificate : ∀ r : Fin 3,
    (∀ g, 0 ≤ rationalMarginal r 2 g) ∧
    0 < rationalMarginal r 2 3 ∧
    (∀ g, g≠3 → rationalMarginal r 2 g ≤ rareMax r) ∧
    rareFloor r ≤ ∑ g : Fin 5,
      if g=3 then rationalMarginal r 2 g * (1-rationalMarginal r 2 g)
      else rareLog r * rationalMarginal r 2 g := by
  decide +kernel

end MME.DWZC1Exact116


open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MME.DWZC1Exact116


theorem negMulLog_lower_from_log (x q c : ℝ) (hx : 0 < x) (hxq : x ≤ q)
    (hlog : Real.log q ≤ -c) : c * x ≤ Real.negMulLog x := by
  have h := (Real.log_le_log hx hxq).trans hlog
  have hm := mul_le_mul_of_nonneg_left h hx.le
  simp only [Real.negMulLog_def]
  nlinarith

theorem negMulLog_quadratic_lower (x : ℝ) (hx : 0 < x) :
    x * (1-x) ≤ Real.negMulLog x := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hx.le
  simp only [Real.negMulLog_def]
  nlinarith

noncomputable def baseMarginal (r i : Fin 3) (g : Fin 5) : ℝ :=
  ∑ s : Fin 4, if leftShape 0 s i = g then (alpha r s : ℝ) else 0

theorem binary_entropy_lower (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpsum : p+q=1) (hpb : p ≤ 500000001/1000000000)
    (hqb : q ≤ 500000001/1000000000) :
    346573/500000 ≤ Real.negMulLog p + Real.negMulLog q := by
  have h1 := negMulLog_lower_from_log p _ _ hp hpb coarse_log_bounds.1
  have h2 := negMulLog_lower_from_log q _ _ hq hqb coarse_log_bounds.1
  nlinarith

theorem baseMarginal_eq (r i : Fin 3) (g : Fin 5) :
    baseMarginal r i g = (rationalMarginal r i g : ℝ) := by
  simp only [baseMarginal,rationalMarginal,Rat.cast_sum,apply_ite,Rat.cast_zero]

theorem base_binary_entropy_lower (r : Fin 3) (i : Fin 3) (hi : i≠2) :
    693146/1000000 ≤ entropy (baseMarginal r i) := by
  have hq := rational_binary_certificate r i hi
  have hsum : ∑ g, baseMarginal r i g = 1 := by
    simp_rw [baseMarginal_eq]
    exact_mod_cast hq.2
  calc
    693146/1000000 = ∑ g, (693146/1000000) * baseMarginal r i g := by
      rw [← Finset.mul_sum,hsum,mul_one]
    _ ≤ entropy (baseMarginal r i) := by
      apply Finset.sum_le_sum
      intro g _
      have hg0 : 0 ≤ baseMarginal r i g := by
        rw [baseMarginal_eq]; exact_mod_cast (hq.1 g).1
      by_cases hz : baseMarginal r i g=0
      · simp [hz]
      · apply negMulLog_lower_from_log _ _ _ (lt_of_le_of_ne hg0 (Ne.symm hz)) _ coarse_log_bounds.1
        rw [baseMarginal_eq]
        simpa only [Rat.cast_div,Rat.cast_ofNat] using
          (Rat.cast_le (K := ℝ)).2 ((hq.1 g).2)

theorem base_rare_entropy_lower (r : Fin 3) :
    (rareFloor r : ℝ) ≤ entropy (baseMarginal r 2) := by
  have hq := rational_rare_certificate r
  have hlog : Real.log (rareMax r : ℝ) ≤ -(rareLog r : ℝ) := by
    by_cases hr : r=0
    · simpa only [rareMax,rareLog,if_pos hr,Rat.cast_div,Rat.cast_ofNat] using coarse_log_bounds.2.1
    · simpa only [rareMax,rareLog,if_neg hr,Rat.cast_div,Rat.cast_ofNat] using coarse_log_bounds.2.2
  have hlow : (rareFloor r:ℝ) ≤ ∑ g : Fin 5,
      if g=3 then baseMarginal r 2 g * (1-baseMarginal r 2 g)
      else (rareLog r:ℝ) * baseMarginal r 2 g := by
    simp_rw [baseMarginal_eq]
    have h := (Rat.cast_le (K := ℝ)).2 hq.2.2.2
    simpa only [Rat.cast_sum,apply_ite,Rat.cast_mul,Rat.cast_sub,Rat.cast_one] using h
  apply hlow.trans
  apply Finset.sum_le_sum
  intro g _
  by_cases hg : g=3
  · rw [if_pos hg]
    apply negMulLog_quadratic_lower
    rw [hg,baseMarginal_eq]
    exact_mod_cast hq.2.1
  · rw [if_neg hg]
    have hg0 : 0 ≤ baseMarginal r 2 g := by
      rw [baseMarginal_eq]; exact_mod_cast hq.1 g
    by_cases hz : baseMarginal r 2 g=0
    · simp [hz]
    · apply negMulLog_lower_from_log _ _ _ (lt_of_le_of_ne hg0 (Ne.symm hz)) _ hlog
      rw [baseMarginal_eq]
      exact_mod_cast hq.2.2.1 g hg

def coarseRotation : Fin 3 → Fin 3 → Fin 3 := ![![0,1,2],![1,2,0],![2,0,1]]

def coarseSwapXY : Fin 3 → Fin 3 := ![1,0,2]

noncomputable def sixModeRate (i : Fin 3) : ℝ :=
  ∑ r : Fin 3, (regionWeightCount r : ℝ)/1000000000000000/2 *
    (entropy (baseMarginal r (coarseRotation r i)) +
      entropy (baseMarginal r (coarseRotation r (coarseSwapXY i))))

/-- The two summands are precisely the actual rotated region and its X/Y swap;
each receives half the original regional weight. -/
theorem sixModeRate_actual_marginals (i : Fin 3) : sixModeRate i =
    ∑ r : Fin 3, (regionWeightCount r : ℝ)/1000000000000000/2 *
      ((∑ g : Fin 5, Real.negMulLog (∑ s : Fin 4,
          if leftShape r s i=g then (alpha r s:ℝ) else 0)) +
        (∑ g : Fin 5, Real.negMulLog (∑ s : Fin 4,
          if leftShape r s (coarseSwapXY i)=g then (alpha r s:ℝ) else 0))) := by
  have hrot : ∀ r s i, leftShape r s i=leftShape 0 s (coarseRotation r i) := by
    decide +kernel
  simp only [sixModeRate,entropy,baseMarginal]
  apply Finset.sum_congr rfl
  intro r _
  simp only [hrot r]

theorem sixModeRate_lower (i : Fin 3) :
    (23110935103/50000000000 : ℝ) < sixModeRate i := by
  have h00 := base_binary_entropy_lower 0 0 (by decide)
  have h01 := base_binary_entropy_lower 0 1 (by decide)
  have h10 := base_binary_entropy_lower 1 0 (by decide)
  have h11 := base_binary_entropy_lower 1 1 (by decide)
  have h20 := base_binary_entropy_lower 2 0 (by decide)
  have h21 := base_binary_entropy_lower 2 1 (by decide)
  have h02 := base_rare_entropy_lower 0
  have h12 := base_rare_entropy_lower 1
  have h22 := base_rare_entropy_lower 2
  norm_num [rareFloor,Fin.ext_iff] at h02 h12 h22
  fin_cases i <;>
    norm_num [sixModeRate,Fin.sum_univ_succ,regionWeightCount,coarseRotation,
      coarseSwapXY,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff] <;>
    linarith only [h00,h01,h10,h11,h20,h21,h02,h12,h22]

end MME.DWZC1Exact116


open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MME.DWZC1Exact116

theorem public_alpha_eq :
    alpha 0 = DWZFourthRecursiveWitness.witness0.alpha ∧
    alpha 1 = DWZFourthRecursiveWitness.witness1.alpha ∧
    alpha 2 = DWZFourthRecursiveWitness.witness2.alpha := by
  refine ⟨?_,?_,?_⟩
  all_goals
    funext s
    decide +kernel +revert

theorem public_original_shapes_eq :
    leftShape 0 = DWZFourthRecursiveWitness.witness0.coarseAddress ∧
    leftShape 0 = DWZFourthRecursiveWitness.witness1.coarseAddress ∧
    leftShape 0 = DWZFourthRecursiveWitness.witness2.coarseAddress := by
  exact ⟨rfl,rfl,rfl⟩

theorem public_original_profiles_eq :
    originalParentCounts = DWZPositiveComponent116.parentProfile.count ∧
    DWZPositiveComponent116.parentProfile.denominator = 1000000000000000000000000000000 ∧
    (∀ r, originalRegionalCounts r = (DWZPositiveComponent116.regionalProfile r).count) ∧
    (∀ r, (DWZPositiveComponent116.regionalProfile r).denominator = 1000000000000000) ∧
    regionWeightCount = DWZPositiveComponent116.regionalWeight := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · intro r
    fin_cases r <;> rfl
  · intro r
    fin_cases r <;> rfl


/-- Region 1 cycles X→Z→Y, region 2 cycles twice.  This explicit
mode table removes ambiguity about which marginal enters the six-region rate. -/
def modeRotation : Fin 3 → Fin 3 → Fin 3 :=
  ![![0,1,2],![1,2,0],![2,0,1]]

theorem regional_shape_orientation : ∀ r s i,
    leftShape r s i = leftShape 0 s (modeRotation r i) := by
  decide +kernel

/-- On the actual four-cell support, the three coarse marginals determine
the distribution uniquely.  Thus its constrained maximum-entropy penalty is zero. -/
theorem regional_marginals_unique (r : Fin 3) (p : Fin 4 → ℝ)
    (h : ∀ i g, (∑ s, if leftShape r s i=g then p s else 0) =
      ∑ s, if leftShape r s i=g then (alpha r s:ℝ) else 0) :
    p = fun s => (alpha r s:ℝ) := by
  let inverseMode : Fin 3 → Fin 3 → Fin 3 := ![![0,1,2],![2,0,1],![1,2,0]]
  have fibers : ∀ r : Fin 3,
      (Finset.univ.filter fun s : Fin 4 => leftShape r s (inverseMode r 2)=4)={0} ∧
      (Finset.univ.filter fun s : Fin 4 => leftShape r s (inverseMode r 2)=2)={3} ∧
      (Finset.univ.filter fun s : Fin 4 => leftShape r s (inverseMode r 0)=0)={0,1} ∧
      (Finset.univ.filter fun s : Fin 4 => leftShape r s (inverseMode r 1)=0)={0,2} := by
    decide +kernel
  have h0 := h (inverseMode r 2) 4
  have h3 := h (inverseMode r 2) 2
  have h1 := h (inverseMode r 0) 0
  have h2 := h (inverseMode r 1) 0
  simp only [← Finset.sum_filter,(fibers r).1,Finset.sum_singleton] at h0
  simp only [← Finset.sum_filter,(fibers r).2.1,Finset.sum_singleton] at h3
  simp only [← Finset.sum_filter,(fibers r).2.2.1,Finset.sum_insert,
    Finset.mem_singleton,show (0:Fin 4)≠1 from by decide,not_false_eq_true,
    Finset.sum_singleton] at h1
  simp only [← Finset.sum_filter,(fibers r).2.2.2,Finset.sum_insert,
    Finset.mem_singleton,show (0:Fin 4)≠2 from by decide,not_false_eq_true,
    Finset.sum_singleton] at h2
  funext s
  fin_cases s
  · exact h0
  · rw [h0] at h1
    exact add_left_cancel h1
  · rw [h0] at h2
    exact add_left_cancel h2
  · exact h3

end MME.DWZC1Exact116


theorem solution :
    let a : Fin 3 → Fin 4 → ℚ :=
      ![MME.DWZFourthRecursiveWitness.witness0.alpha,
        MME.DWZFourthRecursiveWitness.witness1.alpha,
        MME.DWZFourthRecursiveWitness.witness2.alpha]
    let rotation : Fin 3 → Fin 3 → Fin 3 := ![![0,1,2],![1,2,0],![2,0,1]]
    let swapXY : Fin 3 → Fin 3 := ![1,0,2]
    let shape : Fin 3 → Fin 4 → Fin 3 → Fin 5 :=
      fun r s i => MME.DWZFourthRecursiveWitness.witness0.coarseAddress s (rotation r i)
    let marginal : Fin 3 → Fin 3 → Fin 5 → ℝ :=
      fun r i g => ∑ s : Fin 4, if shape r s i=g then (a r s:ℝ) else 0
    (∀ (r : Fin 3) (p : Fin 4 → ℝ),
      (∀ (i : Fin 3) (g : Fin 5),
        (∑ s : Fin 4, if shape r s i=g then p s else 0)=marginal r i g) →
      p=fun s => (a r s:ℝ)) ∧
    (∀ i : Fin 3, (23110935103/50000000000 : ℝ) <
      ∑ r : Fin 3, (MME.DWZPositiveComponent116.regionalWeight r:ℝ)/1000000000000000/2 *
        ((∑ g : Fin 5, Real.negMulLog (marginal r i g)) +
         (∑ g : Fin 5, Real.negMulLog (marginal r (swapXY i) g)))) := by
  have ha : MME.DWZC1Exact116.alpha =
      ![MME.DWZFourthRecursiveWitness.witness0.alpha,
        MME.DWZFourthRecursiveWitness.witness1.alpha,
        MME.DWZFourthRecursiveWitness.witness2.alpha] := by
    funext r
    fin_cases r
    · exact MME.DWZC1Exact116.public_alpha_eq.1
    · exact MME.DWZC1Exact116.public_alpha_eq.2.1
    · exact MME.DWZC1Exact116.public_alpha_eq.2.2
  have hs : MME.DWZC1Exact116.leftShape =
      fun r s i => MME.DWZFourthRecursiveWitness.witness0.coarseAddress s
        (MME.DWZC1Exact116.coarseRotation r i) := by
    funext r s i
    rw [MME.DWZC1Exact116.regional_shape_orientation]
    rfl
  have hw : MME.DWZC1Exact116.regionWeightCount =
      MME.DWZPositiveComponent116.regionalWeight := rfl
  have hu := MME.DWZC1Exact116.regional_marginals_unique
  have hf : ∀ i : Fin 3, (23110935103/50000000000:ℝ) <
      ∑ r : Fin 3, (MME.DWZC1Exact116.regionWeightCount r:ℝ)/1000000000000000/2 *
        ((∑ g : Fin 5, Real.negMulLog (∑ s : Fin 4,
            if MME.DWZC1Exact116.leftShape r s i=g then (MME.DWZC1Exact116.alpha r s:ℝ) else 0)) +
          (∑ g : Fin 5, Real.negMulLog (∑ s : Fin 4,
            if MME.DWZC1Exact116.leftShape r s (MME.DWZC1Exact116.coarseSwapXY i)=g
            then (MME.DWZC1Exact116.alpha r s:ℝ) else 0))) := by
    intro i
    rw [← MME.DWZC1Exact116.sixModeRate_actual_marginals]
    exact MME.DWZC1Exact116.sixModeRate_lower i
  rw [ha,hs] at hu
  rw [ha,hs,hw] at hf
  exact ⟨hu,hf⟩
