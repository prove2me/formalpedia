-- Prove2me | solution 1 for mme_dwz_positive_611_regional_rate_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T18:26:05.386444+00:00
-- url     : https://prove2.me/submissions/e0587631-30d0-4bbd-bf94-58ba2a4a8d76

import Theorems.Thm_mme_dwz_positive_611_integer_fine_profile_validity
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_recursive_thin_split_entropy_penalty_zero

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.DWZ611Fine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private theorem splitV (r : Fin 4) (j : Fin 4) : (splitEquiv r j).val = shape r j := rfl
private theorem wordV (w : Fin 9) : wordEquiv w = word w := rfl
private theorem mAt (r : Fin 4) (j : Fin 4) :
    m r (splitEquiv r j) = weightCount r * alphaCount (region r) j * denominator := by
  simp only [m, Equiv.symm_apply_apply]
private theorem muAt (r : Fin 4) (j : Fin 4) (i : Fin 3) (w : Fin 9) :
    mu i ⟨r,splitEquiv r j⟩ (wordEquiv w) =
      weightCount r * (alphaCount (region r) j + alphaCount (region r) (Fin.rev j)) * fineCount r j i w := by
  simp only [mu, Equiv.symm_apply_apply]
private theorem compAt (r : Fin 4) (j : Fin 4) :
    complement (parent_total r) (splitEquiv r j) = splitEquiv r (Fin.rev j) := by
  have h : ∀ r j i, parent r i - (shape r j i).val = (shape r (Fin.rev j) i).val := by decide +kernel
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact h r j i

private theorem cell_frequency (r : Fin 4) (j : Fin 4) (i : Fin 3) (w : Fin 9) :
    cellFrequency (mu i) ⟨r,splitEquiv r j⟩ (wordEquiv w) = (beta r j i w : ℝ) := by
  have hm := mme_dwz_positive_611_integer_fine_profile_validity.2.1 i ⟨r,splitEquiv r j⟩
  have hrat : ∀ r j i w,
      ((weightCount r * (alphaCount (region r) j + alphaCount (region r) (Fin.rev j)) * fineCount r j i w : ℕ) : ℚ) /
        ((weightCount r * alphaCount (region r) j * denominator +
          weightCount r * alphaCount (region r) (Fin.rev j) * denominator : ℕ) : ℚ) = beta r j i w := by
    decide +kernel
  unfold cellFrequency
  rw [hm]
  simp only [muAt, compAt, mAt]
  have hh := congrArg (fun q : ℚ ↦ (q : ℝ)) (hrat r j i w)
  simpa only [Rat.cast_div, Rat.cast_natCast] using hh

private theorem n_weight (r : Fin 4) : (n r : ℝ) = (totalCount : ℝ) * (weight r : ℝ) := by
  have h : ∀ r, (n r : ℚ) = totalCount * weight r := by decide +kernel
  exact_mod_cast h r

private theorem m_alpha (r : Fin 4) (j : Fin 4) :
    (m r (splitEquiv r j) : ℝ) = (n r : ℝ) * (alpha r j : ℝ) := by
  rw [mAt]
  have h : ∀ r j, ((weightCount r * alphaCount (region r) j * denominator : ℕ) : ℚ) =
      n r * alpha r j := by decide +kernel
  exact_mod_cast h r j

private theorem n_ne (r : Fin 4) : (n r : ℝ) ≠ 0 := by
  exact_mod_cast ne_of_gt (mme_dwz_positive_611_integer_fine_profile_validity.2.2.2.2.2.2.1 r)

private theorem mixture (r : Fin 4) (i : Fin 3) (a b : Fin 9) :
    parentMixture parent_total n m (mu i) r ![wordEquiv a,wordEquiv b] =
      (jointWord r i a b : ℝ) := by
  unfold parentMixture
  rw [← (splitEquiv r).sum_comp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, cell_frequency, compAt, m_alpha]
  unfold jointWord
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  field_simp [n_ne r]

private theorem word_sum {f : CompleteSplit.CompleteWord 2 → ℝ} :
    (∑ w, f w) = ∑ w : Fin 9, f (wordEquiv w) := (wordEquiv.sum_comp f).symm

private theorem mass_word_sum (f : CompleteSplit.CompleteWord 2 → ℝ) :
    massEntropy f = massEntropy (fun w : Fin 9 ↦ f (wordEquiv w)) := by
  unfold massEntropy entropy
  rw [word_sum (f := fun w ↦ Real.negMulLog (f w)), word_sum (f := f)]

private theorem coarse_counts (r : Fin 4) (i : Fin 3) (g : Fin 5) :
    (marginalCounts m i r g : ℝ) = (n r : ℝ) * (coarse r i g : ℝ) := by
  have hsub : (∑ c : {c : RecursiveThinSplit.Split 4 (parent r) // c.val i = g}, m r c.val) =
      ∑ c : RecursiveThinSplit.Split 4 (parent r), if c.val i = g then m r c else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun c : RecursiveThinSplit.Split 4 (parent r) ↦ c.val i = g)
      (Finset.univ.filter (fun c : RecursiveThinSplit.Split 4 (parent r) ↦ c.val i = g))
      (by intro c; simp) (m r)).symm
  unfold marginalCounts
  rw [hsub, ← (splitEquiv r).sum_comp]
  simp only [splitV, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, m_alpha]
  unfold coarse
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : shape r j i = g <;> simp [h]

private theorem coarse_total (r : Fin 4) (i : Fin 3) : ∑ g, (coarse r i g : ℝ) = 1 := by
  have h : ∀ r i, (∑ g, coarse r i g) = 1 := by decide +kernel
  exact_mod_cast h r i

private theorem coarse_identity : coarsePotential m 0 = (totalCount : ℝ) * coarseRate := by
  unfold coarsePotential coarseRate
  simp_rw [coarse_counts]
  simp_rw [(mme_regional_mass_entropy_algebra (C := Unit)).1]
  simp only [massEntropy]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [n_weight, coarse_total r 0]
  simp only [Real.negMulLog_one, sub_zero, entropy, ratEntropy, mul_assoc]

private theorem penalty_zero : penaltyPotential n m = 0 := by
  unfold penaltyPotential
  apply Finset.sum_eq_zero
  intro r hr
  have hs : (∑ c, (m r c : ℝ) / n r) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, mme_dwz_positive_611_integer_fine_profile_validity.1]
    exact div_self (n_ne r)
  have ht : ∀ r, ∃ i, parent r i ≤ 1 := by decide +kernel
  rw [(mme_recursive_thin_split_entropy_penalty_zero 4 (parent r) (ht r) _
    (fun _ ↦ by positivity) hs).2.2]
  simp

private theorem joint_sum (f : (Fin 2 → CompleteSplit.CompleteWord 2) → ℝ) :
    (∑ w, f w) = ∑ a : Fin 9, ∑ b : Fin 9, f ![wordEquiv a,wordEquiv b] := by
  let e : (Fin 9 × Fin 9) ≃ (Fin 2 → CompleteSplit.CompleteWord 2) :=
    { toFun := fun p ↦ ![wordEquiv p.1,wordEquiv p.2]
      invFun := fun w ↦ (wordEquiv.symm (w 0),wordEquiv.symm (w 1))
      left_inv := by intro p; simp
      right_inv := by intro w; funext i; fin_cases i <;> simp }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  rfl

private theorem parent_identity (i : Fin 3) :
    parentPotential parent_total n m (mu i) = (totalCount : ℝ) * parentRate i := by
  unfold parentPotential entropy parentRate
  simp_rw [joint_sum, mixture]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [n_weight]
  ring

private theorem sum_cells {T : Type*} [AddCommMonoid T] (f : Cell 4 4 parent → T) :
    (∑ c, f c) = ∑ r, ∑ j : Fin 4, f ⟨r,splitEquiv r j⟩ := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  exact ((splitEquiv r).sum_comp (fun c ↦ f ⟨r,c⟩)).symm

private theorem boundary_at (i : Fin 2) (r : Fin 4) (j : Fin 4) :
    yzBoundary i ⟨r,splitEquiv r j⟩ ↔ boundary i r j = true := by
  fin_cases i <;> simp [yzBoundary, yBoundary, zBoundary, boundary, splitV]

private theorem boundary_zero (i : Fin 2) (r : Fin 4) (j : Fin 4) (h : boundary i r j ≠ true) :
    ratMassEntropy (partMass i r (j.castAdd 5)) = 0 := by
  have hz : ∀ i r j, boundary i r j ≠ true → ∀ w, partMass i r (j.castAdd 5) w = 0 := by
    decide +kernel
  simp [ratMassEntropy, ratEntropy, hz i r j h]

private theorem boundary_calibration (i : Fin 2) (r : Fin 4) (j : Fin 4) (w : Fin 9)
    (h : boundary i r j = true) :
    (mu (yzMode i) ⟨r,splitEquiv r j⟩ (wordEquiv w) : ℝ) =
      (n r : ℝ) * (partMass i r (j.castAdd 5) w : ℝ) := by
  rw [muAt]
  have hc : ∀ i r j w, boundary i r j = true →
      ((weightCount r * (alphaCount (region r) j + alphaCount (region r) (Fin.rev j)) *
        fineCount r j (yzMode i) w : ℕ) : ℚ) = n r * partMass i r (j.castAdd 5) w := by
    decide +kernel
  exact_mod_cast hc i r j w h

private theorem interior_calibration (i : Fin 2) (r : Fin 4) (g : Fin 5) (w : Fin 9) :
    (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) (Sum.inr (r,g)) (wordEquiv w) : ℝ) =
      (n r : ℝ) * (partMass i r (g.natAdd 4) w : ℝ) := by
  dsimp only [partCount]
  rw [sum_cells]
  simp only [boundary_at, modeGroup, splitV, muAt]
  have hc : ∀ i r g w,
      ((∑ r' : Fin 4, ∑ j : Fin 4,
        if ¬ boundary i r' j = true ∧ (r',shape r' j (yzMode i)) = (r,g)
        then weightCount r' * (alphaCount (region r') j + alphaCount (region r') (Fin.rev j)) *
          fineCount r' j (yzMode i) w else 0 : ℕ) : ℚ) = n r * partMass i r (g.natAdd 4) w := by
    decide +kernel
  have hh := congrArg (fun q : ℚ ↦ (q : ℝ)) (hc i r g w)
  simpa only [Rat.cast_mul, Rat.cast_natCast] using hh

private theorem boundary_entropy (i : Fin 2) (r : Fin 4) (j : Fin 4) (h : boundary i r j = true) :
    massEntropy (fun w ↦ (mu (yzMode i) ⟨r,splitEquiv r j⟩ w : ℝ)) =
      (n r : ℝ) * ratMassEntropy (partMass i r (j.castAdd 5)) := by
  rw [mass_word_sum]
  simp_rw [boundary_calibration i r j _ h]
  rw [(mme_regional_mass_entropy_algebra (C := Unit)).1]
  simp only [massEntropy, entropy, ratMassEntropy, ratEntropy, Rat.cast_sum]

private theorem interior_entropy (i : Fin 2) (r : Fin 4) (g : Fin 5) :
    massEntropy (fun w ↦
      (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) (Sum.inr (r,g)) w : ℝ)) =
      (n r : ℝ) * ratMassEntropy (partMass i r (g.natAdd 4)) := by
  rw [mass_word_sum]
  simp_rw [interior_calibration]
  rw [(mme_regional_mass_entropy_algebra (C := Unit)).1]
  simp only [massEntropy, entropy, ratMassEntropy, ratEntropy, Rat.cast_sum]

private theorem sum_boundary (i : Fin 2) :
    (∑ c : {c : Cell 4 4 parent // yzBoundary i c},
      massEntropy (fun w ↦ (mu (yzMode i) c.val w : ℝ))) =
        ∑ r, (n r : ℝ) * ∑ j : Fin 4, ratMassEntropy (partMass i r (j.castAdd 5)) := by
  have hs : (∑ c : {c : Cell 4 4 parent // yzBoundary i c},
      massEntropy (fun w ↦ (mu (yzMode i) c.val w : ℝ))) =
      ∑ c : Cell 4 4 parent, if yzBoundary i c then massEntropy (fun w ↦ (mu (yzMode i) c w : ℝ)) else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := yzBoundary i)
      (Finset.univ.filter (yzBoundary i)) (by intro c; simp)
      (fun c ↦ massEntropy (fun w ↦ (mu (yzMode i) c w : ℝ)))).symm
  rw [hs, sum_cells]
  simp only [boundary_at]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hb : boundary i r j = true
  · simp only [if_pos hb, boundary_entropy i r j hb]
  · simp only [if_neg hb, boundary_zero i r j hb, mul_zero]

private theorem compatibility_identity (i : Fin 2) :
    compatibilityPotential i (mu (yzMode i)) = (totalCount : ℝ) * compatibilityRate i := by
  unfold compatibilityPotential
  rw [(mme_regional_mass_entropy_algebra).2.2, Fintype.sum_sum_type]
  change (∑ c : {c : Cell 4 4 parent // yzBoundary i c},
      massEntropy (fun w ↦ (mu (yzMode i) c.val w : ℝ))) +
    (∑ g : Fin 4 × Fin 5, massEntropy (fun w ↦
      (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) (Sum.inr g) w : ℝ))) = _
  rw [sum_boundary, Fintype.sum_prod_type]
  simp_rw [interior_entropy, ← Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  unfold compatibilityRate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← mul_add, n_weight]
  rw [Fin.sum_univ_add (fun s : Fin (4 + 5) ↦ ratMassEntropy (partMass i r s))]
  ring

theorem solution :
    regionalRate parent_total n m mu = (totalCount : ℝ) * explicitRate := by
  have hp : 0 ≤ (totalCount : ℝ) := by positivity
  have hc0 : compatibilityPotential 0 (mu 1) = (totalCount : ℝ) * compatibilityRate 0 := compatibility_identity 0
  have hc1 : compatibilityPotential 1 (mu 2) = (totalCount : ℝ) * compatibilityRate 1 := compatibility_identity 1
  unfold regionalRate explicitRate
  rw [coarse_identity, penalty_zero, sub_zero, parent_identity, parent_identity,
    hc0, hc1]
  rw [← mul_sub, ← mul_sub, ← mul_min_of_nonneg _ _ hp, ← mul_min_of_nonneg _ _ hp]
