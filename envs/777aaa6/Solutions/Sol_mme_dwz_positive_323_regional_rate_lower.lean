-- Prove2me | solution 1 for mme_dwz_positive_323_regional_rate_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:32:03.144933+00:00
-- url     : https://prove2.me/submissions/7c9c7d7d-0501-4562-877f-a7b76ccf6456

import Theorems.Thm_mme_dwz_positive_323_integer_fine_profile_validity
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_recursive_thin_split_entropy_penalty_zero
import Theorems.Thm_mme_dwz_fourth_recursive_entropy_upper

namespace MME.DWZPenaltyTransport

open BigOperators MME MME.RecursiveThinSplit


theorem marginal_ite {D : Type*} {I : Type*} [Fintype D] [DecidableEq I] (coord : D → I)
    (p : D → ℝ) (i : I) :
    mme_modern_marginal coord p i = ∑ a, if coord a = i then p a else 0 := by
  unfold mme_modern_marginal
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun a ↦ coord a = i)) (fun a ↦ by simp) p).symm

/-- A same-marginal distribution on the physical splits of a region has entropy at most the
public witness bound of that region, read through a coordinate permutation. -/
theorem entropy_le_witness (w : Fin 63) {S : Type*} [Fintype S]
    (e : Fin (DWZFourthRecursiveWitness.witness w).cellCount ≃ S)
    (coord : S → Fin 3 → Fin 5) (σ : Equiv.Perm (Fin 3))
    (haddr : ∀ a m, (DWZFourthRecursiveWitness.witness w).coarseAddress a m = coord (e a) (σ m))
    (α : S → ℝ) (halpha : ∀ a, ((DWZFourthRecursiveWitness.witness w).alpha a : ℝ) = α (e a))
    (ρ : S → ℝ) (hρ0 : ∀ c, 0 ≤ ρ c) (hρ1 : ∑ c, ρ c = 1)
    (hmarg : ∀ i g, (∑ c, if coord c i = g then ρ c else 0) = ∑ c, if coord c i = g then α c else 0) :
    (∑ c, Real.negMulLog (ρ c)) ≤ ((DWZFourthRecursiveWitness.witness w).entropyUpper : ℝ) := by
  have hsum : ∀ f : S → ℝ, (∑ a, f (e a)) = ∑ c, f c := fun f ↦ Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  have h := mme_dwz_fourth_recursive_entropy_upper w (fun a ↦ ρ (e a)) (fun a ↦ hρ0 _)
    (by rw [hsum ρ]; exact hρ1) (by
      intro mode j
      rw [marginal_ite, marginal_ite]
      simp_rw [haddr, halpha]
      rw [hsum (fun c ↦ if coord c (σ mode) = j then ρ c else 0),
        hsum (fun c ↦ if coord c (σ mode) = j then α c else 0)]
      exact hmarg (σ mode) j)
  rwa [hsum (fun c ↦ Real.negMulLog (ρ c))] at h

/-- The recursive entropy penalty of a region, in nats, is at most the witness bound minus the
entropy of the region's split distribution. -/
theorem penalty_le_witness {half : ℕ} {parent : Fin 3 → ℕ} (w : Fin 63)
    (e : Fin (DWZFourthRecursiveWitness.witness w).cellCount ≃ MME.RecursiveThinSplit.Split half parent)
    (σ : Equiv.Perm (Fin 3)) (hhalf : half = 4)
    (haddr : ∀ a m, ((DWZFourthRecursiveWitness.witness w).coarseAddress a m).val = ((e a).val (σ m)).val)
    (α : MME.RecursiveThinSplit.Split half parent → ℝ)
    (halpha : ∀ a, ((DWZFourthRecursiveWitness.witness w).alpha a : ℝ) = α (e a))
    (hα0 : ∀ c, 0 ≤ α c) (hα1 : ∑ c, α c = 1) :
    Real.log 2 * entropyPenalty α ≤
      ((DWZFourthRecursiveWitness.witness w).entropyUpper : ℝ) - ∑ c, Real.negMulLog (α c) := by
  subst hhalf
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : ∀ ρ ∈ SameMarginalDistributions α,
      mme_modern_entropyBits ρ ≤ ((DWZFourthRecursiveWitness.witness w).entropyUpper : ℝ) / Real.log 2 := by
    rintro ρ ⟨h0, h1, hm⟩
    unfold mme_modern_entropyBits
    apply div_le_div_of_nonneg_right _ hlog.le
    refine entropy_le_witness w e (fun c i ↦ c.val i) σ ?_ α halpha ρ h0 h1 ?_
    · intro a m
      exact Fin.ext (haddr a m)
    · intro i g
      have := hm i g
      rw [marginal_ite, marginal_ite] at this
      exact this
  have hne : (mme_modern_entropyBits '' SameMarginalDistributions α).Nonempty :=
    ⟨_, α, ⟨hα0, hα1, fun _ _ ↦ rfl⟩, rfl⟩
  have hsup : sSup (mme_modern_entropyBits '' SameMarginalDistributions α) ≤
      ((DWZFourthRecursiveWitness.witness w).entropyUpper : ℝ) / Real.log 2 :=
    csSup_le hne (by rintro _ ⟨ρ, hρ, rfl⟩; exact hbound ρ hρ)
  have hb : Real.log 2 * mme_modern_entropyBits α = ∑ c, Real.negMulLog (α c) := by
    unfold mme_modern_entropyBits
    rw [mul_div_cancel₀ _ hlog.ne']
  unfold entropyPenalty
  have := mul_le_mul_of_nonneg_left hsup hlog.le
  rw [mul_div_cancel₀ _ hlog.ne'] at this
  rw [mul_sub, hb]
  linarith

end MME.DWZPenaltyTransport

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.DWZ323Fine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private theorem splitV (r : Fin 6) (j : Fin 10) : (splitEquiv r j).val = shape r j := rfl
private theorem wordV (w : Fin 9) : wordEquiv w = word w := rfl
private theorem mAt (r : Fin 6) (j : Fin 10) :
    m r (splitEquiv r j) = weightCount r * alphaCount (region r) j * denominator := by
  simp only [m, Equiv.symm_apply_apply]
private theorem muAt (r : Fin 6) (j : Fin 10) (i : Fin 3) (w : Fin 9) :
    mu i ⟨r,splitEquiv r j⟩ (wordEquiv w) =
      weightCount r * (alphaCount (region r) j + alphaCount (region r) (Fin.rev j)) * fineCount r j i w := by
  simp only [mu, Equiv.symm_apply_apply]
private theorem compAt (r : Fin 6) (j : Fin 10) :
    complement (parent_total r) (splitEquiv r j) = splitEquiv r (Fin.rev j) := by
  have h : ∀ r j i, parent r i - (shape r j i).val = (shape r (Fin.rev j) i).val := by decide +kernel
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact h r j i

private theorem cell_frequency (r : Fin 6) (j : Fin 10) (i : Fin 3) (w : Fin 9) :
    cellFrequency (mu i) ⟨r,splitEquiv r j⟩ (wordEquiv w) = (beta r j i w : ℝ) := by
  have hm := mme_dwz_positive_323_integer_fine_profile_validity.2.1 i ⟨r,splitEquiv r j⟩
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

private theorem n_weight (r : Fin 6) : (n r : ℝ) = (totalCount : ℝ) * (weight r : ℝ) := by
  have h : ∀ r, (n r : ℚ) = totalCount * weight r := by decide +kernel
  exact_mod_cast h r

private theorem m_alpha (r : Fin 6) (j : Fin 10) :
    (m r (splitEquiv r j) : ℝ) = (n r : ℝ) * (alpha r j : ℝ) := by
  rw [mAt]
  have h : ∀ r j, ((weightCount r * alphaCount (region r) j * denominator : ℕ) : ℚ) =
      n r * alpha r j := by decide +kernel
  exact_mod_cast h r j

private theorem n_ne (r : Fin 6) : (n r : ℝ) ≠ 0 := by
  exact_mod_cast ne_of_gt (mme_dwz_positive_323_integer_fine_profile_validity.2.2.2.2.2.2.1 r)

private theorem mixture (r : Fin 6) (i : Fin 3) (a b : Fin 9) :
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

private theorem coarse_counts (r : Fin 6) (i : Fin 3) (g : Fin 5) :
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

private theorem coarse_total (r : Fin 6) (i : Fin 3) : ∑ g, (coarse r i g : ℝ) = 1 := by
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

private def rotP : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩

private def swapP : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩

/-- Coordinate frame of each region relative to its regional parent. -/
private def sigmaR : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, swapP, rotP.symm, rotP.symm.trans swapP, rotP, rotP.trans swapP]

private theorem cell_count : ∀ r : Fin 6,
    (DWZFourthRecursiveWitness.witness (witnessIndex (region r))).cellCount = 10 := by
  decide +kernel

private theorem witness_addr : ∀ (r : Fin 6) (a : Fin 10) (k : Fin 3),
    ((DWZFourthRecursiveWitness.witness (witnessIndex (region r))).coarseAddress
      (Fin.cast (cell_count r).symm a) k).val = (shape r a (sigmaR r k)).val := by
  decide +kernel

private theorem witness_alpha : ∀ (r : Fin 6) (a : Fin 10),
    (DWZFourthRecursiveWitness.witness (witnessIndex (region r))).alpha
      (Fin.cast (cell_count r).symm a) = alpha r a := by
  decide +kernel

private theorem penalty_le : penaltyPotential n m ≤ (totalCount : ℝ) * penaltyRate := by
  unfold penaltyPotential penaltyRate
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  let e : Fin (DWZFourthRecursiveWitness.witness (witnessIndex (region r))).cellCount ≃
      RecursiveThinSplit.Split 4 (parent r) := (finCongr (cell_count r)).trans (splitEquiv r)
  have hs : (∑ c, (m r c : ℝ) / n r) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, mme_dwz_positive_323_integer_fine_profile_validity.1]
    exact div_self (n_ne r)
  have hα : ∀ j, (m r (splitEquiv r j) : ℝ) / n r = (alpha r j : ℝ) := by
    intro j
    rw [m_alpha, mul_comm, mul_div_assoc, div_self (n_ne r), mul_one]
  have key := MME.DWZPenaltyTransport.penalty_le_witness (witnessIndex (region r)) e (sigmaR r) rfl
    (fun a k ↦ by
      have h := witness_addr r (Fin.cast (cell_count r) a) k
      simp only [Fin.cast_cast, Fin.cast_eq_self] at h
      rw [h]
      rfl)
    (fun c ↦ (m r c : ℝ) / n r)
    (fun a ↦ by
      have h := witness_alpha r (Fin.cast (cell_count r) a)
      simp only [Fin.cast_cast, Fin.cast_eq_self] at h
      rw [h]
      exact (hα _).symm)
    (fun c ↦ by positivity) hs
  have hent : ratEntropy (alpha r) = ∑ c, Real.negMulLog ((m r c : ℝ) / n r) := by
    unfold ratEntropy
    exact Fintype.sum_equiv (splitEquiv r) _ _ (fun j ↦ by rw [hα])
  rw [hent, ← mul_assoc, ← n_weight, mul_assoc]
  exact mul_le_mul_of_nonneg_left key (Nat.cast_nonneg _)

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

private theorem sum_cells {T : Type*} [AddCommMonoid T] (f : Cell 4 6 parent → T) :
    (∑ c, f c) = ∑ r, ∑ j : Fin 10, f ⟨r,splitEquiv r j⟩ := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  exact ((splitEquiv r).sum_comp (fun c ↦ f ⟨r,c⟩)).symm

private theorem boundary_at (i : Fin 2) (r : Fin 6) (j : Fin 10) :
    yzBoundary i ⟨r,splitEquiv r j⟩ ↔ boundary i r j = true := by
  fin_cases i <;> simp [yzBoundary, yBoundary, zBoundary, boundary, splitV]

private theorem boundary_zero (i : Fin 2) (r : Fin 6) (j : Fin 10) (h : boundary i r j ≠ true) :
    ratMassEntropy (partMass i r (j.castAdd 5)) = 0 := by
  have hz : ∀ i r j, boundary i r j ≠ true → ∀ w, partMass i r (j.castAdd 5) w = 0 := by
    decide +kernel
  simp [ratMassEntropy, ratEntropy, hz i r j h]

private theorem boundary_calibration (i : Fin 2) (r : Fin 6) (j : Fin 10) (w : Fin 9)
    (h : boundary i r j = true) :
    (mu (yzMode i) ⟨r,splitEquiv r j⟩ (wordEquiv w) : ℝ) =
      (n r : ℝ) * (partMass i r (j.castAdd 5) w : ℝ) := by
  rw [muAt]
  have hc : ∀ i r j w, boundary i r j = true →
      ((weightCount r * (alphaCount (region r) j + alphaCount (region r) (Fin.rev j)) *
        fineCount r j (yzMode i) w : ℕ) : ℚ) = n r * partMass i r (j.castAdd 5) w := by
    decide +kernel
  exact_mod_cast hc i r j w h

private theorem interior_calibration (i : Fin 2) (r : Fin 6) (g : Fin 5) (w : Fin 9) :
    (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) (Sum.inr (r,g)) (wordEquiv w) : ℝ) =
      (n r : ℝ) * (partMass i r (g.natAdd 10) w : ℝ) := by
  dsimp only [partCount]
  rw [sum_cells]
  simp only [boundary_at, modeGroup, splitV, muAt]
  have hc : ∀ i r g w,
      ((∑ r' : Fin 6, ∑ j : Fin 10,
        if ¬ boundary i r' j = true ∧ (r',shape r' j (yzMode i)) = (r,g)
        then weightCount r' * (alphaCount (region r') j + alphaCount (region r') (Fin.rev j)) *
          fineCount r' j (yzMode i) w else 0 : ℕ) : ℚ) = n r * partMass i r (g.natAdd 10) w := by
    decide +kernel
  have hh := congrArg (fun q : ℚ ↦ (q : ℝ)) (hc i r g w)
  simpa only [Rat.cast_mul, Rat.cast_natCast] using hh

private theorem boundary_entropy (i : Fin 2) (r : Fin 6) (j : Fin 10) (h : boundary i r j = true) :
    massEntropy (fun w ↦ (mu (yzMode i) ⟨r,splitEquiv r j⟩ w : ℝ)) =
      (n r : ℝ) * ratMassEntropy (partMass i r (j.castAdd 5)) := by
  rw [mass_word_sum]
  simp_rw [boundary_calibration i r j _ h]
  rw [(mme_regional_mass_entropy_algebra (C := Unit)).1]
  simp only [massEntropy, entropy, ratMassEntropy, ratEntropy, Rat.cast_sum]

private theorem interior_entropy (i : Fin 2) (r : Fin 6) (g : Fin 5) :
    massEntropy (fun w ↦
      (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) (Sum.inr (r,g)) w : ℝ)) =
      (n r : ℝ) * ratMassEntropy (partMass i r (g.natAdd 10)) := by
  rw [mass_word_sum]
  simp_rw [interior_calibration]
  rw [(mme_regional_mass_entropy_algebra (C := Unit)).1]
  simp only [massEntropy, entropy, ratMassEntropy, ratEntropy, Rat.cast_sum]

private theorem sum_boundary (i : Fin 2) :
    (∑ c : {c : Cell 4 6 parent // yzBoundary i c},
      massEntropy (fun w ↦ (mu (yzMode i) c.val w : ℝ))) =
        ∑ r, (n r : ℝ) * ∑ j : Fin 10, ratMassEntropy (partMass i r (j.castAdd 5)) := by
  have hs : (∑ c : {c : Cell 4 6 parent // yzBoundary i c},
      massEntropy (fun w ↦ (mu (yzMode i) c.val w : ℝ))) =
      ∑ c : Cell 4 6 parent, if yzBoundary i c then massEntropy (fun w ↦ (mu (yzMode i) c w : ℝ)) else 0 := by
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
  change (∑ c : {c : Cell 4 6 parent // yzBoundary i c},
      massEntropy (fun w ↦ (mu (yzMode i) c.val w : ℝ))) +
    (∑ g : Fin 6 × Fin 5, massEntropy (fun w ↦
      (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) (Sum.inr g) w : ℝ))) = _
  rw [sum_boundary, Fintype.sum_prod_type]
  simp_rw [interior_entropy, ← Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  unfold compatibilityRate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← mul_add, n_weight]
  rw [Fin.sum_univ_add (fun s : Fin (10 + 5) ↦ ratMassEntropy (partMass i r s))]
  ring

theorem solution :
    (totalCount : ℝ) * explicitRate ≤ regionalRate parent_total n m mu := by
  have hp : 0 ≤ (totalCount : ℝ) := by positivity
  have hc0 : compatibilityPotential 0 (mu 1) = (totalCount : ℝ) * compatibilityRate 0 := compatibility_identity 0
  have hc1 : compatibilityPotential 1 (mu 2) = (totalCount : ℝ) * compatibilityRate 1 := compatibility_identity 1
  unfold regionalRate explicitRate
  rw [coarse_identity, parent_identity, parent_identity, hc0, hc1]
  rw [mul_min_of_nonneg _ _ hp, mul_min_of_nonneg _ _ hp]
  refine min_le_min ?_ (min_le_min (le_of_eq (by ring)) (le_of_eq (by ring)))
  have := penalty_le
  rw [mul_sub]
  linarith
