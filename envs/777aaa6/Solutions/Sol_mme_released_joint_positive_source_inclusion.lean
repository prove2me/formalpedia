-- Prove2me | solution 1 for mme_released_joint_positive_source_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T03:31:52.729198+00:00
-- url     : https://prove2.me/submissions/f4336171-55d3-4979-bf4f-67000bf7a1e1

import Definitions.Def_mme_released_global_two_part_split_data
import Theorems.Thm_mme_released_interior_scaled_parent_graded_fine_word_window
import Theorems.Thm_mme_released_joint_interior_owner_parent_typical
import Theorems.Thm_mme_released_joint_interior_fine_selection
import Theorems.Thm_mme_released_joint_interior_owner_fine_partition
import Theorems.Thm_mme_released_joint_interior_owner_mass
import Theorems.Thm_mme_released_interior_boundary_classification
import Theorems.Thm_mme_released_global_word_counts_row_marginal

set_option autoImplicit false

open scoped BigOperators Classical
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.MoreAsymmetryExactSeed

namespace JointPositiveSource

private abbrev ownerBlocks (k : ℕ) (j : Fin 270) :=
  k * ReleasedJointInterior.weight j * denominator ^ 4

private noncomputable def ownerLabel (k : ℕ) (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k)
    (b : ReleasedRecursive.Asm.PBlk k a) : Fin 270 :=
  finProdFinEquiv (b.val.1, ReleasedGlobal.shapeEquiv.symm
    (ReleasedRecursive.Asm.cellOf k a b.val))

private abbrev OwnerFiber (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) (j : Fin 270) :=
  {b : ReleasedRecursive.Asm.PBlk k a // ownerLabel k a b = j}

private theorem label_eq_iff (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k)
    (b : ReleasedRecursive.Asm.PBlk k a) (j : Fin 270) :
    ownerLabel k a b = j ↔
      b.val.1 = (ReleasedJointInterior.component j).1 ∧
      ReleasedRecursive.Asm.cellOf k a b.val =
        ReleasedGlobal.shapeEquiv (ReleasedJointInterior.component j).2 := by
  change finProdFinEquiv (b.val.1, ReleasedGlobal.shapeEquiv.symm
    (ReleasedRecursive.Asm.cellOf k a b.val)) = j ↔ _
  constructor
  · intro h
    have hpair := congrArg (finProdFinEquiv : Fin 6 × Fin 45 ≃ Fin 270).symm h
    simp only [Equiv.symm_apply_apply] at hpair
    refine ⟨congrArg Prod.fst hpair, ?_⟩
    have hc := congrArg (fun p : Fin 6 × Fin 45 => ReleasedGlobal.shapeEquiv p.2) hpair
    simpa only [Equiv.apply_symm_apply] using hc
  · rintro ⟨ho, hc⟩
    apply (finProdFinEquiv : Fin 6 × Fin 45 ≃ Fin 270).symm.injective
    rw [Equiv.symm_apply_apply]
    apply Prod.ext
    · exact ho
    · exact (congrArg ReleasedGlobal.shapeEquiv.symm hc).trans
        (ReleasedGlobal.shapeEquiv.symm_apply_apply _)

private theorem interior_iff (o : Fin 6) (s : Fin 45) :
    (ReleasedInterior.seed o s).boundary = [] ↔
      ¬ ReleasedRecursive.Asm.isZeroCell (ReleasedGlobal.shapeEquiv s) := by
  rw [mme_released_interior_boundary_classification]
  change (∀ i : Fin 3, 0 < ((ReleasedGlobal.shapeEquiv s).val i).val) ↔ _
  simp only [ReleasedRecursive.Asm.isZeroCell, not_or]
  constructor
  · intro h
    exact ⟨(h 0).ne', (h 1).ne', (h 2).ne'⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact Nat.pos_of_ne_zero h0
    · exact Nat.pos_of_ne_zero h1
    · exact Nat.pos_of_ne_zero h2

private theorem cellOf_owner (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k)
    (b : ReleasedRecursive.Asm.Blk k) (o : Fin 6) (ho : b.1 = o) :
    ReleasedRecursive.Asm.cellOf k a b = (a o).val 0 b.2 := by
  rcases b with ⟨owner, position⟩
  change owner = o at ho
  subst o
  rfl

private noncomputable def positiveFiberEquiv (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) (j : Fin 270)
    (hi : (ReleasedInterior.seed (ReleasedJointInterior.component j).1
      (ReleasedJointInterior.component j).2).boundary = []) :
    OwnerFiber k a j ≃
      {t : Fin (ReleasedGlobal.blocks k) //
        (a (ReleasedJointInterior.component j).1).val 0 t =
          ReleasedGlobal.shapeEquiv (ReleasedJointInterior.component j).2} where
  toFun b := ⟨b.val.val.2, by
    obtain ⟨ho, hc⟩ := (label_eq_iff k a b.val j).mp b.property
    exact (cellOf_owner k a b.val.val _ ho).symm.trans hc⟩
  invFun t := ⟨⟨⟨(ReleasedJointInterior.component j).1, t.val⟩, by
    change ¬ ReleasedRecursive.Asm.isZeroCell
      ((a (ReleasedJointInterior.component j).1).val 0 t.val)
    rw [t.property]
    exact (interior_iff _ _).mp hi⟩,
    (label_eq_iff k a _ j).mpr ⟨rfl, t.property⟩⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    have ho := ((label_eq_iff k a b.val j).mp b.property).1
    exact Sigma.ext ho.symm HEq.rfl
  right_inv t := by
    apply Subtype.ext
    rfl

private theorem fiber_card (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) (j : Fin 270) :
    Fintype.card (OwnerFiber k a j) = ownerBlocks k j := by
  by_cases hi : (ReleasedInterior.seed (ReleasedJointInterior.component j).1
      (ReleasedJointInterior.component j).2).boundary = []
  · rw [Fintype.card_congr (positiveFiberEquiv k a j hi),
      ReleasedRecursive.Asm.block_count]
    simp only [ReleasedGlobal.counts, ReleasedGlobal.coarseCounts,
      Equiv.symm_apply_apply, ownerBlocks, ReleasedJointInterior.weight, if_pos hi]
    exact (Nat.mul_assoc _ _ _).symm
  · have hzero : ReleasedRecursive.Asm.isZeroCell
        (ReleasedGlobal.shapeEquiv (ReleasedJointInterior.component j).2) := by
      by_contra h
      exact hi ((interior_iff _ _).mpr h)
    letI : IsEmpty (OwnerFiber k a j) := ⟨fun b => by
      apply b.val.property
      rw [((label_eq_iff k a b.val j).mp b.property).2]
      exact hzero⟩
    simp only [Fintype.card_eq_zero, ownerBlocks, ReleasedJointInterior.weight,
      if_neg hi, Nat.mul_zero, Nat.zero_mul]

private noncomputable def fiberEquiv (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) (j : Fin 270) :
    Fin (ownerBlocks k j) ≃ OwnerFiber k a j :=
  Fintype.equivOfCardEq ((Fintype.card_fin _).trans (fiber_card k a j).symm)

private theorem fiber_count {A I W : Type} [Fintype A]
    (f : A → I) (j : I) {n : ℕ} (e : Fin n ≃ {x : A // f x = j})
    (g : A → W) (w : W) :
    Fintype.card {t : Fin n // g (e t).val = w} =
      Fintype.card {x : A // f x = j ∧ g x = w} := by
  let d : {t : Fin n // g (e t).val = w} ≃
      {x : A // f x = j ∧ g x = w} := {
    toFun := fun t => ⟨(e t.val).val, (e t.val).property, t.property⟩
    invFun := fun x => ⟨e.symm ⟨x.val, x.property.1⟩, by
      simpa only [Equiv.apply_symm_apply] using x.property.2⟩
    left_inv := fun t => by
      apply Subtype.ext
      exact e.symm_apply_apply t.val
    right_inv := fun x => by
      apply Subtype.ext
      change (e (e.symm ⟨x.val, x.property.1⟩)).val = x.val
      exact congrArg (fun z : {a : A // f a = j} => z.val)
        (e.apply_symm_apply ⟨x.val, x.property.1⟩) }
  exact Fintype.card_congr d

private theorem hash_mode (o : Fin 6) (i : Fin 3) :
    ReleasedGlobal.hashMode o i = (ReleasedJointInterior.roleEquiv o).symm i :=
  (by decide +kernel : ∀ (o : Fin 6) (i : Fin 3),
    ReleasedGlobal.hashMode o i = (ReleasedJointInterior.roleEquiv o).symm i) o i

private noncomputable def selectedWord (k : ℕ) (j : Fin 270)
    (e : Fin (ownerBlocks k j * 2) ≃
      Position (fun r => ReleasedJointInterior.size r k j))
    (x : ∀ r : Fin 6, ProfiledCW.FineWord (ReleasedJointInterior.blocks r k * 4)) :
    ProfiledCW.FineWord (ownerBlocks k j * 4) := fun q =>
  let p := ReleasedJointInterior.ownerFineEmbedding k j e
    (show (ownerBlocks k j * 2) * 2 ^ (2 - 1) = ownerBlocks k j * 4
      from Nat.mul_assoc (ownerBlocks k j) 2 2) q
  x p.1 p.2

private def CellConclusion (k : ℕ) (j : Fin 270) (i : Fin 3) (eta : ℝ)
    (z : ProfiledCW.FineWord (ownerBlocks k j * 4)) : Prop :=
  (∀ p : Fin (ownerBlocks k j),
    CWCells.grade (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p) =
      ReleasedInterior.parent (ReleasedJointInterior.component j).2 0
        ((ReleasedJointInterior.roleEquiv (ReleasedJointInterior.component j).1).symm i)) ∧
  ∀ w : CompleteWord 3,
    |(Fintype.card {p : Fin (ownerBlocks k j) //
      ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p = w} : ℝ) /
      (ownerBlocks k j : ℝ) -
      ((((ReleasedGlobal.jointRows (ReleasedJointInterior.component j).1
        (ReleasedJointInterior.component j).2).map (fun p =>
        if ReleasedGlobal.atom p.1
          ((ReleasedJointInterior.roleEquiv (ReleasedJointInterior.component j).1).symm i)
          = w then p.2 else 0)).sum : ℕ) : ℝ) / (denominator : ℝ) ^ 4| ≤ eta

private def OwnerWindow (k : ℕ) (j : Fin 270)
    (e : Fin (ownerBlocks k j * 2) ≃
      Position (fun r => ReleasedJointInterior.size r k j)) : Prop :=
  ∀ (i : Fin 3)
    (x : ∀ r : Fin 6, ProfiledCW.FineWord (ReleasedJointInterior.blocks r k * 4))
    (eta : ℝ),
    (∀ r, ParentGraded (ReleasedJointInterior.parent r) (ReleasedJointInterior.size r k)
      ((ReleasedJointInterior.roleEquiv r).symm i)
      (ProfiledCW.split (ell := 2) (ReleasedJointInterior.positions r k)
        (ReleasedJointInterior.positions_length r k) (x r))) →
    (∀ r, ReleasedJointInterior.source r k eta
      ((ReleasedJointInterior.roleEquiv r).symm i) (x r)) →
    CellConclusion k j i eta (selectedWord k j e x)

private theorem owner_window (k : ℕ) (hk : 0 < k) (j : Fin 270)
    (hw : 0 < ReleasedJointInterior.weight j) :
    ∃ e : Fin (ownerBlocks k j * 2) ≃
      Position (fun r => ReleasedJointInterior.size r k j), OwnerWindow k j e := by
  have hi : (ReleasedInterior.seed (ReleasedJointInterior.component j).1
      (ReleasedJointInterior.component j).2).boundary = [] := by
    by_contra h
    simp only [ReleasedJointInterior.weight, if_neg h] at hw
    omega
  obtain ⟨e, he⟩ := mme_released_interior_scaled_parent_graded_fine_word_window
    (ReleasedJointInterior.component j).1 (ReleasedJointInterior.component j).2 hi
    (k * ReleasedJointInterior.weight j) (Nat.mul_pos hk hw)
  refine ⟨e, ?_⟩
  intro i x eta hg ht
  let f := fun r => ProfiledCW.split (ell := 2) (ReleasedJointInterior.positions r k)
    (ReleasedJointInterior.positions_length r k) (x r)
  have hm (r : Fin 6) :
      (ReleasedJointInterior.orientation (ReleasedJointInterior.component j).1 r).symm
        ((ReleasedJointInterior.roleEquiv (ReleasedJointInterior.component j).1).symm i) =
          (ReleasedJointInterior.roleEquiv r).symm i := by
    simp only [ReleasedJointInterior.orientation, Equiv.symm_trans_apply,
      Equiv.symm_symm, Equiv.apply_symm_apply]
  have hsplit : ProfiledCW.split e
      (show (ownerBlocks k j * 2) * 2 ^ (2 - 1) = ownerBlocks k j * 4
        from Nat.mul_assoc (ownerBlocks k j) 2 2) (selectedWord k j e x) =
      fun p => f p.1 ⟨j, p.2⟩ := by
    funext p
    exact mme_released_joint_interior_fine_selection k j e _ x p
  have hp : ParentGraded (ReleasedInterior.parent (ReleasedJointInterior.component j).2)
      (fun r => k * ReleasedJointInterior.weight j *
        ReleasedInterior.regionalSize (ReleasedJointInterior.component j).1
          (ReleasedJointInterior.component j).2 r)
      ((ReleasedJointInterior.roleEquiv (ReleasedJointInterior.component j).1).symm i)
      (fun p => f p.1 ⟨j, p.2⟩) := by
    intro r t
    have h := hg r j t
    simpa only [ReleasedJointInterior.parent, ReleasedJointInterior.orientation,
      Equiv.trans_apply, Equiv.apply_symm_apply] using h
  have ht' := mme_released_joint_interior_owner_parent_typical k j
    ((ReleasedJointInterior.roleEquiv (ReleasedJointInterior.component j).1).symm i)
    eta f (fun r => by rw [hm r]; exact ht r)
  have hc := he ((ReleasedJointInterior.roleEquiv (ReleasedJointInterior.component j).1).symm i)
    (selectedWord k j e x) eta (by rw [hsplit]; exact hp) (by rw [hsplit]; exact ht')
  simpa only [CellConclusion, ownerBlocks, CWCells.grade, Fintype.card_eq_nat_card] using hc

private theorem all_owner_windows (k : ℕ) (hk : 0 < k) :
    ∃ e : ∀ j : Fin 270, Fin (ownerBlocks k j * 2) ≃
      Position (fun r => ReleasedJointInterior.size r k j),
      ∀ j, 0 < ReleasedJointInterior.weight j → OwnerWindow k j (e j) := by
  have h (j : Fin 270) : ∃ e : Fin (ownerBlocks k j * 2) ≃
      Position (fun r => ReleasedJointInterior.size r k j),
      0 < ReleasedJointInterior.weight j → OwnerWindow k j e := by
    by_cases hw : 0 < ReleasedJointInterior.weight j
    · obtain ⟨e, he⟩ := owner_window k hk j hw
      exact ⟨e, fun _ => he⟩
    · have hc : Fintype.card (Fin (ownerBlocks k j * 2)) =
          Fintype.card (Position (fun r => ReleasedJointInterior.size r k j)) := by
        simp only [Fintype.card_fin, Fintype.card_sigma, Fintype.card_prod]
        rw [← Finset.sum_mul, mme_released_joint_interior_owner_mass]
      exact ⟨Fintype.equivOfCardEq hc, fun h => (hw h).elim⟩
  choose e he using h
  exact ⟨e, he⟩

private noncomputable def partFineEquiv (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) :
    ReleasedRecursive.Asm.PBlk k a × Fin 4 ≃
      Fin (ReleasedRecursive.Asm.partSize k a 1) :=
  ((ReleasedRecursive.Asm.pEnum k a).prodCongr (Equiv.refl (Fin 4))).trans
    (finProdFinEquiv.trans (finCongr (ReleasedRecursive.Asm.pLen k a)))

private noncomputable def actualFineEquiv (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) :
    (Σ j : Fin 270, Fin (ownerBlocks k j * 4)) ≃
      Fin (ReleasedRecursive.Asm.partSize k a 1) :=
  (Equiv.sigmaCongrRight (fun j =>
    (finProdFinEquiv : Fin (ownerBlocks k j) × Fin 4 ≃ _).symm)).trans
    ((Equiv.sigmaProdDistrib (fun j => Fin (ownerBlocks k j)) (Fin 4)).symm.trans
      ((((Equiv.sigmaCongrRight (fiberEquiv k a)).trans
        (Equiv.sigmaFiberEquiv (ownerLabel k a))).prodCongr
          (Equiv.refl (Fin 4))).trans (partFineEquiv k a)))

private theorem actualFine_apply (k : ℕ)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) (j : Fin 270)
    (p : Fin (ownerBlocks k j)) (r : Fin 4) :
    actualFineEquiv k a ⟨j, finProdFinEquiv (p, r)⟩ =
      partFineEquiv k a ((fiberEquiv k a j p).val, r) := by
  simp only [actualFineEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.symm_apply_apply]
  rfl

private theorem normalized_bound (k alpha D H R : ℕ)
    (hk : 0 < k) (ha : 0 < alpha) (hD : 0 < D) (haD : alpha ≤ D)
    (eta : ℝ) (heta : 0 ≤ eta)
    (h : |(H : ℝ) / (k * alpha * D ^ 4 : ℕ) - (R : ℝ) / (D : ℝ) ^ 4| ≤ eta) :
    |(H : ℝ) / (D ^ 5 * k : ℕ) - (alpha * R : ℕ) / (D : ℝ) ^ 5| ≤ eta := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have ha' : (alpha : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hnonneg : 0 ≤ (alpha : ℝ) / D := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hle : (alpha : ℝ) / D ≤ 1 :=
    (div_le_one (by exact_mod_cast hD : (0 : ℝ) < D)).mpr (by exact_mod_cast haD)
  have hid : (H : ℝ) / (D ^ 5 * k : ℕ) - (alpha * R : ℕ) / (D : ℝ) ^ 5 =
      ((alpha : ℝ) / D) *
        ((H : ℝ) / (k * alpha * D ^ 4 : ℕ) - (R : ℝ) / (D : ℝ) ^ 4) := by
    push_cast
    field_simp [hk', ha', hD']
    <;> ring
  rw [hid, abs_mul, abs_of_nonneg hnonneg]
  exact (mul_le_mul_of_nonneg_left h hnonneg).trans (mul_le_of_le_one_left heta hle)

private theorem cell_global_bound (k : ℕ) (hk : 0 < k) (j : Fin 270)
    (hi : (ReleasedInterior.seed (ReleasedJointInterior.component j).1
      (ReleasedJointInterior.component j).2).boundary = [])
    (i : Fin 3) (w : CompleteWord 3) (H : ℕ) (eta : ℝ) (heta : 0 ≤ eta)
    (hz : ReleasedJointInterior.weight j = 0 → H = 0)
    (hb : 0 < ReleasedJointInterior.weight j →
      |(H : ℝ) / (ownerBlocks k j : ℝ) -
        ((((ReleasedGlobal.jointRows (ReleasedJointInterior.component j).1
          (ReleasedJointInterior.component j).2).map (fun p =>
            if ReleasedGlobal.atom p.1
              ((ReleasedJointInterior.roleEquiv (ReleasedJointInterior.component j).1).symm i)
              = w then p.2 else 0)).sum : ℕ) : ℝ) / (denominator : ℝ) ^ 4| ≤ eta) :
    |(H : ℝ) / (ReleasedGlobal.blocks k : ℝ) -
      (ReleasedGlobal.profile (ReleasedJointInterior.component j).1).2
        (ReleasedGlobal.hashMode (ReleasedJointInterior.component j).1 i)
        (ReleasedRecursive.Asm.cellOfShape
          (ReleasedGlobal.shapeEquiv (ReleasedJointInterior.component j).2)) w| ≤ eta := by
  have hw : ReleasedJointInterior.weight j = ReleasedGlobal.alpha
      (ReleasedJointInterior.component j).1 (ReleasedJointInterior.component j).2 := by
    simp only [ReleasedJointInterior.weight, if_pos hi]
  change |(H : ℝ) / (denominator ^ 5 * k : ℕ) -
    (ReleasedGlobal.wordCounts (ReleasedJointInterior.component j).1
      (ReleasedGlobal.hashMode (ReleasedJointInterior.component j).1 i)
      (ReleasedGlobal.shapeEquiv (ReleasedJointInterior.component j).2) w : ℝ) /
        (denominator : ℝ) ^ 5| ≤ eta
  rw [mme_released_global_word_counts_row_marginal, Equiv.symm_apply_apply, hash_mode]
  by_cases ha : ReleasedGlobal.alpha (ReleasedJointInterior.component j).1
      (ReleasedJointInterior.component j).2 = 0
  · rw [hz (hw.trans ha), ha]
    simpa only [Nat.zero_mul, Nat.cast_zero, zero_div, sub_zero, abs_zero] using heta
  · have haD : ReleasedGlobal.alpha (ReleasedJointInterior.component j).1
        (ReleasedJointInterior.component j).2 ≤ denominator := by
      calc
        _ ≤ ∑ s : Fin 45, ReleasedGlobal.alpha (ReleasedJointInterior.component j).1 s :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        _ = denominator := mme_released_global_joint_counts_valid.1 _
    apply normalized_bound _ _ _ _ _ hk (Nat.pos_of_ne_zero ha)
      (by norm_num [denominator]) haD eta heta
    simpa only [ownerBlocks, hw] using hb (by rw [hw]; exact Nat.pos_of_ne_zero ha)

end JointPositiveSource

open JointPositiveSource

/-- The common parent-graded sources lie inside the positive part of every
global reference after one position permutation, fixed for all tolerances
and words. Empty owner/shape fibers are retained. -/
theorem solution (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) :
    ∃ E : (Σ r : Fin 6, Fin (ReleasedJointInterior.blocks r k * 4)) ≃
        Fin (ReleasedRecursive.Asm.partSize k a 1),
      ∀ (eta : ℝ), 0 < eta →
        ∀ (eps : Fin 6 → ℝ), (∀ o, eta ≤ eps o) →
          ∀ (i : Fin 3)
            (y : ProfiledCW.FineWord (ReleasedRecursive.Asm.partSize k a 1)),
            (∀ r,
              ParentGraded (ReleasedJointInterior.parent r) (ReleasedJointInterior.size r k)
                ((ReleasedJointInterior.roleEquiv r).symm i)
                (ProfiledCW.split (ell := 2) (ReleasedJointInterior.positions r k)
                  (ReleasedJointInterior.positions_length r k) (fun q => y (E ⟨r, q⟩))) ∧
              ReleasedJointInterior.source r k eta
                ((ReleasedJointInterior.roleEquiv r).symm i) (fun q => y (E ⟨r, q⟩))) →
              ReleasedRecursive.Asm.QPos k a eps i y := by
  obtain ⟨e, he⟩ := all_owner_windows k hk
  obtain ⟨U, hU⟩ := mme_released_joint_interior_owner_fine_partition k
    (fun j => ownerBlocks k j * 2) (fun j => ownerBlocks k j * 4) e
    (fun j => Nat.mul_assoc (ownerBlocks k j) 2 2)
  let E := U.symm.trans (actualFineEquiv k a)
  refine ⟨E, ?_⟩
  intro eta heta eps heps i y hs
  let x := fun r q => y (E ⟨r, q⟩)
  have hword (j : Fin 270) (p : Fin (ownerBlocks k j)) :
      ProfiledCW.split (ell := 3) (Equiv.refl _) rfl (selectedWord k j (e j) x) p =
        ReleasedRecursive.Asm.pBlockWord k a y (fiberEquiv k a j p).val := by
    funext r
    change y (E (ReleasedJointInterior.ownerFineEmbedding k j (e j)
      (Nat.mul_assoc (ownerBlocks k j) 2 2) (finProdFinEquiv (p, r)))) = _
    rw [← hU j (finProdFinEquiv (p, r))]
    change y (actualFineEquiv k a (U.symm (U ⟨j, finProdFinEquiv (p, r)⟩))) = _
    rw [Equiv.symm_apply_apply, actualFine_apply]
    rfl
  have hcell (j : Fin 270) (hw : 0 < ReleasedJointInterior.weight j) :
      CellConclusion k j i eta (selectedWord k j (e j) x) :=
    he j hw i x eta (fun r => (hs r).1) (fun r => (hs r).2)
  have hcount (j : Fin 270) (w : CompleteWord 3) :
      Fintype.card {p : Fin (ownerBlocks k j) //
        ProfiledCW.split (ell := 3) (Equiv.refl _) rfl (selectedWord k j (e j) x) p = w} =
      Fintype.card {b : ReleasedRecursive.Asm.PBlk k a //
        ownerLabel k a b = j ∧ ReleasedRecursive.Asm.pBlockWord k a y b = w} := by
    simp only [hword]
    simpa only [Fintype.card_eq_nat_card] using
      fiber_count (ownerLabel k a) j (fiberEquiv k a j)
        (ReleasedRecursive.Asm.pBlockWord k a y) w
  constructor
  · intro b
    let j := ownerLabel k a b
    let p := (fiberEquiv k a j).symm ⟨b, rfl⟩
    have hp : (fiberEquiv k a j p).val = b :=
      congrArg Subtype.val ((fiberEquiv k a j).apply_symm_apply ⟨b, rfl⟩)
    have hw : 0 < ReleasedJointInterior.weight j := by
      by_contra h
      have hz : ReleasedJointInterior.weight j = 0 := Nat.eq_zero_of_not_pos h
      have ht := p.isLt
      simp only [ownerBlocks, hz, Nat.mul_zero, Nat.zero_mul] at ht
      omega
    have hg := (hcell j hw).1 p
    rw [hword, hp] at hg
    have hj := (label_eq_iff k a b j).mp rfl
    change CWCells.grade (ReleasedRecursive.Asm.pBlockWord k a y b) =
      ((ReleasedGlobal.shapeEquiv (ReleasedJointInterior.component j).2).val
        ((ReleasedJointInterior.roleEquiv (ReleasedJointInterior.component j).1).symm i)).val at hg
    rw [← hash_mode, ← hj.1, ← hj.2] at hg
    exact hg
  · intro o c hc w
    let j : Fin 270 := finProdFinEquiv (o, ReleasedGlobal.shapeEquiv.symm c)
    have ho : (ReleasedJointInterior.component j).1 = o := by
      simp only [ReleasedJointInterior.component, j, Equiv.symm_apply_apply]
    have hshape : ReleasedGlobal.shapeEquiv (ReleasedJointInterior.component j).2 = c := by
      simp only [ReleasedJointInterior.component, j, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply]
    have hi : (ReleasedInterior.seed (ReleasedJointInterior.component j).1
        (ReleasedJointInterior.component j).2).boundary = [] :=
      (interior_iff _ _).mpr (by rw [hshape]; exact hc)
    have hb := cell_global_bound k hk j hi i w
      (Fintype.card {b : ReleasedRecursive.Asm.PBlk k a //
        ownerLabel k a b = j ∧ ReleasedRecursive.Asm.pBlockWord k a y b = w}) eta
      (le_of_lt heta) (fun hz => by
        rw [← hcount j w]
        letI : IsEmpty (Fin (ownerBlocks k j)) := ⟨fun p => by
          have hp : p.val < 0 := by
            simpa only [ownerBlocks, hz, Nat.mul_zero, Nat.zero_mul] using p.isLt
          exact Nat.not_lt_zero _ hp⟩
        exact Fintype.card_eq_zero) (fun hw => by
        rw [← hcount j w]
        exact (hcell j hw).2 w)
    rw [ho, hshape] at hb
    have hcounts : Fintype.card {b : ReleasedRecursive.Asm.PBlk k a //
        ownerLabel k a b = j ∧ ReleasedRecursive.Asm.pBlockWord k a y b = w} =
      Fintype.card {b : ReleasedRecursive.Asm.PBlk k a //
        b.val.1 = o ∧ (a o).val 0 b.val.2 = c ∧
          ReleasedRecursive.Asm.pBlockWord k a y b = w} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro b
      rw [label_eq_iff, ho, hshape]
      constructor
      · rintro ⟨⟨hbo, hbc⟩, hw⟩
        exact ⟨hbo, (cellOf_owner k a b.val o hbo).symm.trans hbc, hw⟩
      · rintro ⟨hbo, hbc, hw⟩
        exact ⟨⟨hbo, (cellOf_owner k a b.val o hbo).trans hbc⟩, hw⟩
    rw [hcounts] at hb
    exact hb.trans (heps o)

#print axioms solution
