-- Prove2me | solution 1 for mme_released_positive_frame_supported_child_words
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T03:01:52.989119+00:00
-- url     : https://prove2.me/submissions/01b72c36-12a8-4406-8f83-b485972e6a76

import Definitions.Def_mme_released_positive_integer_frame_data
import Theorems.Thm_mme_recursive_CW_supported_words_of_joint_histogram
import Theorems.Thm_mme_released_positive_region0_profile_reindex
import Theorems.Thm_mme_released_positive_region1_profile_reindex
import Theorems.Thm_mme_released_positive_region2_profile_reindex
import Theorems.Thm_mme_released_positive_region3_profile_reindex
import Theorems.Thm_mme_released_positive_region4_profile_reindex
import Theorems.Thm_mme_released_positive_region5_profile_reindex
import Mathlib

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit MME.RegionRealization
  MME.ProfiledCW MME.RecursiveYZ.CWCells MME.ReleasedPositiveInteger
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace PositiveChildNonempty

noncomputable def jointFrom {W : Type*} [DecidableEq W] (entries : List (ℕ × ℕ))
    (word : ℕ → Fin 3 → W) (v : Fin 3 → W) : ℕ := by
  classical
  exact (entries.map fun p => if word p.1 = v then p.2 else 0).sum

private theorem single_marginal {W : Type*} [Fintype W] [DecidableEq W]
    (v : Fin 3 → W) (weight : ℕ) (i : Fin 3) (w : W) :
    (∑ u : Fin 3 → W, if u i = w then (if v = u then weight else 0) else 0) =
      if v i = w then weight else 0 := by
  classical
  rw [Finset.sum_eq_single v]
  · simp
  · intro u _ h
    simp [Ne.symm h]
  · simp

private theorem if_add_zero (p : Prop) [Decidable p] (a b : ℕ) :
    (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) := by
  split_ifs <;> simp

private theorem if_mul_zero (p : Prop) [Decidable p] (a b : ℕ) :
    (if p then a * b else 0) = a * (if p then b else 0) := by
  split_ifs <;> simp

private theorem jointFrom_marginal {W : Type*} [Fintype W] [DecidableEq W]
    (entries : List (ℕ × ℕ)) (word : ℕ → Fin 3 → W) (i : Fin 3) (w : W) :
    (∑ v, if v i = w then jointFrom entries word v else 0) =
      (entries.map fun p => if word p.1 i = w then p.2 else 0).sum := by
  classical
  induction entries with
  | nil => simp [jointFrom]
  | cons p entries ih =>
    simp only [jointFrom, List.map_cons, List.sum_cons] at ih ⊢
    simp_rw [if_add_zero]
    rw [Finset.sum_add_distrib, single_marginal, ih]

private theorem jointFrom_support {W : Type*} [DecidableEq W] (entries : List (ℕ × ℕ))
    (word : ℕ → Fin 3 → W) (predicate : (Fin 3 → W) → Prop)
    (support : ∀ a, predicate (word a)) (v : Fin 3 → W)
    (positive : 0 < jointFrom entries word v) : predicate v := by
  classical
  induction entries with
  | nil => simp [jointFrom] at positive
  | cons p entries ih =>
    by_cases same : word p.1 = v
    · exact same ▸ support p.1
    · simp only [jointFrom, List.map_cons, List.sum_cons, same, if_false, zero_add] at positive
      exact ih positive

private theorem marginal_positive {W : Type*} [Fintype W] [DecidableEq W]
    (joint : (Fin 3 → W) → ℕ) (v : Fin 3 → W) (i : Fin 3)
    (positive : 0 < joint v) :
    0 < ∑ u, if u i = v i then joint u else 0 := by
  classical
  have bound := Finset.single_le_sum
    (fun u (_ : u ∈ (Finset.univ : Finset (Fin 3 → W))) =>
      Nat.zero_le (if u i = v i then joint u else 0)) (Finset.mem_univ v)
  exact positive.trans_le (by simpa only [if_pos rfl] using bound)

private theorem joint_mass_from_marginal {W : Type*} [Fintype W] [DecidableEq W]
    (joint : (Fin 3 → W) → ℕ) (mu : W → ℕ) (i : Fin 3)
    (marginal : ∀ w, ∑ v, (if v i = w then joint v else 0) = mu w) :
    ∑ v, joint v = ∑ w, mu w := by
  classical
  calc
    _ = ∑ w, ∑ v, if v i = w then joint v else 0 := by
      rw [Finset.sum_comm]
      simp
    _ = ∑ w, mu w := Finset.sum_congr rfl fun w _ => marginal w

private theorem elementary_support (a : Fin 6) :
    ∑ i : Fin 3, (ReleasedGlobal.elementary a i).val = 2 := by
  fin_cases a <;> decide +kernel

private theorem oriented_child_support (owner : Fin 6) (orientation : Equiv.Perm (Fin 3))
    (a : ℕ) (h : Fin (2 ^ (2 - 1))) :
    (ReleasedInterior.childWord owner a (orientation 0) h).val +
      (ReleasedInterior.childWord owner a (orientation 1) h).val +
      (ReleasedInterior.childWord owner a (orientation 2) h).val = 2 := by
  let atom : Fin 6 := ⟨a / 6 ^ h.val % 6, Nat.mod_lt _ (by decide)⟩
  have perm := (orientation.trans (ReleasedJointInterior.roleEquiv owner)).sum_comp
    (fun i => (ReleasedGlobal.elementary atom i).val)
  have total := elementary_support atom
  simpa only [Fin.sum_univ_three] using perm.trans total

noncomputable def commonEntries (region : Fin 6)
    (c : Cell 4 270 (ReleasedJointInterior.parent region)) : List (ℕ × ℕ) :=
  ReleasedInterior.child
    (ReleasedInterior.seed (ReleasedJointInterior.component c.1).1
      (ReleasedJointInterior.component c.1).2) region.val
    (ReleasedInterior.sourceShape (ReleasedJointInterior.component c.1).1
      ((ReleasedJointInterior.splitEquiv region c.1).symm c.2))

noncomputable def commonFactor (region : Fin 6) (k : ℕ)
    (c : Cell 4 270 (ReleasedJointInterior.parent region)) : ℕ :=
  k * ReleasedJointInterior.weight c.1 *
    ((ReleasedInterior.seed (ReleasedJointInterior.component c.1).1
      (ReleasedJointInterior.component c.1).2).region.getD region.val 0 *
    (ReleasedInterior.splitWeight (ReleasedJointInterior.component c.1).1
      (ReleasedJointInterior.component c.1).2 region
      ((ReleasedJointInterior.splitEquiv region c.1).symm c.2) +
    ReleasedInterior.splitWeight (ReleasedJointInterior.component c.1).1
      (ReleasedJointInterior.component c.1).2 region
      (complement (ReleasedInterior.parent_total (ReleasedJointInterior.component c.1).2 region)
        ((ReleasedJointInterior.splitEquiv region c.1).symm c.2))) *
    MoreAsymmetryExactSeed.denominator)

noncomputable def commonWords (region : Fin 6)
    (c : Cell 4 270 (ReleasedJointInterior.parent region)) (a : ℕ) : Fin 3 → CompleteWord 2 :=
  fun i => ReleasedInterior.childWord (ReleasedJointInterior.component c.1).1 a
    (ReleasedJointInterior.orientation (ReleasedJointInterior.component c.1).1 region i)

noncomputable def commonJoint (region : Fin 6) (k : ℕ)
    (c : Cell 4 270 (ReleasedJointInterior.parent region))
    (v : Fin 3 → CompleteWord 2) : ℕ :=
  commonFactor region k c * jointFrom (commonEntries region c) (commonWords region c) v

private theorem commonJoint_marginal (region : Fin 6) (k : ℕ) (i : Fin 3)
    (c : Cell 4 270 (ReleasedJointInterior.parent region)) (w : CompleteWord 2) :
    (∑ v, if v i = w then commonJoint region k c v else 0) =
      ReleasedJointInterior.integerProfile region k i c w := by
  classical
  simp only [commonJoint, if_mul_zero, ← Finset.mul_sum]
  rw [jointFrom_marginal]
  simp only [commonFactor, commonEntries, commonWords, ReleasedJointInterior.integerProfile,
    ReleasedInterior.integerProfile, ReleasedInterior.childMarginal]
  ring

private theorem commonJoint_support (region : Fin 6) (k : ℕ)
    (c : Cell 4 270 (ReleasedJointInterior.parent region)) (v : Fin 3 → CompleteWord 2)
    (positive : 0 < commonJoint region k c v) :
    ∀ h, (v 0 h).val + (v 1 h).val + (v 2 h).val = 2 := by
  have pos : 0 < jointFrom (commonEntries region c) (commonWords region c) v := by
    apply Nat.pos_of_ne_zero
    intro zero
    simp [commonJoint, zero] at positive
  apply jointFrom_support (commonEntries region c) (commonWords region c) _ _ v pos
  intro a h
  exact oriented_child_support (ReleasedJointInterior.component c.1).1
    (ReleasedJointInterior.orientation (ReleasedJointInterior.component c.1).1 region) a h

/- The fiber-count argument is copied verbatim from raresbuhai's accepted
proof p2m:solution/50983a64-7873-4293-b499-5e40f94a5eef of
p2m:theorem/42ce2054-4a77-4ab8-872d-5d87385fc333. Its statement is local here;
no private declaration from the imported submission is assumed accessible. -/
private theorem full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (r : Fin R)
    (c : MME.RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r,c⟩} =
      MME.RecursiveThinSplit.count (a r) c +
      MME.RecursiveThinSplit.count (a r) (complement (htotal r) c) := by
  classical
  let e : {p : Position n // fullCell htotal a p = ⟨r,c⟩} ≃
      {p : Fin (n r) × Fin 2 //
        (if p.2 = 0 then a r p.1 else complement (htotal r) (a r p.1)) = c} := {
    toFun := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨(t,h), eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun p ↦ ⟨⟨r,p.val⟩, by
      change (⟨r,_⟩ : Cell half R parent) = ⟨r,c⟩
      rw [p.property]⟩
    left_inv := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have hc (t : Fin (n r)) : complement (htotal r) (a r t) = c ↔
      a r t = complement (htotal r) c := by
    constructor
    · intro h
      simpa only [complement_complement] using congrArg (complement (htotal r)) h
    · intro h
      rw [h, complement_complement]
  simp only [show (1 : Fin 2) ≠ 0 by decide, 
    MME.RecursiveThinSplit.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_add_distrib]
  simp only [ite_true, ite_false, hc]
  congr 1

private theorem realize_frame {half ell R M B L : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half}
    {m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ}
    {mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ}
    {length : L * 2 ^ (ell - 1) = M} {minimum : ℕ}
    {grading : Predicate M} {source : ℝ → Predicate M}
    (frame : FrameData (B := B) parent n total m mu length minimum grading source)
    (coupling : ∃ joint : Cell half R parent → (Fin 3 → CompleteWord ell) → ℕ,
      (∀ i c w, ∑ v, (if v i = w then joint c v else 0) = mu i c w) ∧
      (∀ c v, 0 < joint c v → ∀ h,
        (v 0 h).val + (v 1 h).val + (v 2 h).val = 2)) :
    ∃ x : Fin 3 → FineWord M,
      supported x ∧ ∀ i,
        Graded total i frame.reference (split frame.positions length (x i)) ∧
        Useful (fullCell total frame.reference) (mu i) (split frame.positions length (x i)) := by
  classical
  obtain ⟨joint, marginal, joint_support⟩ := coupling
  have cell_mass : ∀ c, ∑ v, joint c v =
      Nat.card {p : Position n // fullCell total frame.reference p = c} := by
    intro c
    rw [joint_mass_from_marginal (joint c) (mu 0 c) 0 (marginal 0 c), frame.mass]
    have ref_counts : ∀ r s, RecursiveThinSplit.count (frame.reference r) s = m r s :=
      (Finset.mem_filter.mp frame.reference_target).2
    have card := full_cell_fiber total frame.reference c.1 c.2
    rw [ref_counts, ref_counts] at card
    simpa only [Nat.card_eq_fintype_card] using card.symm
  have cell_grade : ∀ c v, 0 < joint c v → ∀ i,
      grade (v i) = (c.2.val i).val := by
    intro c v positive i
    have pos := marginal_positive (joint c) v i positive
    rw [marginal] at pos
    exact frame.support i c (v i) pos
  obtain ⟨words, grades, counts, support, _⟩ :=
    mme_recursive_CW_supported_words_of_joint_histogram
      (fullCell total frame.reference) (fun c i => (c.2.val i).val)
      mu joint cell_mass marginal cell_grade joint_support
  let x : Fin 3 → FineWord M := fun i => flatten frame.positions length (words i)
  have unflatten (i : Fin 3) : split frame.positions length (x i) = words i := by
    funext p h
    simp [x, split, flatten]
  refine ⟨x, ?_, ?_⟩
  · intro q
    exact support (frame.positions (finProdFinEquiv.symm (Fin.cast length.symm q)).1)
      (finProdFinEquiv.symm (Fin.cast length.symm q)).2
  · intro i
    rw [unflatten]
    exact ⟨grades i, counts i⟩

private theorem profile_counts (region : Fin 6) :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size region 1 j})
      (hp : ∀ r, RecStage.parent3 region r = ReleasedJointInterior.parent region (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size region k (e r).val = k * RecStage.n3 region r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 region r)),
          ReleasedJointInterior.splitCount region k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hp r)) c) =
              k * RecStage.m3 region r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 region r)) (w : CompleteWord 2),
          ReleasedJointInterior.integerProfile region k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hp r)) c⟩ w =
              k * RecStage.mu3 region i ⟨r,c⟩ w) := by
  fin_cases region
  · exact mme_released_positive_region0_profile_reindex
  · exact mme_released_positive_region1_profile_reindex
  · exact mme_released_positive_region2_profile_reindex
  · exact mme_released_positive_region3_profile_reindex
  · exact mme_released_positive_region4_profile_reindex
  · exact mme_released_positive_region5_profile_reindex

private theorem compact_coupling (region : Fin 6) (k : ℕ) :
    ∃ joint : Cell 4 88 (RecStage.parent3 region) → (Fin 3 → CompleteWord 2) → ℕ,
      (∀ i c w, ∑ v, (if v i = w then joint c v else 0) = k * RecStage.mu3 region i c w) ∧
      (∀ c v, 0 < joint c v → ∀ h,
        (v 0 h).val + (v 1 h).val + (v 2 h).val = 2) := by
  classical
  obtain ⟨e, hp, counts⟩ := profile_counts region
  let select : Cell 4 88 (RecStage.parent3 region) →
      Cell 4 270 (ReleasedJointInterior.parent region) :=
    fun c => ⟨(e c.1).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hp c.1)) c.2⟩
  refine ⟨fun c v => commonJoint region k (select c) v, ?_, ?_⟩
  · intro i c w
    rw [commonJoint_marginal]
    exact (counts k).2.2 i c.1 c.2 w
  · intro c v positive
    exact commonJoint_support region k (select c) v positive

end PositiveChildNonempty

/-- Every positive integer frame has an exact jointly supported central child histogram. -/
theorem solution (region : Fin 6) (k : ℕ) (frame : Frame region k) :
    ∃ x : Fin 3 → FineWord (ReleasedJointInterior.blocks region k * 4),
      supported x ∧ ∀ i,
        Graded (RecStage.htotal3 region) i frame.reference
          (split (ell := 2) frame.positions (ReleasedJointInterior.positions_length region k) (x i)) ∧
        Useful (fullCell (RecStage.htotal3 region) frame.reference)
          (fun c w => k * RecStage.mu3 region i c w)
          (split (ell := 2) frame.positions (ReleasedJointInterior.positions_length region k) (x i)) := by
  exact PositiveChildNonempty.realize_frame frame (PositiveChildNonempty.compact_coupling region k)

#print axioms solution
