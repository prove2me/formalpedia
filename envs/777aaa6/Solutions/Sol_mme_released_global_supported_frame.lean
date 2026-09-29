-- Prove2me | solution 1 for mme_released_global_supported_frame
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:30:58.740149+00:00
-- url     : https://prove2.me/submissions/74bcd8d7-f4d3-4f5f-88e4-2ccac4478d17

import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_released_global_profile_count_identities
import Theorems.Thm_mme_released_global_profile_normalization
import Theorems.Thm_mme_recursive_region_target_nonempty
import Theorems.Thm_mme_recursive_CW_supported_words_of_joint_histogram
import Theorems.Thm_mme_global_CW_supported_histogram_admissibility
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RecursiveYZ MME.ProfiledCW
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
set_option maxHeartbeats 2400000

private theorem cell_fiber {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (a : RecursiveXHash.Address degree R bounds n) (r : Fin R)
    (c : RecursiveThinSplit.Split degree (bounds r)) :
    Fintype.card {p : Place n // cell a p = ⟨r,c⟩} = RecursiveThinSplit.count (a r) c := by
  classical
  let e : {p : Place n // cell a p = ⟨r,c⟩} ≃ {t : Fin (n r) // a r t = c} := {
    toFun := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨t, eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun t ↦ ⟨⟨r,t.val⟩, by change (⟨r,_⟩ : Cell degree R bounds) = ⟨r,c⟩; rw [t.property]⟩
    left_inv := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro t; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  rfl

attribute [local irreducible] jointRows alpha atom rowCounts jointCounts coarseCounts wordCounts shapeEquiv

theorem solution (owner : Fin 6) (k : ℕ) (hk : 0 < k) :
    ∃ a : Reference owner k,
      (frame owner k hk a).Admissible (scaledWords owner k) ∧
      ∀ eps : ℝ, 0 ≤ eps →
      ∃ x : Fin 3 → FineWord (4*blocks k), supported x ∧
        ∀ i, (frame owner k hk a).window (windowGood owner k eps) i (x i) := by
  classical
  have hv := mme_released_global_profile_count_identities owner
  have hm : ∀ r : Fin 1, ∑ c : Shape, counts owner k r c = blocks k := by
    intro r
    simp only [counts,← Finset.mul_sum,hv.1,blocks,mul_comm]
  obtain ⟨ref,href⟩ := mme_recursive_region_target_nonempty (fun (_ : Fin 1) (_ : Fin 3) ↦ 8)
    (fun _ ↦ blocks k) (counts owner k) hm
  let a : Reference owner k := ⟨ref,href⟩
  let D := frame owner k hk a
  have hmass : ∀ c : Cell 8 1 (fun _ _ ↦ 8),
      ∑ v : JointWord, k*jointCounts owner c.2 v =
        Nat.card {p : Place (fun _ : Fin 1 ↦ blocks k) // cell ref p = c} := by
    intro c
    rw [← Finset.mul_sum,hv.2.1 c.2]
    have hc := cell_fiber ref c.1 c.2
    have hj := (Finset.mem_filter.mp href).2 c.1 c.2
    simpa only [Fintype.card_eq_nat_card,hj,counts] using hc.symm
  have hmargin : ∀ i (c : Cell 8 1 (fun _ _ ↦ 8)) w,
      ∑ v : JointWord, (if v i = w then k*jointCounts owner c.2 v else 0) =
        scaledWords owner k i c w := by
    intro i c w
    simp only [scaledWords,wordCounts,Finset.mul_sum,mul_ite,mul_zero]
  have hgrade : ∀ (c : Cell 8 1 (fun _ _ ↦ 8)) v, 0 < k*jointCounts owner c.2 v →
      ∀ i, CWCells.grade (v i) = (c.2.val i).val := by
    intro c v h
    exact (hv.2.2.1 c.2 v (Nat.pos_of_mul_pos_left h)).1
  have hsupport : ∀ (c : Cell 8 1 (fun _ _ ↦ 8)) v, 0 < k*jointCounts owner c.2 v →
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2 := by
    intro c v h
    exact (hv.2.2.1 c.2 v (Nat.pos_of_mul_pos_left h)).2
  obtain ⟨w,hg,hw,hs,_⟩ := mme_recursive_CW_supported_words_of_joint_histogram
    (ell := 3) (cell ref) (fun c i ↦ (c.2.val i).val) (scaledWords owner k)
    (fun c v ↦ k*jointCounts owner c.2 v) hmass hmargin hgrade hsupport
  have hh := mme_global_CW_supported_histogram_admissibility D w hg hs
  have hmu : (fun i ↦ count (cell ref) (w i)) = scaledWords owner k :=
    funext fun i ↦ funext fun c ↦ funext fun u ↦ hw i c u
  change D.Admissible (fun i ↦ count (cell ref) (w i)) at hh
  have hh' : D.Admissible (scaledWords owner k) := (congrArg D.Admissible hmu).mp hh
  refine ⟨a,hh',?_⟩
  intro eps heps
  let x : Fin 3 → FineWord (4*blocks k) := fun i ↦ flatten D.positions D.length (w i)
  have hx : ∀ i, split D.positions D.length (x i) = w i := by
    intro i
    funext p r
    simp [x,split,flatten]
  have hnorm := (mme_released_global_profile_normalization owner).2.2.2.2.2
  have hb : (0 : ℝ) < (blocks k : ℕ) := by
    have hbn : 0 < blocks k := by unfold blocks denominator; positivity
    exact_mod_cast hbn
  refine ⟨x,?_,?_⟩
  · intro t
    exact hs (D.positions (finProdFinEquiv.symm (Fin.cast D.length.symm t)).1)
      (finProdFinEquiv.symm (Fin.cast D.length.symm t)).2
  · intro i
    change GlobalCW.Graded i ref (split D.positions D.length (x i)) ∧
      windowGood owner k eps i (count (cell ref) (split D.positions D.length (x i)))
    rw [hx i]
    refine ⟨hg i,?_⟩
    intro c u
    rw [hw i c u]
    change |(scaledWords owner k i c u : ℝ)/(blocks k : ℝ) - (profile owner).2 i c u| ≤ eps
    rw [hnorm k i c u]
    have heq : (blocks k : ℝ)*(profile owner).2 i c u/(blocks k : ℝ) =
        (profile owner).2 i c u := mul_div_cancel_left₀ _ (ne_of_gt hb)
    rw [heq,sub_self,abs_zero]
    exact heps
