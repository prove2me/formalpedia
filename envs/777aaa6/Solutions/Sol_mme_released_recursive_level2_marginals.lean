-- Prove2me | solution 1 for mme_released_recursive_level2_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T22:08:25.470424+00:00
-- url     : https://prove2.me/submissions/b15db355-66be-4f91-933f-84549689120f

import Mathlib
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_bridge_data
import Theorems.Thm_mme_released_recursive_stage_structure_valid
import Theorems.Thm_mme_released_recursive_level2_shapes
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace MME.L2Cert

/-- A sum over admissible splits is a filtered sum over all grade triples. -/
theorem split_sum_expand {half : ℕ} {parent : Fin 3 → ℕ} (g : (Fin 3 → Fin (half + 1)) → ℚ) :
    ∑ c : RecursiveThinSplit.Split half parent, g c.val =
      ∑ a : Fin 3 → Fin (half + 1),
        if (a 0).val + (a 1).val + (a 2).val = half ∧ ∀ i, (a i).val ≤ parent i then g a else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine (Finset.sum_subtype _ (fun a ↦ ?_) g).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- At level two a cell frequency is the indicator of the cell's grade. -/
theorem freq_l2 (i : Fin 3) (r : Fin 1104)
    (e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r))
    (v : CompleteSplit.CompleteWord 1) :
    freqQ (mu2 i) ⟨r, e⟩ v =
      if (v 0).val = (e.val i).val ∧ m2 r e + m2 r (complement (htotal2 r) e) ≠ 0 then 1 else 0 := by
  classical
  have hmass := mme_released_recursive_stage_structure_valid.2.1 i (⟨r, e⟩ :
    Cell (2 * 2 ^ (1 - 1)) 1104 parent2)
  unfold freqQ
  rw [hmass]
  show ((mu2 i ⟨r, e⟩ v : ℚ)) / ((m2 r e + m2 r (complement (htotal2 r) e) : ℕ) : ℚ) = _
  by_cases hz : m2 r e + m2 r (complement (htotal2 r) e) = 0
  · rw [hz]
    simp only [Nat.cast_zero, div_zero, ne_eq, not_true_eq_false, and_false, if_false]
  · have hzq : ((m2 r e + m2 r (complement (htotal2 r) e) : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast hz
    by_cases hv : (v 0).val = (e.val i).val
    · rw [if_pos ⟨hv, hz⟩]
      show ((mu2 i ⟨r, e⟩ v : ℕ) : ℚ) / _ = 1
      rw [show mu2 i ⟨r, e⟩ v = m2 r e + m2 r (complement (htotal2 r) e) from by
        unfold mu2; rw [if_pos hv]]
      exact div_self hzq
    · rw [if_neg (fun h ↦ hv h.1)]
      show ((mu2 i ⟨r, e⟩ v : ℕ) : ℚ) / _ = 0
      rw [show mu2 i ⟨r, e⟩ v = 0 from by unfold mu2; rw [if_neg hv]]
      simp


theorem m2_jwv (r : Fin 1104) (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)) :
    m2 r c = (l2At r).2.1 * jwv r c.val * D := rfl

theorem mixQ_eq_PL (i : Fin 3) (r : Fin 1104) (hr : 0 < n2 r)
    (w : Fin 2 → CompleteSplit.CompleteWord 1) :
    mixQ htotal2 n2 m2 (mu2 i) r w = PL i r w := by
  classical
  have hD : (D : ℚ) ≠ 0 := by unfold D; norm_num
  have hWtn : 0 < (l2At r).2.1 := by
    by_contra hcon
    have hz : (l2At r).2.1 = 0 := by omega
    rw [show n2 r = (l2At r).2.1 * D ^ 2 from rfl, hz, zero_mul] at hr
    exact absurd hr (lt_irrefl 0)
  have hWt : ((l2At r).2.1 : ℚ) ≠ 0 := by exact_mod_cast hWtn.ne'
  unfold mixQ PL
  have hterm : ∀ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      (m2 r c : ℚ) * freqQ (mu2 i) ⟨r, c⟩ (w 0) *
        freqQ (mu2 i) ⟨r, complement (htotal2 r) c⟩ (w 1) =
      (if ((w 0 0).val = (c.val i).val ∧ (w 1 0).val = parent2 r i - (c.val i).val) then
        (((l2At r).2.1 * jwv r c.val * D : ℕ) : ℚ) else 0) := by
    intro c
    rw [freq_l2 i r c (w 0), freq_l2 i r (complement (htotal2 r) c) (w 1)]
    have hcomp : ((complement (htotal2 r) c).val i).val = parent2 r i - (c.val i).val := rfl
    have hmasscomp : m2 r (complement (htotal2 r) c) +
        m2 r (complement (htotal2 r) (complement (htotal2 r) c)) =
        m2 r c + m2 r (complement (htotal2 r) c) := by
      rw [complement_complement]; omega
    rw [hcomp, hmasscomp, ← m2_jwv r c]
    by_cases hm : m2 r c + m2 r (complement (htotal2 r) c) = 0
    · have hzero : m2 r c = 0 := by omega
      have hzero2 : m2 r (complement (htotal2 r) c) = 0 := by omega
      simp [hm, hzero, hzero2]
    · by_cases h0 : (w 0 0).val = (c.val i).val <;>
        by_cases h1 : (w 1 0).val = parent2 r i - (c.val i).val <;>
        split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun c _ ↦ hterm c)]
  rw [split_sum_expand (half := 2 * 2 ^ (1 - 1)) (parent := parent2 r)
    (fun a ↦ if ((w 0 0).val = (a i).val ∧ (w 1 0).val = parent2 r i - (a i).val) then
      (((l2At r).2.1 * jwv r a * D : ℕ) : ℚ) else 0)]
  have hsum : (∑ a : Tri,
      if ((a 0).val + (a 1).val + (a 2).val = 2 * 2 ^ (1 - 1) ∧ ∀ k, (a k).val ≤ parent2 r k) then
        (if ((w 0 0).val = (a i).val ∧ (w 1 0).val = parent2 r i - (a i).val) then
          (((l2At r).2.1 * jwv r a * D : ℕ) : ℚ) else 0) else 0)
      = ((l2At r).2.1 : ℚ) * (D : ℚ) *
        ∑ a : Tri, (if ((a 0).val + (a 1).val + (a 2).val = 2 * 2 ^ (1 - 1) ∧
            ∀ k, (a k).val ≤ parent2 r k) ∧ ((w 0 0).val = (a i).val ∧
          (w 1 0).val = parent2 r i - (a i).val) then (jwv r a : ℚ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    by_cases hA : ((a 0).val + (a 1).val + (a 2).val = 2 * 2 ^ (1 - 1) ∧
        ∀ k, (a k).val ≤ parent2 r k) <;>
      by_cases hB : ((w 0 0).val = (a i).val ∧ (w 1 0).val = parent2 r i - (a i).val) <;>
      simp [hA, hB] <;> push_cast <;> ring
  rw [hsum, show n2 r = (l2At r).2.1 * D ^ 2 from rfl]
  push_cast
  field_simp

/-- Grade triples as ordered triples of grades. -/
def triEquiv : (Fin 3 × Fin 3 × Fin 3) ≃ Tri where
  toFun x := ![x.1, x.2.1, x.2.2]
  invFun a := (a 0, a 1, a 2)
  left_inv := by intro x; simp
  right_inv := by
    intro a
    funext k
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl

/-- A sum over grade triples is an explicit threefold sum. -/
theorem sum_tri (g : Tri → ℚ) :
    ∑ a : Tri, g a =
      ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, g ![x, y, z] := by
  classical
  rw [← Equiv.sum_comp triEquiv g, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [Fintype.sum_prod_type]
  rfl

/-- The level-two mixture is the grade marginal, on the complementary pair of words. -/
theorem PL_eq_Jm (i : Fin 3) (r : Fin 1104) (w : Fin 2 → CompleteSplit.CompleteWord 1) :
    PL i r w =
      (if (w 1 0).val = parent2 r i - (w 0 0).val then (Jm r i (w 0 0) : ℚ) else 0) / (D : ℚ) := by
  classical
  unfold PL Jm
  rw [sum_tri]
  by_cases hw : (w 1 0).val = parent2 r i - (w 0 0).val
  · rw [if_pos hw]
    push_cast
    refine congrArg (fun t : ℚ ↦ t / (D : ℚ)) ?_
    refine Finset.sum_congr rfl (fun x _ ↦ Finset.sum_congr rfl (fun y _ ↦
      Finset.sum_congr rfl (fun z _ ↦ ?_)))
    by_cases hA : (((![x, y, z] : Tri) 0).val + ((![x, y, z] : Tri) 1).val +
        ((![x, y, z] : Tri) 2).val = 2 * 2 ^ (1 - 1) ∧
        ∀ k, ((![x, y, z] : Tri) k).val ≤ parent2 r k)
    · by_cases h1 : (w 0 0).val = ((![x, y, z] : Tri) i).val
      · rw [if_pos ⟨hA, h1, by rw [← h1]; exact hw⟩, if_pos ⟨hA, h1⟩]
      · rw [if_neg (fun h ↦ h1 h.2.1), if_neg (fun h ↦ h1 h.2)]
    · rw [if_neg (fun h ↦ hA h.1), if_neg (fun h ↦ hA h.1)]
  · rw [if_neg hw]
    have hz : ∀ x y z : Fin 3,
        (if ((((![x, y, z] : Tri) 0).val + ((![x, y, z] : Tri) 1).val +
            ((![x, y, z] : Tri) 2).val = 2 * 2 ^ (1 - 1) ∧
            ∀ k, ((![x, y, z] : Tri) k).val ≤ parent2 r k) ∧
           ((w 0 0).val = ((![x, y, z] : Tri) i).val ∧
            (w 1 0).val = parent2 r i - ((![x, y, z] : Tri) i).val)) then
          (jwv r ![x, y, z] : ℚ) else 0) = 0 := by
      intro x y z
      rw [if_neg]
      rintro ⟨-, h1, h2⟩
      exact hw (by rw [h1]; exact h2)
    rw [Finset.sum_congr rfl (fun x _ ↦ Finset.sum_congr rfl (fun y _ ↦
      Finset.sum_congr rfl (fun z _ ↦ hz x y z)))]
    simp
theorem Jm_112_0 (r : Fin 1104) (hP : parent2 r = ![1, 1, 2])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 0 v = (![D / 2, D / 2, 0] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
theorem Jm_112_1 (r : Fin 1104) (hP : parent2 r = ![1, 1, 2])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 1 v = (![D / 2, D / 2, 0] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
theorem Jm_112_2 (r : Fin 1104) (hP : parent2 r = ![1, 1, 2])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 2 v = (![(l2At r).2.2, D - 2 * (l2At r).2.2, (l2At r).2.2] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
theorem Jm_121_0 (r : Fin 1104) (hP : parent2 r = ![1, 2, 1])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 0 v = (![D / 2, D / 2, 0] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
theorem Jm_121_1 (r : Fin 1104) (hP : parent2 r = ![1, 2, 1])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 1 v = (![(l2At r).2.2, D - 2 * (l2At r).2.2, (l2At r).2.2] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
theorem Jm_121_2 (r : Fin 1104) (hP : parent2 r = ![1, 2, 1])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 2 v = (![D / 2, D / 2, 0] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
theorem Jm_211_0 (r : Fin 1104) (hP : parent2 r = ![2, 1, 1])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 0 v = (![(l2At r).2.2, D - 2 * (l2At r).2.2, (l2At r).2.2] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
theorem Jm_211_1 (r : Fin 1104) (hP : parent2 r = ![2, 1, 1])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 1 v = (![D / 2, D / 2, 0] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
theorem Jm_211_2 (r : Fin 1104) (hP : parent2 r = ![2, 1, 1])
    (hs : 2 * (l2At r).2.2 ≤ D) (v : Fin 3) :
    Jm r 2 v = (![D / 2, D / 2, 0] : Fin 3 → ℕ) v := by
  unfold Jm jwv
  rw [hP]
  unfold D at hs
  match v with
  | 0 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 1 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega
  | 2 =>
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [jw, D, Fin.forall_fin_succ]
    try omega

theorem shape_vec (r : Fin 1104) :
    parent2 r = ![1, 1, 2] ∨ parent2 r = ![1, 2, 1] ∨ parent2 r = ![2, 1, 1] := by
  rcases mme_released_recursive_level2_shapes.1 r with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; unfold parent2 normTriple; rw [h1, h2]; norm_num
  · right; left; unfold parent2 normTriple; rw [h1, h2]; norm_num
  · right; right; unfold parent2 normTriple; rw [h1, h2]; norm_num

theorem Jm_closed (r : Fin 1104) (i v : Fin 3) :
    Jm r i v = if parent2 r i = 2 then
        (![(l2At r).2.2, D - 2 * (l2At r).2.2, (l2At r).2.2] : Fin 3 → ℕ) v
      else (![D / 2, D / 2, 0] : Fin 3 → ℕ) v := by
  have hs := mme_released_recursive_level2_shapes.2 r
  rcases shape_vec r with h | h | h
  · match i with
    | 0 => rw [Jm_112_0 r h hs v, if_neg (by rw [h]; decide)]
    | 1 => rw [Jm_112_1 r h hs v, if_neg (by rw [h]; decide)]
    | 2 => rw [Jm_112_2 r h hs v, if_pos (by rw [h]; decide)]
  · match i with
    | 0 => rw [Jm_121_0 r h hs v, if_neg (by rw [h]; decide)]
    | 1 => rw [Jm_121_1 r h hs v, if_pos (by rw [h]; decide)]
    | 2 => rw [Jm_121_2 r h hs v, if_neg (by rw [h]; decide)]
  · match i with
    | 0 => rw [Jm_211_0 r h hs v, if_pos (by rw [h]; decide)]
    | 1 => rw [Jm_211_1 r h hs v, if_neg (by rw [h]; decide)]
    | 2 => rw [Jm_211_2 r h hs v, if_neg (by rw [h]; decide)]

end MME.L2Cert

theorem solution :
    (∀ {half : ℕ} {parent : Fin 3 → ℕ} (g : (Fin 3 → Fin (half + 1)) → ℚ),
      ∑ c : RecursiveThinSplit.Split half parent, g c.val =
        ∑ a : Fin 3 → Fin (half + 1),
          if (a 0).val + (a 1).val + (a 2).val = half ∧ ∀ i, (a i).val ≤ parent i then g a
          else 0) ∧
    (∀ (i : Fin 3) (r : Fin 1104), 0 < n2 r → ∀ w : Fin 2 → CompleteSplit.CompleteWord 1,
      mixQ htotal2 n2 m2 (mu2 i) r w = PL i r w) ∧
    (∀ (i : Fin 3) (r : Fin 1104) (w : Fin 2 → CompleteSplit.CompleteWord 1),
      PL i r w =
        (if (w 1 0).val = parent2 r i - (w 0 0).val then (Jm r i (w 0 0) : ℚ) else 0) / (D : ℚ)) ∧
    ∀ (r : Fin 1104) (i v : Fin 3), Jm r i v =
      if parent2 r i = 2 then
        (![(l2At r).2.2, D - 2 * (l2At r).2.2, (l2At r).2.2] : Fin 3 → ℕ) v
      else (![D / 2, D / 2, 0] : Fin 3 → ℕ) v :=
  ⟨fun {half} {parent} g ↦ MME.L2Cert.split_sum_expand g,
   fun i r hr w ↦ MME.L2Cert.mixQ_eq_PL i r hr w,
   fun i r w ↦ MME.L2Cert.PL_eq_Jm i r w,
   MME.L2Cert.Jm_closed⟩
