-- Prove2me | solution 1 for mme_released_recursive_level2_penalty_tools
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T02:17:47.892145+00:00
-- url     : https://prove2.me/submissions/47cf371c-4076-40a2-bcc2-516708805523

import Mathlib
import Definitions.Def_mme_released_recursive_level2_penalty_data
import Definitions.Def_mme_released_recursive_level2_sum_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_potential_floor
import Theorems.Thm_mme_released_recursive_stage_level2_counts0
import Theorems.Thm_mme_released_recursive_stage_level2_counts1
import Theorems.Thm_mme_released_recursive_stage_level2_counts2
import Theorems.Thm_mme_released_recursive_stage_level2_counts3
import Theorems.Thm_mme_certified_entropy_penalty_rational

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000


namespace MME.L2Cert

theorem m2_total' (r : Fin 1104) :
    ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r), m2 r e = n2 r := by
  rcases lt_or_ge r.val 276 with h | h
  · exact (mme_released_recursive_stage_level2_counts0 r (Nat.zero_le _) h).2
  · rcases lt_or_ge r.val 552 with h2 | h2
    · exact (mme_released_recursive_stage_level2_counts1 r h h2).2
    · rcases lt_or_ge r.val 828 with h3 | h3
      · exact (mme_released_recursive_stage_level2_counts2 r h2 h3).2
      · exact (mme_released_recursive_stage_level2_counts3 r h3 r.isLt).2

theorem alphaQ_nonneg (r : Fin 1104)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)) : 0 ≤ alphaQ r c := by
  unfold alphaQ
  positivity

theorem alphaQ_sum (r : Fin 1104) :
    ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r), alphaQ r c = 1 := by
  have hn : ((n2 r : ℕ) : ℚ) ≠ 0 := by
    have := mme_released_recursive_level2_potential_floor.1 r
    exact_mod_cast this.ne'
  unfold alphaQ
  rw [← Finset.sum_div, ← Nat.cast_sum, m2_total' r]
  exact div_self hn

/-- The level-two penalty bound of a region, from the published rational penalty bound. -/
theorem pen_bound (r : Fin 1104) :
    Real.log 2 * entropyPenalty (fun c ↦ ((alphaQ r c : ℚ) : ℝ)) ≤
      (((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
          qvalQ (fun k ↦ ∑ i, PE r i (c.val i) k)) - 2 +
        ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
          (alphaQ r c) ^ 2 / qvalQ (fun k ↦ ∑ i, PE r i (c.val i) k) : ℚ) : ℝ) :=
  mme_certified_entropy_penalty_rational (alphaQ r) (alphaQ_nonneg r) (alphaQ_sum r) (PE r)

theorem m2_jwv' (r : Fin 1104)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)) :
    m2 r c = (l2At r).2.1 * jwv r c.val * D := rfl

/-- The normalized split weight is the small split weight over the scale. -/
theorem alphaQ_jwv (r : Fin 1104)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)) :
    alphaQ r c = (jwv r c.val : ℚ) / (D : ℚ) := by
  have hW : 0 < (l2At r).2.1 := by
    have := mme_released_recursive_level2_potential_floor.1 r
    by_contra hc
    have hz : (l2At r).2.1 = 0 := by omega
    rw [show n2 r = (l2At r).2.1 * D ^ 2 from rfl, hz, zero_mul] at this
    exact absurd this (lt_irrefl 0)
  have hW' : ((l2At r).2.1 : ℚ) ≠ 0 := by exact_mod_cast hW.ne'
  have hD' : ((D : ℕ) : ℚ) ≠ 0 := by
    have : 0 < D := by unfold D; norm_num
    exact_mod_cast this.ne'
  unfold alphaQ
  rw [m2_jwv' r c, show n2 r = (l2At r).2.1 * D ^ 2 from rfl]
  push_cast
  field_simp

/-- Grade triples as ordered triples of grades. -/
def triEquivP : (Fin 3 × Fin 3 × Fin 3) ≃ Tri where
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

/-- A rational sum over grade triples is an explicit threefold sum. -/
theorem sum_triP (g : Tri → ℚ) :
    ∑ a : Tri, g a = ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, g ![x, y, z] := by
  classical
  rw [← Equiv.sum_comp triEquivP g, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [Fintype.sum_prod_type]
  rfl

/-- The split weights of a region of shape (1, 1, 2). -/
theorem jwv_112 (r : Fin 1104) (hp : parent2 r = ![1, 1, 2]) :
    jwv r ![0, 0, 2] = (l2At r).2.2 ∧
      jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 1, 0] = (l2At r).2.2 := by
  unfold jwv
  rw [hp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [jw, D, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
/-- The split weights of a region of shape (1, 2, 1). -/
theorem jwv_121 (r : Fin 1104) (hp : parent2 r = ![1, 2, 1]) :
    jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![0, 2, 0] = (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = (l2At r).2.2 ∧
      jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2 := by
  unfold jwv
  rw [hp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [jw, D, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
/-- The split weights of a region of shape (2, 1, 1). -/
theorem jwv_211 (r : Fin 1104) (hp : parent2 r = ![2, 1, 1]) :
    jwv r ![0, 1, 1] = (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2 ∧
      jwv r ![2, 0, 0] = (l2At r).2.2 := by
  unfold jwv
  rw [hp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [jw, D, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

/-- Only the parametric coordinate contributes to the penalty reference. -/
theorem PE_sum (r : Fin 1104) (a : Tri) (k : Fin 4) :
    ∑ i, PE r i (a i) k = PE r (certMode r) (a (certMode r)) k := by
  classical
  rw [Finset.sum_eq_single (certMode r)]
  · intro i _ hi
    unfold PE
    rw [if_neg hi]
  · intro h
    exact absurd (Finset.mem_univ _) h


end MME.L2Cert

theorem solution :
    (∀ (r : Fin 1104) (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)),
      0 ≤ alphaQ r c ∧ alphaQ r c = (jwv r c.val : ℚ) / (D : ℚ)) ∧
    (∀ r : Fin 1104, ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      alphaQ r c = 1) ∧
    (∀ (r : Fin 1104) (a : Tri) (k : Fin 4),
      ∑ i, PE r i (a i) k = PE r (certMode r) (a (certMode r)) k) ∧
    (∀ g : Tri → ℚ, ∑ a : Tri, g a =
      ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, g ![x, y, z]) ∧
    (∀ (r : Fin 1104), parent2 r = ![1, 1, 2] →
      jwv r ![0, 0, 2] = (l2At r).2.2 ∧ jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧ jwv r ![1, 1, 0] = (l2At r).2.2) ∧
    (∀ (r : Fin 1104), parent2 r = ![1, 2, 1] →
      jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧ jwv r ![0, 2, 0] = (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = (l2At r).2.2 ∧ jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2) ∧
    (∀ (r : Fin 1104), parent2 r = ![2, 1, 1] →
      jwv r ![0, 1, 1] = (l2At r).2.2 ∧ jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2 ∧ jwv r ![2, 0, 0] = (l2At r).2.2) ∧
    ∀ r : Fin 1104,
      Real.log 2 * entropyPenalty (fun c ↦ ((alphaQ r c : ℚ) : ℝ)) ≤
        (((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
            qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) - 2 +
          ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
            (alphaQ r c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t) : ℚ) : ℝ) :=
  ⟨fun r c ↦ ⟨MME.L2Cert.alphaQ_nonneg r c, MME.L2Cert.alphaQ_jwv r c⟩,
   MME.L2Cert.alphaQ_sum,
   fun r a k ↦ MME.L2Cert.PE_sum r a k,
   fun g ↦ MME.L2Cert.sum_triP g,
   fun r hp ↦ MME.L2Cert.jwv_112 r hp,
   fun r hp ↦ MME.L2Cert.jwv_121 r hp,
   fun r hp ↦ MME.L2Cert.jwv_211 r hp,
   fun r ↦ MME.L2Cert.pen_bound r⟩
