-- Prove2me | solution 1 for mme_released_recursive_level2_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T01:37:37.996335+00:00
-- url     : https://prove2.me/submissions/73adeb2d-f793-466a-af86-7e95d35513be

import Mathlib
import Definitions.Def_mme_released_recursive_level2_sum_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_potential_floor
import Theorems.Thm_mme_released_recursive_stage_level2_counts0
import Theorems.Thm_mme_released_recursive_stage_level2_counts1
import Theorems.Thm_mme_released_recursive_stage_level2_counts2
import Theorems.Thm_mme_released_recursive_stage_level2_counts3
import Theorems.Thm_mme_certified_entropy_bridge
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.L2Cert

/-- Pairs of one-letter words are pairs of letters. -/
def wpairEquiv : (Fin 3 × Fin 3) ≃ (Fin 2 → CompleteSplit.CompleteWord 1) where
  toFun x := wpair x.1 x.2
  invFun w := (w 0 0, w 1 0)
  left_inv := fun _ ↦ rfl
  right_inv := by
    intro w
    funext k z
    match k, z with
    | 0, 0 => rfl
    | 1, 0 => rfl

/-- A real-valued sum over pairs of one-letter words is a double sum over letters. -/
theorem sum_wpair_real (f : (Fin 2 → CompleteSplit.CompleteWord 1) → ℝ) :
    ∑ w, f w = ∑ a : Fin 3, ∑ b : Fin 3, f (wpair a b) := by
  classical
  rw [← Equiv.sum_comp wpairEquiv f, Fintype.sum_prod_type]
  rfl

/-- The entropy of the level-two mixture is the entropy of the grade distribution. -/
theorem entropy_collapse (i : Fin 3) (r : Fin 1104) (hr : 0 < n2 r) :
    entropy (fun w ↦ ((mixQ htotal2 n2 m2 (mu2 i) r w : ℚ) : ℝ)) =
      entropy (fun a : Fin 3 ↦ ((PG i r a : ℚ) : ℝ)) := by
  classical
  show ∑ w, Real.negMulLog ((mixQ htotal2 n2 m2 (mu2 i) r w : ℚ) : ℝ) = _
  rw [sum_wpair_real (fun w ↦ Real.negMulLog ((mixQ htotal2 n2 m2 (mu2 i) r w : ℚ) : ℝ))]
  show _ = ∑ a : Fin 3, Real.negMulLog ((PG i r a : ℚ) : ℝ)
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  have hc : parent2 r i - a.val < 3 := by
    have := mme_released_recursive_level2_potential_floor.2.1 r i
    omega
  rw [Finset.sum_eq_single (⟨parent2 r i - a.val, hc⟩ : Fin 3)]
  · rw [mme_released_recursive_level2_marginals.2.1 i r hr (wpair a ⟨parent2 r i - a.val, hc⟩),
      mme_released_recursive_level2_marginals.2.2.1 i r
        (wpair a ⟨parent2 r i - a.val, hc⟩)]
    show Real.negMulLog (((if (⟨parent2 r i - a.val, hc⟩ : Fin 3).val =
      parent2 r i - ((wpair a ⟨parent2 r i - a.val, hc⟩) 0 0).val then
        (Jm r i ((wpair a ⟨parent2 r i - a.val, hc⟩) 0 0) : ℚ) else 0) / (D : ℚ) : ℚ) : ℝ) = _
    rw [show ((wpair a ⟨parent2 r i - a.val, hc⟩) 0 0) = a from rfl, if_pos rfl]
    rfl
  · intro b _ hb
    rw [mme_released_recursive_level2_marginals.2.1 i r hr (wpair a b),
      mme_released_recursive_level2_marginals.2.2.1 i r (wpair a b)]
    show Real.negMulLog (((if b.val = parent2 r i - ((wpair a b) 0 0).val then
      (Jm r i ((wpair a b) 0 0) : ℚ) else 0) / (D : ℚ) : ℚ) : ℝ) = 0
    rw [show ((wpair a b) 0 0) = a from rfl,
      if_neg (fun h ↦ hb (Fin.ext h))]
    simp [Real.negMulLog]
  · intro h
    exact absurd (Finset.mem_univ _) h



/-- Grade triples as ordered triples of grades. -/
def triEquiv2 : (Fin 3 × Fin 3 × Fin 3) ≃ Tri where
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

theorem m2_jwv (r : Fin 1104)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)) :
    m2 r c = (l2At r).2.1 * jwv r c.val * D := rfl

/-- Natural-number form of the split-sum expansion. -/
theorem split_sum_expand_nat {half : Nat} {parent : Fin 3 → Nat}
    (g : (Fin 3 → Fin (half + 1)) → Nat) :
    (∑ c : RecursiveThinSplit.Split half parent, g c.val) =
      ∑ a : Fin 3 → Fin (half + 1),
        if (a 0).val + (a 1).val + (a 2).val = half ∧ ∀ i, (a i).val ≤ parent i then g a else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine (Finset.sum_subtype _ (fun a ↦ ?_) g).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Natural-number form of the triple-sum expansion. -/
theorem sum_tri_nat (g : Tri → Nat) :
    ∑ a : Tri, g a = ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, g ![x, y, z] := by
  classical
  rw [← Equiv.sum_comp triEquiv2 g, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [Fintype.sum_prod_type]
  rfl

/-- The coordinate-zero marginal counts of a level-two region, in closed form. -/
theorem marg_eq (r : Fin 1104) (j : Fin 3) :
    marginalCounts m2 0 r j = (l2At r).2.1 * Jm r 0 j * D := by
  classical
  have h1 : ∀ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      c ∈ Finset.univ.filter (fun c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r) ↦
        c.val 0 = j) ↔ c.val 0 = j := by
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 : (∑ c ∈ Finset.univ.filter
        (fun c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r) ↦ c.val 0 = j),
        m2 r c) =
      ∑ a : {c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r) // c.val 0 = j},
        m2 r a.val :=
    Finset.sum_subtype _ h1 _
  have step1 : marginalCounts m2 0 r j =
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        (if c.val 0 = j then (l2At r).2.1 * jwv r c.val * D else 0) := by
    unfold marginalCounts
    rw [← h2, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun c _ ↦ ?_)
    by_cases hc : c.val 0 = j
    · rw [if_pos hc, if_pos hc, m2_jwv r c]
    · rw [if_neg hc, if_neg hc]
  rw [step1]
  rw [show (∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      (if c.val 0 = j then (l2At r).2.1 * jwv r c.val * D else 0)) =
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        (fun a : Tri ↦ if a 0 = j then (l2At r).2.1 * jwv r a * D else 0) c.val from rfl]
  rw [split_sum_expand_nat (fun a : Tri ↦ if a 0 = j then (l2At r).2.1 * jwv r a * D else 0),
    sum_tri_nat]
  rw [show (l2At r).2.1 * Jm r 0 j * D =
      ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3,
        (l2At r).2.1 *
          (if (((![x, y, z] : Tri) 0).val + (![x, y, z] : Tri) 1 + (![x, y, z] : Tri) 2 =
              2 * 2 ^ (1 - 1) ∧ ∀ k, ((![x, y, z] : Tri) k).val ≤ parent2 r k) ∧
              (j : Fin 3).val = ((![x, y, z] : Tri) 0).val then jwv r ![x, y, z] else 0) * D from by
    unfold Jm
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    rw [Finset.mul_sum, Finset.sum_mul]]
  refine Finset.sum_congr rfl (fun x _ ↦ Finset.sum_congr rfl (fun y _ ↦
    Finset.sum_congr rfl (fun z _ ↦ ?_)))
  by_cases hA : (((![x, y, z] : Tri) 0).val + ((![x, y, z] : Tri) 1).val +
      ((![x, y, z] : Tri) 2).val = 2 * 2 ^ (1 - 1) ∧
      ∀ k, ((![x, y, z] : Tri) k).val ≤ parent2 r k)
  · by_cases hB : ((![x, y, z] : Tri) 0 = j)
    · rw [if_pos hA, if_pos hB, if_pos ⟨hA, (Fin.ext_iff.mp hB).symm⟩]
      try ring
    · rw [if_pos hA, if_neg hB, if_neg (fun h ↦ hB (Fin.ext h.2.symm))]
      try ring
  · rw [if_neg hA, if_neg (fun h ↦ hA h.1)]
    try ring


theorem m2_total (r : Fin 1104) :
    ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r), m2 r e = n2 r := by
  rcases lt_or_ge r.val 276 with h | h
  · exact (mme_released_recursive_stage_level2_counts0 r (Nat.zero_le _) h).2
  · rcases lt_or_ge r.val 552 with h2 | h2
    · exact (mme_released_recursive_stage_level2_counts1 r h h2).2
    · rcases lt_or_ge r.val 828 with h3 | h3
      · exact (mme_released_recursive_stage_level2_counts2 r h2 h3).2
      · exact (mme_released_recursive_stage_level2_counts3 r h3 r.isLt).2

theorem marg_total (r : Fin 1104) : ∑ j, marginalCounts m2 0 r j = n2 r := by
  classical
  rw [show (∑ j, marginalCounts m2 0 r j) =
      ∑ j : Fin (2 * 2 ^ (1 - 1) + 1),
        ∑ a : {a : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r) // a.val 0 = j},
          m2 r a.val from rfl]
  rw [Fintype.sum_fiberwise
    (fun a : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r) ↦ a.val 0)
    (fun c ↦ m2 r c)]
  exact m2_total r

theorem normQ_marg (r : Fin 1104) (j : Fin 3) :
    normQ (marginalCounts m2 0 r) j = PG 0 r j := by
  have hW : 0 < (l2At r).2.1 := by
    have := mme_released_recursive_level2_potential_floor.1 r
    by_contra hc
    have hz : (l2At r).2.1 = 0 := by omega
    rw [show n2 r = (l2At r).2.1 * D ^ 2 from rfl, hz, zero_mul] at this
    exact absurd this (lt_irrefl 0)
  have hD : 0 < D := by unfold D; norm_num
  unfold normQ PG
  rw [marg_total r, marg_eq r j, show n2 r = (l2At r).2.1 * D ^ 2 from rfl]
  have hW' : ((l2At r).2.1 : ℚ) ≠ 0 := by exact_mod_cast hW.ne'
  have hD' : ((D : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  field_simp

/-- The level-two coarse potential is the mode-zero parent potential. -/
theorem coarse_eq : coarsePotential m2 0 = parentPotential htotal2 n2 m2 (mu2 0) := by
  rw [mme_certified_entropy_bridge.{0, 0}.2.2.2.2.2 m2 0
      (fun r ↦ by rw [marg_total r]; exact mme_released_recursive_level2_potential_floor.1 r),
    mme_certified_entropy_bridge.{0, 0}.2.2.2.1 htotal2 n2 m2 (mu2 0)]
  refine Finset.sum_congr rfl (fun r _ ↦ ?_)
  rw [marg_total r]
  refine congrArg (fun t : ℝ ↦ ((n2 r : ℕ) : ℝ) * t) ?_
  rw [show (fun j ↦ ((normQ (marginalCounts m2 0 r) j : ℚ) : ℝ)) =
      (fun j : Fin 3 ↦ ((PG 0 r j : ℚ) : ℝ)) from
    funext fun j ↦ by rw [normQ_marg r j]]
  exact (entropy_collapse 0 r (mme_released_recursive_level2_potential_floor.1 r)).symm


end MME.L2Cert

theorem solution :
    (∀ (i : Fin 3) (r : Fin 1104), 0 < n2 r →
      entropy (fun w ↦ ((mixQ htotal2 n2 m2 (mu2 i) r w : ℚ) : ℝ)) =
        entropy (fun a : Fin 3 ↦ ((PG i r a : ℚ) : ℝ))) ∧
    (∀ (r : Fin 1104) (j : Fin 3),
      marginalCounts m2 0 r j = (l2At r).2.1 * Jm r 0 j * D) ∧
    (∀ r : Fin 1104, ∑ j, marginalCounts m2 0 r j = n2 r) ∧
    coarsePotential m2 0 = parentPotential htotal2 n2 m2 (mu2 0) :=
  ⟨fun i r hr ↦ MME.L2Cert.entropy_collapse i r hr,
   fun r j ↦ MME.L2Cert.marg_eq r j,
   MME.L2Cert.marg_total,
   MME.L2Cert.coarse_eq⟩
