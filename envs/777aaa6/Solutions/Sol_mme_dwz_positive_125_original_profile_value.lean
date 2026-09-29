-- Prove2me | solution 1 for mme_dwz_positive_125_original_profile_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T01:55:37.582215+00:00
-- url     : https://prove2.me/submissions/e7ff3944-8776-488b-8cff-bc837365b4de

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_positive_125_regional_profile_data
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_six_symmetrized_tau_value
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_complete_split_CW_square_cyclic_basis_transport
import Theorems.Thm_mme_CW_square_canonical_support_and_scalar_blocks
import Theorems.Thm_mme_dwz_fourth_coupled63_prescribedZ_six_values
import Theorems.Thm_mme_CW_square_canonical_central202_restrict
import Theorems.Thm_mme_dwz_fourth_elementary_four_actual_prescribed_z_endpoints
import Theorems.Thm_mme_dwz_induced_regional_square_children_restrict_original_profiles
import Theorems.Thm_mme_dwz_positive_125_original_profile_regional_restrict
import Theorems.Thm_mme_dwz_prescribed_z_power_projection
import Theorems.Thm_mme_dwz_prescribed_z_six_finite_common_physical_length
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Theorems.Thm_mme_HasPrescribedZSix_of_constant_grade_oneHot
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Theorems.Thm_mme_MMObj_tau_value
import Theorems.Thm_mme_recursive_thin_regional_induced_families_below_marginal_rate
import Theorems.Thm_mme_recursive_thin_split_marginal_joint_counts
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_scaled_multinomial_log_rate
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_sixSymmetrization_kronFin_isomorphic
import Theorems.Thm_mme_sixSymmetrization_MMObj_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict

universe u

section

open MME MME.TensorObj MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

namespace MME.DWZC1SimultaneousChild

noncomputable def regionTarget {K : Type u} [Field K] (q N : ℕ)
    (sx sy : Fin N → Fin 3 → Fin 5) : TensorObj K 3 :=
  kronFin N (fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx r))
    ((cwSquareCanonicalGrading K q).blockSubtensor (sy r)))

noncomputable def regionSource {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ) : TensorObj K 3 :=
  prescribedZPower (cwFourthConstituent K q I J L)
    (constituentBasis K q I J L 2)
    (fun a : LiftedCoarseCoordinate.{u} q L ↦ cwSquarePairGrade q a.down.val.1) p m

/-- Reuse the accepted simultaneous tensor extraction without replaying its
private map-construction proof in the final endpoint submission. -/
theorem simultaneous_regional_restrict {K : Type u} [Field K] (q R k : ℕ)
    (I J L : Fin R → Fin 9) (p : Fin R → IntegerZSplitProfile 5)
    (m : Fin R → ℕ) (σ : Fin R → Equiv.Perm (Fin 3))
    (sx sy : ∀ _j : Fin k, ∀ r : Fin R, Fin ((p r).length (m r)) → Fin 3 → Fin 5)
    (hsum : ∀ j r t i, (sx j r t i).val + (sy j r t i).val =
      (cwFourthBlockType (I r) (J r) (L r) i).val)
    (hprofile : ∀ j r a, (Finset.univ.filter
      (fun t : Fin ((p r).length (m r)) ↦ sx j r t 2 = a)).card = (p r).count a * m r)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r t,
        (sx (js (σ r 0)) r t 0).val + (sx (js (σ r 1)) r t 1).val +
          (sx (js (σ r 2)) r t 2).val = 4) →
      ∃ j, js = fun _ ↦ j) :
    TensorObj.Restrict
      (bigAdd (fun j : Fin k ↦ kronFin R (fun r ↦
        permObj (σ r) (regionTarget q ((p r).length (m r)) (sx j r) (sy j r)))))
      (kronFin R (fun r ↦ permObj (σ r) (regionSource (K := K) q (I r) (J r) (L r) (p r) (m r)))) := by
  exact mme_dwz_induced_regional_square_children_restrict_original_profiles
    (K := K) q R k I J L p m σ sx sy hsum hprofile hInduced

end MME.DWZC1SimultaneousChild

end


section

open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MME.DWZC1CoarseCounts

theorem prescribed_card {A : Type*} [Fintype A] (n : ℕ) (m : A → ℕ)
    (hm : ∑ a, m a = n) :
    Nat.card {w : Fin n → A // ∀ a, Fintype.card {t // w t = a} = m a} =
      Nat.multinomial Finset.univ m := by
  have h := mme_fintype_prescribed_fiber_function_card (α := Fin n) m
    (by simpa only [Fintype.card_fin] using hm)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.multinomial, hm] using h

theorem joint_card (half : ℕ) (parent : Fin 3 → ℕ) (n : ℕ)
    (m : MME.RecursiveThinSplit.Split half parent → ℕ) (hm : ∑ a, m a = n) :
    Nat.card {w : Fin n → MME.RecursiveThinSplit.Split half parent // HasJointCounts w m} =
      Nat.multinomial Finset.univ m := by
  have h := prescribed_card n m hm
  simpa only [HasJointCounts, count, Fintype.card_subtype] using h

theorem target_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) :
    (target (n := n) m).card = ∏ r, Nat.multinomial Finset.univ (m r) := by
  have he := @Equiv.subtypePiEquivPi (Fin R)
    (fun r ↦ Fin (n r) → MME.RecursiveThinSplit.Split half (parent r))
    (fun r w ↦ HasJointCounts w (m r))
  have hc := Nat.card_congr he
  rw [Nat.card_pi] at hc
  have hcard : (target (n := n) m).card =
      Nat.card {w : Address half R parent n // ∀ r, HasJointCounts (w r) (m r)} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, target]
  rw [hcard, hc]
  exact Finset.prod_congr rfl (fun r _ ↦ joint_card half (parent r) (n r) (m r) (hm r))

def marginal {half : ℕ} {parent : Fin 3 → ℕ}
    (m : MME.RecursiveThinSplit.Split half parent → ℕ) (i : Fin 3) (j : Fin (half + 1)) : ℕ :=
  ∑ a : {a : MME.RecursiveThinSplit.Split half parent // a.val i = j}, m a.val

theorem marginal_sum {half : ℕ} {parent : Fin 3 → ℕ}
    (m : MME.RecursiveThinSplit.Split half parent → ℕ) (i : Fin 3) :
    (∑ j, marginal m i j) = ∑ a, m a := by
  exact Fintype.sum_fiberwise (fun a : MME.RecursiveThinSplit.Split half parent ↦ a.val i) m

def degree {half : ℕ} {parent : Fin 3 → ℕ}
    (m : MME.RecursiveThinSplit.Split half parent → ℕ) (i : Fin 3) : ℕ :=
  ∏ j, (marginal m i j).factorial /
    ∏ a : {a : MME.RecursiveThinSplit.Split half parent // a.val i = j}, (m a.val).factorial

theorem joint_fiber_card (half : ℕ) (parent : Fin 3 → ℕ) (n : ℕ)
    (m : MME.RecursiveThinSplit.Split half parent → ℕ) (i : Fin 3) (x : Fin n → Fin (half + 1))
    (hx : ∀ j, Fintype.card {t // x t = j} = marginal m i j) :
    Nat.card {w : Fin n → MME.RecursiveThinSplit.Split half parent //
      HasJointCounts w m ∧ (∀ t, (w t).val i = x t)} = degree m i := by
  have h := mme_fintype_constrained_prescribed_fiber_function_card
    x (fun a : MME.RecursiveThinSplit.Split half parent ↦ a.val i) m (fun j ↦ (hx j).symm)
  have he : {w : Fin n → MME.RecursiveThinSplit.Split half parent //
      HasJointCounts w m ∧ (∀ t, (w t).val i = x t)} ≃
      {w : Fin n → MME.RecursiveThinSplit.Split half parent //
        (∀ t, (w t).val i = x t) ∧
          ∀ a, Fintype.card {t // w t = a} = m a} :=
    Equiv.subtypeEquivRight (fun w ↦ by
      simp only [HasJointCounts, count, Fintype.card_subtype, and_comm])
  rw [Nat.card_congr he, h]
  simp only [hx, degree]

theorem target_fiber_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (i : Fin 3) (x : ∀ r, Fin (n r) → Fin (half + 1))
    (hx : ∀ r j, Fintype.card {t // x r t = j} = marginal (m r) i j) :
    ((target (n := n) m).filter (fun w ↦ block i w = x)).card =
      ∏ r, degree (m r) i := by
  let W := {w : Address half R parent n //
    ∀ r, HasJointCounts (w r) (m r) ∧ ∀ t, (w r t).val i = x r t}
  have hc : ((target (n := n) m).filter (fun w ↦ block i w = x)).card = Nat.card W := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, target,
      Finset.filter_filter, W]
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, hxw⟩ r
      exact ⟨hw r, fun t ↦ congrFun (congrFun hxw r) t⟩
    · intro hw
      exact ⟨fun r ↦ (hw r).1, funext fun r ↦ funext (hw r).2⟩
  have he := @Equiv.subtypePiEquivPi (Fin R)
    (fun r ↦ Fin (n r) → MME.RecursiveThinSplit.Split half (parent r))
    (fun r w ↦ HasJointCounts w (m r) ∧ ∀ t, (w t).val i = x r t)
  rw [hc, Nat.card_congr he, Nat.card_pi]
  exact Finset.prod_congr rfl (fun r _ ↦
    joint_fiber_card half (parent r) (n r) (m r) i (x r) (hx r))

theorem ambient_fiber_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (i : Fin 3) (a : Address half R parent n) (ha : a ∈ ambient (n := n) m) :
    ((ambient (n := n) m).filter (fun b ↦ block i b = block i a)).card =
      ∏ r, degree (m r) i := by
  have he := (mme_recursive_x_hash_family_counts half R parent n m).2.2 hthin
  rw [he]
  apply target_fiber_card
  intro r j
  have h := (Finset.mem_filter.mp ha).2 r i j
  simpa only [HasMarginalCounts, count, Fintype.card_subtype, block, marginal] using h

theorem degree_pos {half : ℕ} {parent : Fin 3 → ℕ}
    (m : MME.RecursiveThinSplit.Split half parent → ℕ) (i : Fin 3) : 0 < degree m i := by
  apply Finset.prod_pos
  intro j _
  exact Nat.multinomial_pos Finset.univ (fun a : {a : MME.RecursiveThinSplit.Split half parent // a.val i = j} ↦ m a.val)

theorem degree_factorial_spec {half : ℕ} {parent : Fin 3 → ℕ}
    (m : MME.RecursiveThinSplit.Split half parent → ℕ) (i : Fin 3) :
    (∏ a, (m a).factorial) * degree m i = ∏ j, (marginal m i j).factorial := by
  calc
    _ = (∏ j, ∏ a : {a : MME.RecursiveThinSplit.Split half parent // a.val i = j}, (m a.val).factorial) *
        (∏ j, (marginal m i j).factorial /
          ∏ a : {a : MME.RecursiveThinSplit.Split half parent // a.val i = j}, (m a.val).factorial) := by
      rw [Fintype.prod_fiberwise (fun a : MME.RecursiveThinSplit.Split half parent ↦ a.val i)
        (fun a ↦ (m a).factorial)]
      rfl
    _ = ∏ j, (∏ a : {a : MME.RecursiveThinSplit.Split half parent // a.val i = j}, (m a.val).factorial) *
        ((marginal m i j).factorial /
          ∏ a : {a : MME.RecursiveThinSplit.Split half parent // a.val i = j}, (m a.val).factorial) :=
      Finset.prod_mul_distrib.symm
    _ = ∏ j, (marginal m i j).factorial := by
      apply Finset.prod_congr rfl
      intro j _
      exact Nat.mul_div_cancel' (Nat.prod_factorial_dvd_factorial_sum Finset.univ
        (fun a : {a : MME.RecursiveThinSplit.Split half parent // a.val i = j} ↦ m a.val))

theorem multinomial_eq_marginal_mul_degree {half : ℕ} {parent : Fin 3 → ℕ}
    (m : MME.RecursiveThinSplit.Split half parent → ℕ) (i : Fin 3) :
    Nat.multinomial Finset.univ m =
      Nat.multinomial Finset.univ (marginal m i) * degree m i := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.prod_factorial_pos Finset.univ m)
  rw [Nat.multinomial_spec]
  calc
    (∑ a, m a).factorial = (∏ j, (marginal m i j).factorial) *
        Nat.multinomial Finset.univ (marginal m i) := by
      rw [Nat.multinomial_spec, marginal_sum]
    _ = (∏ a, (m a).factorial) *
        (Nat.multinomial Finset.univ (marginal m i) * degree m i) := by
      rw [← degree_factorial_spec]
      ring

theorem regional_multinomial_factorization (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) :
    (∏ r, Nat.multinomial Finset.univ (m r)) =
      (∏ r, Nat.multinomial Finset.univ (marginal (m r) i)) * ∏ r, degree (m r) i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun r _ ↦ multinomial_eq_marginal_mul_degree (m r) i)

theorem ambient_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) :
    (ambient (n := n) m).card = ∏ r, Nat.multinomial Finset.univ (m r) := by
  rw [(mme_recursive_x_hash_family_counts half R parent n m).2.2 hthin]
  exact target_card half R parent n m hm

theorem ambient_image_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) (i : Fin 3) :
    ((ambient (n := n) m).image (block i)).card =
      ∏ r, Nat.multinomial Finset.univ (marginal (m r) i) := by
  have hc := Finset.card_eq_sum_card_image (block i) (ambient (n := n) m)
  have hf : (∑ x ∈ (ambient (n := n) m).image (block i),
      ((ambient (n := n) m).filter (fun w ↦ block i w = x)).card) =
      ((ambient (n := n) m).image (block i)).card * ∏ r, degree (m r) i := by
    calc
      _ = ∑ _x ∈ (ambient (n := n) m).image (block i), ∏ r, degree (m r) i := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact ambient_fiber_card half R parent hthin n m i a ha
      _ = _ := by simp
  rw [hf, ambient_card half R parent hthin n m hm,
    regional_multinomial_factorization half R parent m i] at hc
  exact (Nat.eq_of_mul_eq_mul_right
    (Finset.prod_pos (fun r _ ↦ degree_pos (m r) i)) hc).symm

end MME.DWZC1CoarseCounts

end


section

open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MME.DWZC1CoarseCounts

noncomputable def entropyMass {A : Type*} [Fintype A] (m : A → ℕ) : ℝ :=
  ((∑ a, m a : ℕ) : ℝ) * Real.log ((∑ a, m a : ℕ) : ℝ) -
    ∑ a, (m a : ℝ) * Real.log (m a : ℝ)

def scaled {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (t : ℕ) (r : Fin R)
    (a : MME.RecursiveThinSplit.Split half (parent r)) : ℕ := m r a * t

def jointCount {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) : ℕ :=
  ∏ r, Nat.multinomial Finset.univ (m r)

def blockCount {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) : ℕ :=
  ∏ r, Nat.multinomial Finset.univ (marginal (m r) i)

def starDegree {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) : ℕ := ∏ r, degree (m r) i

noncomputable def jointEntropy {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) : ℝ := ∑ r, entropyMass (m r)

noncomputable def blockEntropy {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) : ℝ :=
  ∑ r, entropyMass (marginal (m r) i)

theorem jointCount_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) : 0 < jointCount m :=
  Finset.prod_pos (fun _r _ ↦ Nat.multinomial_pos _ _)

theorem blockCount_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) : 0 < blockCount m i :=
  Finset.prod_pos (fun _r _ ↦ Nat.multinomial_pos _ _)

theorem starDegree_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) : 0 < starDegree m i :=
  Finset.prod_pos (fun r _ ↦ degree_pos (m r) i)

theorem jointCount_eq_blockCount_mul_starDegree
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) :
    jointCount m = blockCount m i * starDegree m i :=
  regional_multinomial_factorization half R parent m i

theorem product_scaled_multinomial_rate
    {S : Type*} [Fintype S] {A : S → Type*} [∀ s, Fintype (A s)]
    (m : ∀ s, A s → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log
      (∏ s, (Nat.multinomial Finset.univ (fun a ↦ m s a * t) : ℝ)) / (t : ℝ))
      atTop (𝓝 (∑ s, entropyMass (m s))) := by
  have h := tendsto_finset_sum Finset.univ
    (fun s _ ↦ mme_scaled_multinomial_log_rate (m s))
  convert h using 1
  funext t
  rw [Real.log_prod]
  · exact Finset.sum_div ..
  · intro s _
    exact_mod_cast (Nat.multinomial_pos (s := Finset.univ)
      (f := fun a ↦ m s a * t)).ne'

theorem marginal_scaled {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (t : ℕ) (r : Fin R) (i : Fin 3)
    (j : Fin (half + 1)) :
    marginal (scaled m t r) i j = marginal (m r) i j * t := by
  simp only [marginal, scaled, Finset.sum_mul]

theorem jointCount_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log (jointCount (scaled m t) : ℝ) / (t : ℝ))
      atTop (𝓝 (jointEntropy m)) := by
  simpa only [jointCount, scaled, Nat.cast_prod, jointEntropy] using
    product_scaled_multinomial_rate m

theorem blockCount_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) :
    Tendsto (fun t : ℕ ↦ Real.log (blockCount (scaled m t) i : ℝ) / (t : ℝ))
      atTop (𝓝 (blockEntropy m i)) := by
  have h := product_scaled_multinomial_rate (fun r ↦ marginal (m r) i)
  simpa only [blockCount, Nat.cast_prod, blockEntropy,
    show ∀ t r, marginal (scaled m t r) i = fun j ↦ marginal (m r) i j * t from
      fun t r ↦ funext (marginal_scaled m t r i)] using h

theorem starDegree_log_eq {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) :
    Real.log (starDegree m i : ℝ) =
      Real.log (jointCount m : ℝ) - Real.log (blockCount m i : ℝ) := by
  have h := jointCount_eq_blockCount_mul_starDegree m i
  have hb : (blockCount m i : ℝ) ≠ 0 := by exact_mod_cast (blockCount_pos m i).ne'
  have hd : (starDegree m i : ℝ) ≠ 0 := by exact_mod_cast (starDegree_pos m i).ne'
  rw [h, Nat.cast_mul, Real.log_mul hb hd]
  ring

theorem starDegree_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) :
    Tendsto (fun t : ℕ ↦ Real.log (starDegree (scaled m t) i : ℝ) / (t : ℝ))
      atTop (𝓝 (jointEntropy m - blockEntropy m i)) := by
  simpa only [starDegree_log_eq, sub_div] using
    (jointCount_log_rate m).sub (blockCount_log_rate m i)

def maxStarDegree {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) : ℕ :=
  max (max (starDegree m 0) (starDegree m 1)) (starDegree m 2)

private theorem log_max_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (max a b) = max (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log ha h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log hb h)]

theorem maxStarDegree_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log (maxStarDegree (scaled m t) : ℝ) / (t : ℝ))
      atTop (𝓝 (max (max (jointEntropy m - blockEntropy m 0)
        (jointEntropy m - blockEntropy m 1)) (jointEntropy m - blockEntropy m 2))) := by
  have h := ((starDegree_log_rate m 0).max (starDegree_log_rate m 1)).max
    (starDegree_log_rate m 2)
  convert h using 1
  funext t
  have hd (i : Fin 3) : (0 : ℝ) < starDegree (scaled m t) i := by
    exact_mod_cast starDegree_pos (scaled m t) i
  rw [maxStarDegree, Nat.cast_max, Nat.cast_max,
    log_max_pos _ _ (lt_max_of_lt_left (hd 0)) (hd 2),
    log_max_pos _ _ (hd 0) (hd 1),
    max_div_div_right (Nat.cast_nonneg t), max_div_div_right (Nat.cast_nonneg t)]

theorem classical_surviving_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦
      (Real.log (jointCount (scaled m t) : ℝ) -
        Real.log (maxStarDegree (scaled m t) : ℝ)) / (t : ℝ))
      atTop (𝓝 (min (min (blockEntropy m 0) (blockEntropy m 1)) (blockEntropy m 2))) := by
  have h := (jointCount_log_rate m).sub (maxStarDegree_log_rate m)
  have hid : jointEntropy m -
      max (max (jointEntropy m - blockEntropy m 0) (jointEntropy m - blockEntropy m 1))
        (jointEntropy m - blockEntropy m 2) =
      min (min (blockEntropy m 0) (blockEntropy m 1)) (blockEntropy m 2) := by
    simp only [max_def, min_def]
    split_ifs <;> linarith
  simpa only [← sub_div, hid] using h

end MME.DWZC1CoarseCounts

end


section

open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace MME.DWZC2Exact125

def alphaCount : Fin 3 → Fin 6 → ℕ := ![
  ![195018609810166,162904858550640,141738231464256,141749965224232,163568763585687,195019571365019],
  ![1414906715525,309457232296906,189127666325256,189127396545243,309457909988708,1414888128362],
  ![1362696554691,336198157907930,162438977495600,162438686126912,336198803283922,1362678630945]]

def regionWeightCount : Fin 3 → ℕ :=
  ![86974611,552127551170202,447872361855188]

def alpha (r : Fin 3) (s : Fin 6) : ℚ := alphaCount r s / 1000000000000000

def leftShape : Fin 3 → Fin 6 → Fin 3 → Fin 5 := ![
  ![![0,0,4],![0,1,3],![0,2,2],![1,0,3],![1,1,2],![1,2,1]],
  ![![0,4,0],![1,3,0],![2,2,0],![0,3,1],![1,2,1],![2,1,1]],
  ![![4,0,0],![3,0,1],![2,0,2],![3,1,0],![2,1,1],![1,1,2]]]

def objectId : Fin 3 → Fin 6 → ℕ :=
  ![![7,8,22,12,79,80],![11,15,23,10,80,81],![21,19,24,20,81,79]]

/-- Physical child Z frequencies (sanity data); the interior 112 frequency is the
accepted canonical coupled63 profile of this consumer. -/
def childProfile : Fin 3 → Fin 6 → Fin 3 → ℚ := ![
  ![![0,0,1],![0,499999999026019/1000000000000000,500000000973981/1000000000000000],![1/27,25/27,1/27],![0,499999999026019/1000000000000000,500000000973981/1000000000000000],![91875149636298293671007557816071292692811/500000000000000500000000000000000000000000000,249908124850363951706328992442183928707307189/250000000000000250000000000000000000000000000,91875149636298293671007557816071292692811/500000000000000500000000000000000000000000000],![1/2,1/2,0]],
  ![![1,0,0],![1,0,0],![1,0,0],![249999999930157/500000000000000,250000000069843/500000000000000,0],![1/2,1/2,0],![1/2,1/2,0]],
  ![![1,0,0],![249999999930157/500000000000000,250000000069843/500000000000000,0],![1/27,25/27,1/27],![1,0,0],![1/2,1/2,0],![91875149636298293671007557816071292692811/500000000000000500000000000000000000000000000,249908124850363951706328992442183928707307189/250000000000000250000000000000000000000000000,91875149636298293671007557816071292692811/500000000000000500000000000000000000000000000]]]

def originalRegionalCounts : Fin 3 → Fin 5 → ℕ := ![
  ![0,195019571365019,305306995049943,304654823774872,195018609810166],
  ![0,1414888128362,498585576313964,498584628842149,1414906715525],
  ![0,1362678630945,498637780779522,498636844034842,1362696554691]]

def originalParentCounts : Fin 5 → ℕ :=
  ![0,1391521776134589574137594393,498608940440923927790391158037,498607997716856279216764679186,1391540066086203418706568384]

def rotatedCoarseCounts : Fin 3 → Fin 5 → ℕ := ![
  ![0,195019571365019,305306995049943,304654823774872,195018609810166],
  ![499999805337687,500000194662313,0,0,0],
  ![163801382681603,672396961191852,163801656126545,0,0]]

theorem original_parent_counts_preserved :
    (∀ r g, (∑ s : Fin 6, if leftShape 0 s 2 = g then alphaCount r s else 0) =
      originalRegionalCounts r g) ∧
    (∀ g, (∑ r : Fin 3, regionWeightCount r * originalRegionalCounts r g) =
      originalParentCounts g) ∧
    (∑ r : Fin 3, regionWeightCount r) = 1000000000000001 ∧
    (∀ r g, (∑ s : Fin 6, if leftShape r s 2 = g then alphaCount r s else 0) =
      rotatedCoarseCounts r g) := by
  decide +kernel

theorem exact_finite_data :
    (∀ r s, 0 < alpha r s) ∧
    (∀ r, ∑ s, alpha r s = 1) ∧
    (∀ r s a, 0 ≤ childProfile r s a) ∧
    (∀ r s, ∑ a, childProfile r s a = 1) ∧
    (∀ r s a, childProfile r s a ≠ 0 →
      ∃ b : Fin 3, a.val + b.val = (leftShape r s 2).val) ∧
    (∀ r s, (leftShape r s 2).val + (leftShape r (Fin.rev s) 2).val =
      ![5,1,2] r) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
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

end MME.DWZC2Exact125

end


section

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MME.DWZB2Positivity

/-- Homogeneous entropy subadditivity for any finite nonnegative table,
including zero rows, zero columns, and a zero total. -/
theorem table_entropy_subadditivity
    {D L : Type*} [Fintype D] [Fintype L]
    (x : D → L → ℝ) (hx : ∀ d l, 0 ≤ x d l) :
    (∑ l, (∑ d, x d l) * Real.log (∑ d, x d l)) -
      (∑ d, ∑ l, x d l * Real.log (x d l)) +
      (∑ d, (∑ l, x d l) * Real.log (∑ l, x d l)) ≤
      (∑ d, ∑ l, x d l) * Real.log (∑ d, ∑ l, x d l) := by
  let row (d : D) : ℝ := ∑ l, x d l
  let col (l : L) : ℝ := ∑ d, x d l
  let total : ℝ := ∑ d, row d
  have hr (d : D) : 0 ≤ row d := Finset.sum_nonneg (fun l _ ↦ hx d l)
  have hc (l : L) : 0 ≤ col l := Finset.sum_nonneg (fun d _ ↦ hx d l)
  have ht : 0 ≤ total := Finset.sum_nonneg (fun d _ ↦ hr d)
  have hxrow (d : D) (l : L) : x d l ≤ row d :=
    Finset.single_le_sum (fun l _ ↦ hx d l) (Finset.mem_univ l)
  have hxcol (d : D) (l : L) : x d l ≤ col l :=
    Finset.single_le_sum (fun d _ ↦ hx d l) (Finset.mem_univ d)
  have hrowtotal (d : D) : row d ≤ total :=
    Finset.single_le_sum (fun d _ ↦ hr d) (Finset.mem_univ d)
  have hcolsum : ∑ l, col l = total := by
    dsimp [col, total, row]
    exact Finset.sum_comm
  by_cases ht0 : total = 0
  · have hx0 (d : D) (l : L) : x d l = 0 := by
      have h := (hxrow d l).trans (hrowtotal d)
      rw [ht0] at h
      exact le_antisymm h (hx d l)
    simp only [hx0, Finset.sum_const_zero, Real.log_zero, zero_mul,
      sub_self, add_zero, le_refl]
  have htpos : 0 < total := lt_of_le_of_ne ht (Ne.symm ht0)
  have hterm (d : D) (l : L) :
      x d l * Real.log (row d) + x d l * Real.log (col l) -
        x d l * Real.log (x d l) - x d l * Real.log total ≤
      row d * col l / total - x d l := by
    by_cases hzero : x d l = 0
    · simpa only [hzero, zero_mul, add_zero, sub_zero] using
        div_nonneg (mul_nonneg (hr d) (hc l)) ht
    have hpos : 0 < x d l := lt_of_le_of_ne (hx d l) (Ne.symm hzero)
    have hrpos : 0 < row d := hpos.trans_le (hxrow d l)
    have hcpos : 0 < col l := hpos.trans_le (hxcol d l)
    have hypos : 0 < row d * col l / total :=
      div_pos (mul_pos hrpos hcpos) htpos
    calc
      _ = x d l * Real.log ((row d * col l / total) / x d l) := by
        rw [Real.log_div hypos.ne' hpos.ne',
          Real.log_div (mul_pos hrpos hcpos).ne' htpos.ne',
          Real.log_mul hrpos.ne' hcpos.ne']
        ring
      _ ≤ x d l * (((row d * col l / total) / x d l) - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hypos hpos)) (hx d l)
      _ = row d * col l / total - x d l := by
        field_simp
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) ↦
    Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) ↦ hterm d l))
  have hrow : (∑ d, ∑ l, x d l * Real.log (row d)) =
      ∑ d, row d * Real.log (row d) := by
    simp only [← Finset.sum_mul, row]
  have hcol : (∑ d, ∑ l, x d l * Real.log (col l)) =
      ∑ l, col l * Real.log (col l) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, col]
  have htotal : (∑ d, ∑ l, x d l * Real.log total) =
      total * Real.log total := by
    simp only [← Finset.sum_mul, total, row]
  have hprod : (∑ d, ∑ l, row d * col l / total) = total := by
    simp only [← Finset.sum_div, ← Finset.mul_sum, hcolsum]
    rw [← Finset.sum_mul]
    change total * total / total = total
    exact mul_div_cancel_right₀ total ht0
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [hrow, hcol, htotal, hprod] at hsum
  change _ ≤ _ - total at hsum
  change (∑ l, col l * Real.log (col l)) -
    (∑ d, ∑ l, x d l * Real.log (x d l)) +
    (∑ d, row d * Real.log (row d)) ≤ total * Real.log total
  linarith

end MME.DWZB2Positivity

end


section

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC2Exact125

noncomputable def entropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

theorem entropy_scale {A : Type*} [Fintype A] (p : A → ℝ)
    (hp : ∑ a, p a = 1) (t : ℝ) :
    entropy (fun a ↦ t * p a) = Real.negMulLog t + t * entropy p := by
  simp only [entropy, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hp, one_mul]

theorem entropy_product {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) :
    entropy (fun x : A × B ↦ p x.1 * q x.2) = entropy p + entropy q := by
  simp only [entropy, Fintype.sum_prod_type, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hp, hq,
    one_mul]

noncomputable def pairDistribution (k : ℕ) (p : Fin 3 → ℝ) (w : Fin 3 × Fin 3) : ℝ :=
  if w.1.val + w.2.val = k then p w.1 else 0

theorem pairDistribution_sum_map (k : ℕ) (p : Fin 3 → ℝ)
    (hsupport : ∀ a, p a ≠ 0 → ∃ b : Fin 3, a.val + b.val = k)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ w : Fin 3 × Fin 3, f (pairDistribution k p w)) = ∑ a, f (p a) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : p a = 0
  · simp [pairDistribution,ha,hf]
  · obtain ⟨b,hb⟩ := hsupport a ha
    rw [Finset.sum_eq_single b]
    · simp [pairDistribution,hb]
    · intro c _ hc
      have hn : a.val + c.val ≠ k := by
        intro he
        have hv : c.val = b.val := by omega
        exact hc (Fin.ext hv)
      simp [pairDistribution,hn,hf]
    · simp

theorem pairDistribution_entropy (k : ℕ) (p : Fin 3 → ℝ)
    (hsupport : ∀ a, p a ≠ 0 → ∃ b : Fin 3, a.val + b.val = k) :
    entropy (pairDistribution k p) = entropy p :=
  pairDistribution_sum_map k p hsupport Real.negMulLog Real.negMulLog_zero

/-- Unnormalized mixture entropy, including a zero total weight. -/
theorem entropy_mixture_lower {C W : Type*} [Fintype C] [Fintype W]
    (a : C → ℝ) (p : C → W → ℝ) (ha : ∀ c, 0 ≤ a c)
    (hp : ∀ c w, 0 ≤ p c w) (hsum : ∀ c, ∑ w, p c w = 1) :
    Real.negMulLog (∑ c, a c) + ∑ c, a c * entropy (p c) ≤
      entropy (fun w ↦ ∑ c, a c * p c w) := by
  have h := MME.DWZB2Positivity.table_entropy_subadditivity
    (fun c w ↦ a c * p c w) (fun c w ↦ mul_nonneg (ha c) (hp c w))
  have hr (c : C) : ∑ w, a c * p c w = a c := by
    rw [← Finset.mul_sum, hsum, mul_one]
  simp only [hr] at h
  have he : (∑ c, entropy (fun w ↦ a c * p c w)) =
      entropy a + ∑ c, a c * entropy (p c) := by
    calc
      _ = ∑ c, (Real.negMulLog (a c) + a c * entropy (p c)) :=
        Finset.sum_congr rfl (fun c _ ↦ entropy_scale (p c) (hsum c) (a c))
      _ = _ := by rw [Finset.sum_add_distrib]; rfl
  simp only [entropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib] at he ⊢
  linarith

/-- A mixture remembers any common deterministic grade, so its entropy includes
the grade entropy in addition to the weighted entropy within each component. -/
theorem graded_mixture_entropy_lower {C W G : Type*}
    [Fintype C] [Fintype W] [Fintype G] [DecidableEq G]
    (a : C → ℝ) (p : C → W → ℝ) (cg : C → G) (wg : W → G)
    (ha : ∀ c, 0 ≤ a c) (hp : ∀ c w, 0 ≤ p c w)
    (hsum : ∀ c, ∑ w, p c w = 1)
    (hsupport : ∀ c w, wg w ≠ cg c → p c w = 0) :
    entropy (fun g ↦ ∑ c, if cg c = g then a c else 0) +
      ∑ c, a c * entropy (p c) ≤
      entropy (fun w ↦ ∑ c, a c * p c w) := by
  let ar (g : G) (c : C) := if cg c = g then a c else 0
  have har (g : G) (c : C) : 0 ≤ ar g c := by
    dsimp [ar]
    split_ifs <;> simp only [ha, le_refl]
  have hg (g : G) := entropy_mixture_lower (ar g) p (har g) hp hsum
  have h := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) ↦ hg g)
  have hleft : (∑ g, ∑ c, ar g c * entropy (p c)) =
      ∑ c, a c * entropy (p c) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    simp [ar, ite_mul]
  have hword (g : G) (w : W) : (∑ c, ar g c * p c w) =
      if wg w = g then ∑ c, a c * p c w else 0 := by
    by_cases hw : wg w = g
    · rw [if_pos hw]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : cg c = g
      · simp [ar,hc]
      · have hz : p c w = 0 := hsupport c w (by rw [hw]; exact Ne.symm hc)
        simp [ar,hc,hz]
    · rw [if_neg hw]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : cg c = g
      · have hz : p c w = 0 := hsupport c w (by rw [hc]; exact hw)
        simp [ar,hc,hz]
      · simp [ar,hc]
  have hright : (∑ g, entropy (fun w ↦ ∑ c, ar g c * p c w)) =
      entropy (fun w ↦ ∑ c, a c * p c w) := by
    simp only [entropy, hword]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_eq_single (wg w)]
    · simp
    · intro g _ hg
      simp [Ne.symm hg]
    · simp
  simp only [Finset.sum_add_distrib] at h
  rw [hleft, hright] at h
  exact h

end MME.DWZC2Exact125

end


section

open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MME.DWZC2Exact125

theorem negMulLog_lower_from_log (x q c : ℝ) (hx : 0 < x) (hxq : x ≤ q)
    (hlog : Real.log q ≤ -c) : c * x ≤ Real.negMulLog x := by
  have h := (Real.log_le_log hx hxq).trans hlog
  have hm := mul_le_mul_of_nonneg_left h hx.le
  simp only [Real.negMulLog_def]
  nlinarith

theorem log_cert_0 : Real.log (4996616998251 / 10000000000000 : ℝ) ≤ -(69382400988717 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4996616998251 / 10000000000000) (((4996616998251 / 10000000000000) * 2^2 - 1) / ((4996616998251 / 10000000000000) * 2^2 + 1)) (-34691200496359 / 50000000000000) (-69382400988717 / 100000000000000) 2 17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_1 : Real.log (20013532007 / 40000000000 : ℝ) ≤ -(34623540449541 / 50000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (20013532007 / 40000000000) (((20013532007 / 40000000000) * 2^1 - 1) / ((20013532007 / 40000000000) * 2^1 + 1)) (-69247080901083 / 100000000000000) (-34623540449541 / 50000000000000) 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_2 : Real.log (420960718793 / 1250000000000 : ℝ) ≤ -(10883593054769 / 10000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (420960718793 / 1250000000000) (((420960718793 / 1250000000000) * 2^2 - 1) / ((420960718793 / 1250000000000) * 2^2 + 1)) (-108835930551691 / 100000000000000) (-10883593054769 / 10000000000000) 2 10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_3 : Real.log (816184055341 / 2500000000000 : ℝ) ≤ -(55970306164537 / 50000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (816184055341 / 2500000000000) (((816184055341 / 2500000000000) * 2^2 - 1) / ((816184055341 / 2500000000000) * 2^2 + 1)) (-4477624493323 / 4000000000000) (-55970306164537 / 50000000000000) 2 9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_4 : Real.log (3367578028293 / 10000000000000 : ℝ) ≤ -(108839129295491 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (3367578028293 / 10000000000000) (((3367578028293 / 10000000000000) * 2^2 - 1) / ((3367578028293 / 10000000000000) * 2^2 + 1)) (-27209782324873 / 25000000000000) (-108839129295491 / 100000000000000) 2 10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_5 : Real.log (1950195713651 / 10000000000000 : ℝ) ≤ -(32693107189 / 20000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (1950195713651 / 10000000000000) (((1950195713651 / 10000000000000) * 2^3 - 1) / ((1950195713651 / 10000000000000) * 2^3 + 1)) (-81732767975501 / 50000000000000) (-32693107189 / 20000000000) 3 12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_6 : Real.log (6106139901 / 20000000000 : ℝ) ≤ -(118643746743017 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (6106139901 / 20000000000) (((6106139901 / 20000000000) * 2^2 - 1) / ((6106139901 / 20000000000) * 2^2 + 1)) (-59321873373509 / 50000000000000) (-118643746743017 / 100000000000000) 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_7 : Real.log (3046548237749 / 10000000000000 : ℝ) ≤ -(29714396714193 / 25000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (3046548237749 / 10000000000000) (((3046548237749 / 10000000000000) * 2^2 - 1) / ((3046548237749 / 10000000000000) * 2^2 + 1)) (-118857586860773 / 100000000000000) (-29714396714193 / 25000000000000) 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_8 : Real.log (975093049051 / 5000000000000 : ℝ) ≤ -(163466029001807 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (975093049051 / 5000000000000) (((975093049051 / 5000000000000) * 2^3 - 1) / ((975093049051 / 5000000000000) * 2^3 + 1)) (-2554156703247 / 1562500000000) (-163466029001807 / 100000000000000) 3 12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_9 : Real.log (1 / 2 : ℝ) ≤ -(13862943611 / 20000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (1 / 2) 0 (-69314718057 / 100000000000) (-13862943611 / 20000000000) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_10 : Real.log (4882814401 / 9765625000 : ℝ) ≤ -(69314679122527 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4882814401 / 9765625000) (((4882814401 / 9765625000) * 2^1 - 1) / ((4882814401 / 9765625000) * 2^1 + 1)) (-4332167445283 / 6250000000000) (-69314679122527 / 100000000000000) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_11 : Real.log (59544469769 / 312500000000 : ℝ) ≤ -(165788104467703 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (59544469769 / 312500000000) (((59544469769 / 312500000000) * 2^3 - 1) / ((59544469769 / 312500000000) * 2^3 + 1)) (-20723513059213 / 12500000000000) (-165788104467703 / 100000000000000) 3 12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_12 : Real.log (6189151422857 / 10000000000000 : ℝ) ≤ -(959574208153 / 2000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (6189151422857 / 10000000000000) (((6189151422857 / 10000000000000) * 2^1 - 1) / ((6189151422857 / 10000000000000) * 2^1 + 1)) (-47978710409651 / 100000000000000) (-959574208153 / 2000000000000) 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_13 : Real.log (1905425544537 / 10000000000000 : ℝ) ≤ -(82893986318637 / 50000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (1905425544537 / 10000000000000) (((1905425544537 / 10000000000000) * 2^3 - 1) / ((1905425544537 / 10000000000000) * 2^3 + 1)) (-6631518905731 / 4000000000000) (-82893986318637 / 50000000000000) 3 12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_14 : Real.log (3537220321 / 2500000000000 : ℝ) ≤ -(656070481211439 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (3537220321 / 2500000000000) (((3537220321 / 2500000000000) * 2^10 - 1) / ((3537220321 / 2500000000000) * 2^10 + 1)) (-8200881015393 / 1250000000000) (-656070481211439 / 100000000000000) 10 11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_15 : Real.log (249292788157 / 500000000000 : ℝ) ≤ -(34799001833133 / 50000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (249292788157 / 500000000000) (((249292788157 / 500000000000) * 2^2 - 1) / ((249292788157 / 500000000000) * 2^2 + 1)) (-69598003670267 / 100000000000000) (-34799001833133 / 50000000000000) 2 17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_16 : Real.log (2492923144211 / 5000000000000 : ℝ) ≤ -(34799096849189 / 50000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (2492923144211 / 5000000000000) (((2492923144211 / 5000000000000) * 2^2 - 1) / ((2492923144211 / 5000000000000) * 2^2 + 1)) (-69598193702379 / 100000000000000) (-34799096849189 / 50000000000000) 2 17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_17 : Real.log (3537266789 / 2500000000000 : ℝ) ≤ -(41004322970823 / 6250000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (3537266789 / 2500000000000) (((3537266789 / 2500000000000) * 2^10 - 1) / ((3537266789 / 2500000000000) * 2^10 + 1)) (-656069167553169 / 100000000000000) (-41004322970823 / 6250000000000) 10 11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_18 : Real.log (2500000840209 / 5000000000000 : ℝ) ≤ -(13862936889329 / 20000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (2500000840209 / 5000000000000) (((2500000840209 / 5000000000000) * 2^1 - 1) / ((2500000840209 / 5000000000000) * 2^1 + 1)) (-34657342224323 / 50000000000000) (-13862936889329 / 20000000000000) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_19 : Real.log (1638013826817 / 10000000000000 : ℝ) ≤ -(180910066628873 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (1638013826817 / 10000000000000) (((1638013826817 / 10000000000000) * 2^3 - 1) / ((1638013826817 / 10000000000000) * 2^3 + 1)) (-90455033317437 / 50000000000000) (-180910066628873 / 100000000000000) 3 9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_20 : Real.log (6723969611919 / 10000000000000 : ℝ) ≤ -(39690639679371 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (6723969611919 / 10000000000000) (((6723969611919 / 10000000000000) * 2^1 - 1) / ((6723969611919 / 10000000000000) * 2^1 + 1)) (-9922659920343 / 25000000000000) (-39690639679371 / 100000000000000) 1 10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_21 : Real.log (819008280633 / 5000000000000 : ℝ) ≤ -(11306868730759 / 6250000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (819008280633 / 5000000000000) (((819008280633 / 5000000000000) * 2^3 - 1) / ((819008280633 / 5000000000000) * 2^3 + 1)) (-36181979939629 / 20000000000000) (-11306868730759 / 6250000000000) 3 9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_22 : Real.log (1362678631 / 1000000000000 : ℝ) ≤ -(659830293459987 / 100000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (1362678631 / 1000000000000) (((1362678631 / 1000000000000) * 2^10 - 1) / ((1362678631 / 1000000000000) * 2^10 + 1)) (-164957573369997 / 25000000000000) (-659830293459987 / 100000000000000) 10 10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_23 : Real.log (1246594451949 / 2500000000000 : ℝ) ≤ -(8698441712723 / 12500000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (1246594451949 / 2500000000000) (((1246594451949 / 2500000000000) * 2^2 - 1) / ((1246594451949 / 2500000000000) * 2^2 + 1)) (-13917506741157 / 20000000000000) (-8698441712723 / 12500000000000) 2 17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_24 : Real.log (4986368440349 / 10000000000000 : ℝ) ≤ -(13917544312543 / 20000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4986368440349 / 10000000000000) (((4986368440349 / 10000000000000) * 2^2 - 1) / ((4986368440349 / 10000000000000) * 2^2 + 1)) (-17396930391679 / 25000000000000) (-13917544312543 / 20000000000000) 2 17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem log_cert_25 : Real.log (13626965547 / 10000000000000 : ℝ) ≤ -(329914489070083 / 50000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (13626965547 / 10000000000000) (((13626965547 / 10000000000000) * 2^10 - 1) / ((13626965547 / 10000000000000) * 2^10 + 1)) (-659828978160167 / 100000000000000) (-329914489070083 / 50000000000000) 10 10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

def rationalMarginal (r i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ s : Fin 6, if leftShape 0 s i = g then alpha r s else 0

noncomputable def baseMarginal (r i : Fin 3) (g : Fin 5) : ℝ :=
  ∑ s : Fin 6, if leftShape 0 s i = g then (alpha r s : ℝ) else 0

theorem baseMarginal_eq (r i : Fin 3) (g : Fin 5) :
    baseMarginal r i g = (rationalMarginal r i g : ℝ) := by
  simp only [baseMarginal,rationalMarginal,Rat.cast_sum,apply_ite,Rat.cast_zero]

theorem ent_0_0 : (6931469516508950385365943237 / 10000000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 0 0) := by
  have h0 : baseMarginal 0 0 0 = (249830849912531 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 0 0 = (249830849912531 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 0 0 1 = (250169150087469 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 0 1 = (250169150087469 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 0 0 2 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 0 2 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 0 0 3 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 0 3 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 0 0 4 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 0 4 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 0 0) = Real.negMulLog (249830849912531 / 500000000000000 : ℝ) + Real.negMulLog (250169150087469 / 500000000000000 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t0 := negMulLog_lower_from_log (249830849912531 / 500000000000000 : ℝ) (4996616998251 / 10000000000000 : ℝ) (69382400988717 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_0
  have t1 := negMulLog_lower_from_log (250169150087469 / 500000000000000 : ℝ) (20013532007 / 40000000000 : ℝ) (34623540449541 / 50000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_1
  simp only [Real.negMulLog_zero]
  norm_num at t0 t1 ⊢
  linarith

theorem ent_0_1 : (109850604457720368341043410843 / 100000000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 0 1) := by
  have h0 : baseMarginal 0 1 0 = (168384287517199 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 1 0 = (168384287517199 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 0 1 1 = (326473622136327 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 1 1 = (326473622136327 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 0 1 2 = (13470312113171 / 40000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 1 2 = (13470312113171 / 40000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 0 1 3 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 1 3 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 0 1 4 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 1 4 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 0 1) = Real.negMulLog (168384287517199 / 500000000000000 : ℝ) + Real.negMulLog (326473622136327 / 1000000000000000 : ℝ) + Real.negMulLog (13470312113171 / 40000000000000 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t0 := negMulLog_lower_from_log (168384287517199 / 500000000000000 : ℝ) (420960718793 / 1250000000000 : ℝ) (10883593054769 / 10000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_2
  have t1 := negMulLog_lower_from_log (326473622136327 / 1000000000000000 : ℝ) (816184055341 / 2500000000000 : ℝ) (55970306164537 / 50000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_3
  have t2 := negMulLog_lower_from_log (13470312113171 / 40000000000000 : ℝ) (3367578028293 / 10000000000000 : ℝ) (108839129295491 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_4
  simp only [Real.negMulLog_zero]
  norm_num at t0 t1 t2 ⊢
  linarith

theorem ent_0_2 : (136191199457801082740587056177 / 100000000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 0 2) := by
  have h0 : baseMarginal 0 2 0 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 2 0 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 0 2 1 = (195019571365019 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 2 1 = (195019571365019 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 0 2 2 = (305306995049943 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 2 2 = (305306995049943 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 0 2 3 = (38081852971859 / 125000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 2 3 = (38081852971859 / 125000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 0 2 4 = (97509304905083 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 0 2 4 = (97509304905083 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 0 2) = Real.negMulLog (0 : ℝ) + Real.negMulLog (195019571365019 / 1000000000000000 : ℝ) + Real.negMulLog (305306995049943 / 1000000000000000 : ℝ) + Real.negMulLog (38081852971859 / 125000000000000 : ℝ) + Real.negMulLog (97509304905083 / 500000000000000 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t1 := negMulLog_lower_from_log (195019571365019 / 1000000000000000 : ℝ) (1950195713651 / 10000000000000 : ℝ) (32693107189 / 20000000000 : ℝ) (by norm_num) (by norm_num) log_cert_5
  have t2 := negMulLog_lower_from_log (305306995049943 / 1000000000000000 : ℝ) (6106139901 / 20000000000 : ℝ) (118643746743017 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_6
  have t3 := negMulLog_lower_from_log (38081852971859 / 125000000000000 : ℝ) (3046548237749 / 10000000000000 : ℝ) (29714396714193 / 25000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_7
  have t4 := negMulLog_lower_from_log (97509304905083 / 500000000000000 : ℝ) (975093049051 / 5000000000000 : ℝ) (163466029001807 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_8
  simp only [Real.negMulLog_zero]
  norm_num at t1 t2 t3 t4 ⊢
  linarith

theorem ent_1_0 : (69314698588755921314755009951 / 100000000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 1 0) := by
  have h0 : baseMarginal 1 0 0 = (499999805337687 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 0 0 = (499999805337687 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 1 0 1 = (500000194662313 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 0 1 = (500000194662313 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 1 0 2 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 0 2 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 1 0 3 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 0 3 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 1 0 4 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 0 4 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 1 0) = Real.negMulLog (499999805337687 / 1000000000000000 : ℝ) + Real.negMulLog (500000194662313 / 1000000000000000 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t0 := negMulLog_lower_from_log (499999805337687 / 1000000000000000 : ℝ) (1 / 2 : ℝ) (13862943611 / 20000000000 : ℝ) (by norm_num) (by norm_num) log_cert_9
  have t1 := negMulLog_lower_from_log (500000194662313 / 1000000000000000 : ℝ) (4882814401 / 9765625000 : ℝ) (69314679122527 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_10
  simp only [Real.negMulLog_zero]
  norm_num at t0 t1 ⊢
  linarith

theorem ent_1_1 : (5804628841321039520380280021 / 6250000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 1 1) := by
  have h0 : baseMarginal 1 1 0 = (5954446976899 / 31250000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 1 0 = (5954446976899 / 31250000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 1 1 1 = (309457571142807 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 1 1 = (309457571142807 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 1 1 2 = (95271277226809 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 1 2 = (95271277226809 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 1 1 3 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 1 3 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 1 1 4 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 1 4 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 1 1) = Real.negMulLog (5954446976899 / 31250000000000 : ℝ) + Real.negMulLog (309457571142807 / 500000000000000 : ℝ) + Real.negMulLog (95271277226809 / 500000000000000 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t0 := negMulLog_lower_from_log (5954446976899 / 31250000000000 : ℝ) (59544469769 / 312500000000 : ℝ) (165788104467703 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_11
  have t1 := negMulLog_lower_from_log (309457571142807 / 500000000000000 : ℝ) (6189151422857 / 10000000000000 : ℝ) (959574208153 / 2000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_12
  have t2 := negMulLog_lower_from_log (95271277226809 / 500000000000000 : ℝ) (1905425544537 / 10000000000000 : ℝ) (82893986318637 / 50000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_13
  simp only [Real.negMulLog_zero]
  norm_num at t0 t1 t2 ⊢
  linarith

theorem ent_1_2 : (4453605834228924179690227429 / 6250000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 1 2) := by
  have h0 : baseMarginal 1 2 0 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 2 0 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 1 2 1 = (707444064181 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 2 1 = (707444064181 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 1 2 2 = (124646394078491 / 250000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 2 2 = (124646394078491 / 250000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 1 2 3 = (498584628842149 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 2 3 = (498584628842149 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 1 2 4 = (56596268621 / 40000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 1 2 4 = (56596268621 / 40000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 1 2) = Real.negMulLog (0 : ℝ) + Real.negMulLog (707444064181 / 500000000000000 : ℝ) + Real.negMulLog (124646394078491 / 250000000000000 : ℝ) + Real.negMulLog (498584628842149 / 1000000000000000 : ℝ) + Real.negMulLog (56596268621 / 40000000000000 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t1 := negMulLog_lower_from_log (707444064181 / 500000000000000 : ℝ) (3537220321 / 2500000000000 : ℝ) (656070481211439 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_14
  have t2 := negMulLog_lower_from_log (124646394078491 / 250000000000000 : ℝ) (249292788157 / 500000000000 : ℝ) (34799001833133 / 50000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_15
  have t3 := negMulLog_lower_from_log (498584628842149 / 1000000000000000 : ℝ) (2492923144211 / 5000000000000 : ℝ) (34799096849189 / 50000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_16
  have t4 := negMulLog_lower_from_log (56596268621 / 40000000000000 : ℝ) (3537266789 / 2500000000000 : ℝ) (41004322970823 / 6250000000000 : ℝ) (by norm_num) (by norm_num) log_cert_17
  simp only [Real.negMulLog_zero]
  norm_num at t1 t2 t3 t4 ⊢
  linarith

theorem ent_2_0 : (13862940250163370478447307291 / 20000000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 2 0) := by
  have h0 : baseMarginal 2 0 0 = (499999831958221 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 0 0 = (499999831958221 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 2 0 1 = (500000168041779 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 0 1 = (500000168041779 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 2 0 2 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 0 2 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 2 0 3 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 0 3 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 2 0 4 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 0 4 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 2 0) = Real.negMulLog (499999831958221 / 1000000000000000 : ℝ) + Real.negMulLog (500000168041779 / 1000000000000000 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t0 := negMulLog_lower_from_log (499999831958221 / 1000000000000000 : ℝ) (1 / 2 : ℝ) (13862943611 / 20000000000 : ℝ) (by norm_num) (by norm_num) log_cert_9
  have t1 := negMulLog_lower_from_log (500000168041779 / 1000000000000000 : ℝ) (2500000840209 / 5000000000000 : ℝ) (13862936889329 / 20000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_18
  simp only [Real.negMulLog_zero]
  norm_num at t0 t1 ⊢
  linarith

theorem ent_2_1 : (85954525742260446689229770991 / 100000000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 2 1) := by
  have h0 : baseMarginal 2 1 0 = (163801382681603 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 1 0 = (163801382681603 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 2 1 1 = (168099240297963 / 250000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 1 1 = (168099240297963 / 250000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 2 1 2 = (32760331225309 / 200000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 1 2 = (32760331225309 / 200000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 2 1 3 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 1 3 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 2 1 4 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 1 4 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 2 1) = Real.negMulLog (163801382681603 / 1000000000000000 : ℝ) + Real.negMulLog (168099240297963 / 250000000000000 : ℝ) + Real.negMulLog (32760331225309 / 200000000000000 : ℝ) + Real.negMulLog (0 : ℝ) + Real.negMulLog (0 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t0 := negMulLog_lower_from_log (163801382681603 / 1000000000000000 : ℝ) (1638013826817 / 10000000000000 : ℝ) (180910066628873 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_19
  have t1 := negMulLog_lower_from_log (168099240297963 / 250000000000000 : ℝ) (6723969611919 / 10000000000000 : ℝ) (39690639679371 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_20
  have t2 := negMulLog_lower_from_log (32760331225309 / 200000000000000 : ℝ) (819008280633 / 5000000000000 : ℝ) (11306868730759 / 6250000000000 : ℝ) (by norm_num) (by norm_num) log_cert_21
  simp only [Real.negMulLog_zero]
  norm_num at t0 t1 t2 ⊢
  linarith

theorem ent_2_2 : (71196258554730280345330499699 / 100000000000000000000000000000 : ℝ) ≤ entropy (baseMarginal 2 2) := by
  have h0 : baseMarginal 2 2 0 = (0 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 2 0 = (0 / 1 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h1 : baseMarginal 2 2 1 = (272535726189 / 200000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 2 1 = (272535726189 / 200000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h2 : baseMarginal 2 2 2 = (249318890389761 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 2 2 = (249318890389761 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h3 : baseMarginal 2 2 3 = (249318422017421 / 500000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 2 3 = (249318422017421 / 500000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have h4 : baseMarginal 2 2 4 = (1362696554691 / 1000000000000000 : ℝ) := by
    rw [baseMarginal_eq]
    have e : rationalMarginal 2 2 4 = (1362696554691 / 1000000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; ring
  have hs : entropy (baseMarginal 2 2) = Real.negMulLog (0 : ℝ) + Real.negMulLog (272535726189 / 200000000000000 : ℝ) + Real.negMulLog (249318890389761 / 500000000000000 : ℝ) + Real.negMulLog (249318422017421 / 500000000000000 : ℝ) + Real.negMulLog (1362696554691 / 1000000000000000 : ℝ) := by
    simp only [entropy, Fin.sum_univ_five, h0, h1, h2, h3, h4]
  rw [hs]
  have t1 := negMulLog_lower_from_log (272535726189 / 200000000000000 : ℝ) (1362678631 / 1000000000000 : ℝ) (659830293459987 / 100000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_22
  have t2 := negMulLog_lower_from_log (249318890389761 / 500000000000000 : ℝ) (1246594451949 / 2500000000000 : ℝ) (8698441712723 / 12500000000000 : ℝ) (by norm_num) (by norm_num) log_cert_23
  have t3 := negMulLog_lower_from_log (249318422017421 / 500000000000000 : ℝ) (4986368440349 / 10000000000000 : ℝ) (13917544312543 / 20000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_24
  have t4 := negMulLog_lower_from_log (1362696554691 / 1000000000000000 : ℝ) (13626965547 / 10000000000000 : ℝ) (329914489070083 / 50000000000000 : ℝ) (by norm_num) (by norm_num) log_cert_25
  simp only [Real.negMulLog_zero]
  norm_num at t1 t2 t3 t4 ⊢
  linarith

def coarseRotation : Fin 3 → Fin 3 → Fin 3 := ![![0,1,2],![1,2,0],![2,0,1]]

def coarseSwapXY : Fin 3 → Fin 3 := ![1,0,2]

noncomputable def sixModeRate (i : Fin 3) : ℝ :=
  ∑ r : Fin 3, (regionWeightCount r : ℝ)/1000000000000001/2 *
    (entropy (baseMarginal r (coarseRotation r i)) +
      entropy (baseMarginal r (coarseRotation r (coarseSwapXY i))))

/-- The two summands are precisely the actual rotated region and its X/Y swap;
each receives half the original regional weight. -/
theorem sixModeRate_actual_marginals (i : Fin 3) : sixModeRate i =
    ∑ r : Fin 3, (regionWeightCount r : ℝ)/1000000000000001/2 *
      ((∑ g : Fin 5, Real.negMulLog (∑ s : Fin 6,
          if leftShape r s i=g then (alpha r s:ℝ) else 0)) +
        (∑ g : Fin 5, Real.negMulLog (∑ s : Fin 6,
          if leftShape r s (coarseSwapXY i)=g then (alpha r s:ℝ) else 0))) := by
  have hrot : ∀ r s i, leftShape r s i=leftShape 0 s (coarseRotation r i) := by
    decide +kernel
  simp only [sixModeRate,entropy,baseMarginal]
  apply Finset.sum_congr rfl
  intro r _
  simp only [hrot r]

theorem sixModeRate_lower (i : Fin 3) :
    (383836115467 / 500000000000 : ℝ) < sixModeRate i := by
  have e00 := ent_0_0
  have e01 := ent_0_1
  have e02 := ent_0_2
  have e10 := ent_1_0
  have e11 := ent_1_1
  have e12 := ent_1_2
  have e20 := ent_2_0
  have e21 := ent_2_1
  have e22 := ent_2_2
  fin_cases i <;>
    norm_num [sixModeRate,Fin.sum_univ_succ,regionWeightCount,coarseRotation,
      coarseSwapXY,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff] <;>
    linarith only [e00, e01, e02, e10, e11, e12, e20, e21, e22]

end MME.DWZC2Exact125

end



section

open BigOperators MME.RecursiveThinSplit MME.DWZC2Exact125
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace MME.DWZC2CoarseCounts125

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def mode : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2],![1,0,2],![0,1,2],![1,0,2],![0,1,2],![1,0,2]]
def parent : Fin 6 → Fin 3 → ℕ :=
  ![![1,2,5],![2,1,5],![2,5,1],![5,2,1],![5,1,2],![1,5,2]]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def shape (c : Fin 6) (s : Fin 6) (i : Fin 3) : Fin 5 :=
  leftShape (region c) s (mode c i)

/-- `permObj sigma` takes physical mode i from original mode sigma.symm i. -/
def sigma : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, MME.swapFirstTwoPerm,
    MME.cyclicPerm.symm, MME.cyclicPerm.symm.trans MME.swapFirstTwoPerm,
    MME.cyclicPerm, MME.cyclicPerm.trans MME.swapFirstTwoPerm]

theorem shape_perm_original : ∀ c s i,
    shape c s i = leftShape 0 s ((sigma c).symm i) := by decide +kernel

theorem parent_perm_original : ∀ c i,
    parent c i = (![1,2,5] : Fin 3 → ℕ) ((sigma c).symm i) := by decide +kernel

theorem sigma_original_Z : ∀ c, sigma c 2 = keptMode c := by decide +kernel

theorem original_shape_from_physical (c : Fin 6) (s : Fin 6) (i : Fin 3) :
    shape c s (sigma c i) = leftShape 0 s i := by
  rw [shape_perm_original, Equiv.symm_apply_apply]

theorem shape_split : ∀ c s,
    (shape c s 0).val + (shape c s 1).val + (shape c s 2).val = 4 ∧
      ∀ i, (shape c s i).val ≤ parent c i := by
  decide +kernel

def splitMap (c : Fin 6) (s : Fin 6) : MME.RecursiveThinSplit.Split 4 (parent c) :=
  ⟨shape c s, shape_split c s⟩

theorem splitMap_bijective : ∀ c, Function.Bijective (splitMap c) := by
  decide +kernel

noncomputable def splitEquiv (c : Fin 6) : Fin 6 ≃ MME.RecursiveThinSplit.Split 4 (parent c) :=
  Equiv.ofBijective (splitMap c) (splitMap_bijective c)

theorem splitEquiv_val (c : Fin 6) (s : Fin 6) :
    (splitEquiv c s).val = shape c s := rfl

noncomputable def counts (c : Fin 6) (a : MME.RecursiveThinSplit.Split 4 (parent c)) : ℕ :=
  regionWeightCount (region c) * alphaCount (region c) ((splitEquiv c).symm a)

def length (c : Fin 6) : ℕ := regionWeightCount (region c) * 1000000000000000

theorem counts_splitEquiv (c : Fin 6) (s : Fin 6) :
    counts c (splitEquiv c s) = regionWeightCount (region c) * alphaCount (region c) s := by
  simp only [counts, Equiv.symm_apply_apply]

theorem alphaCount_sum : ∀ r, (∑ s, alphaCount r s) = 1000000000000000 := by
  decide +kernel

theorem counts_mass (c : Fin 6) : (∑ a, counts c a) = length c := by
  rw [← (splitEquiv c).sum_comp (counts c)]
  simp only [counts_splitEquiv, ← Finset.mul_sum, alphaCount_sum, length]

theorem total_mass : (∑ c, length c) = 2000000000000002000000000000000 := by
  decide +kernel

theorem total_mass_pos : 0 < ∑ c, length c := by rw [total_mass]; norm_num

theorem parent_total : ∀ c, parent c 0 + parent c 1 + parent c 2 = 8 := by
  decide +kernel

theorem parent_thin : ∀ c, ∃ i, parent c i ≤ 1 := by decide +kernel

theorem complementary_shape : ∀ c s i,
    (shape c s i).val + (shape c (Fin.rev s) i).val = parent c i := by
  decide +kernel

theorem right_supported (c : Fin 6) (a : MME.RecursiveThinSplit.Split 4 (parent c)) (i : Fin 3) :
    parent c i - (a.val i).val ≤ 4 := by
  obtain ⟨s, rfl⟩ := (splitEquiv c).surjective a
  have h := complementary_shape c s i
  have hb := (shape c (Fin.rev s) i).isLt
  simp only [splitEquiv_val] at *
  omega

theorem marginal_counts (c : Fin 6) (i : Fin 3) (j : Fin 5) :
    DWZC1CoarseCounts.marginal (counts c) i j =
      regionWeightCount (region c) *
        ∑ s : Fin 6, if shape c s i = j then alphaCount (region c) s else 0 := by
  have he := (splitEquiv c).sum_comp
    (fun a ↦ if a.val i = j then counts c a else 0)
  have hf : (∑ a : {a : MME.RecursiveThinSplit.Split 4 (parent c) // a.val i = j}, counts c a.val) =
      ∑ a : MME.RecursiveThinSplit.Split 4 (parent c), if a.val i = j then counts c a else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun a : MME.RecursiveThinSplit.Split 4 (parent c) ↦ a.val i = j)
      (Finset.univ.filter (fun a : MME.RecursiveThinSplit.Split 4 (parent c) ↦ a.val i = j))
      (by intro a; simp) (counts c)).symm
  rw [DWZC1CoarseCounts.marginal, hf, ← he]
  simp only [counts_splitEquiv, splitEquiv_val, Finset.mul_sum, mul_ite, mul_zero]

theorem retained_shape : ∀ c s,
    shape c s (keptMode c) = leftShape 0 s 2 := by decide +kernel

theorem regionalProfile_count : ∀ r j,
    (DWZPositiveComponent125.regionalProfile r).count j = originalRegionalCounts r j := by
  decide +kernel

theorem retained_original_profile (c : Fin 6) (j : Fin 5) :
    DWZC1CoarseCounts.marginal (counts c) (keptMode c) j =
      (DWZPositiveComponent125.regionalProfile (region c)).count j * regionWeightCount (region c) := by
  rw [marginal_counts]
  simp only [retained_shape]
  rw [original_parent_counts_preserved.1, regionalProfile_count]
  exact Nat.mul_comm _ _

theorem original_profile_length (c : Fin 6) :
    length c = (DWZPositiveComponent125.regionalProfile (region c)).length
      (regionWeightCount (region c)) := by
  have hd : ∀ r, (DWZPositiveComponent125.regionalProfile r).denominator =
      1000000000000000 := by decide +kernel
  simp only [length, DWZRestrictedValue.IntegerZSplitProfile.length, hd, Nat.mul_comm]

theorem scaled_counts_mass (t : ℕ) (c : Fin 6) :
    (∑ a, DWZC1CoarseCounts.scaled counts t c a) = length c * t := by
  simp only [DWZC1CoarseCounts.scaled, ← Finset.sum_mul, counts_mass]

theorem scaled_total_mass (t : ℕ) :
    (∑ c, length c * t) = 2000000000000002000000000000000 * t := by
  rw [← Finset.sum_mul, total_mass]

theorem scaled_retained_original_profile (t : ℕ) (c : Fin 6) (j : Fin 5) :
    DWZC1CoarseCounts.marginal (DWZC1CoarseCounts.scaled counts t c) (keptMode c) j =
      (DWZPositiveComponent125.regionalProfile (region c)).count j *
        (regionWeightCount (region c) * t) := by
  rw [DWZC1CoarseCounts.marginal_scaled, retained_original_profile, Nat.mul_assoc]

theorem scaled_original_profile_length (t : ℕ) (c : Fin 6) :
    length c * t = (DWZPositiveComponent125.regionalProfile (region c)).length
      (regionWeightCount (region c) * t) := by
  rw [original_profile_length]
  simp only [DWZRestrictedValue.IntegerZSplitProfile.length, Nat.mul_assoc]

theorem original_coordinate (c : Fin 6) (a : MME.RecursiveThinSplit.Split 4 (parent c))
    (i : Fin 3) :
    leftShape 0 ((splitEquiv c).symm a) i = a.val (sigma c i) := by
  obtain ⟨s, rfl⟩ := (splitEquiv c).surjective a
  simp only [Equiv.symm_apply_apply, splitEquiv_val, original_shape_from_physical]

theorem target_split_index_count (t : ℕ)
    (a : MME.RecursiveXHash.Address 4 6 parent (fun c ↦ length c * t))
    (ha : a ∈ MME.RecursiveXHash.target (DWZC1CoarseCounts.scaled counts t))
    (c : Fin 6) (s : Fin 6) :
    (Finset.univ.filter (fun v ↦ (splitEquiv c).symm (a c v) = s)).card =
      regionWeightCount (region c) * alphaCount (region c) s * t := by
  have h := (Finset.mem_filter.mp ha).2 c (splitEquiv c s)
  simpa only [MME.RecursiveThinSplit.HasJointCounts, MME.RecursiveThinSplit.count,
    Equiv.symm_apply_eq, DWZC1CoarseCounts.scaled, counts_splitEquiv] using h

theorem aggregate_original_profile (j : Fin 5) :
    (∑ c, DWZC1CoarseCounts.marginal (counts c) (keptMode c) j) =
      2 * DWZPositiveComponent125.parentProfile.count j := by
  simp only [retained_original_profile, regionalProfile_count]
  have h : ∀ g : Fin 5,
      (∑ c : Fin 6, originalRegionalCounts (region c) g * regionWeightCount (region c)) =
        2 * DWZPositiveComponent125.parentProfile.count g := by decide +kernel
  exact h j

theorem scaled_aggregate_original_profile (t : ℕ) (j : Fin 5) :
    (∑ c, DWZC1CoarseCounts.marginal (DWZC1CoarseCounts.scaled counts t c) (keptMode c) j) =
      DWZPositiveComponent125.parentProfile.count j * (2 * t) := by
  simp only [DWZC1CoarseCounts.marginal_scaled, ← Finset.sum_mul, aggregate_original_profile]
  ring

end MME.DWZC2CoarseCounts125

end


section

open BigOperators MME MME.TensorObj MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

namespace MME.DWZC1LiteralChildExtraction

open DWZC2CoarseCounts125 DWZC2Exact125

abbrev Addr (t : ℕ) := Address 4 6 parent (fun c ↦ length c * t)

def profile (c : Fin 6) := DWZPositiveComponent125.regionalProfile (region c)
def scale (t : ℕ) (c : Fin 6) := regionWeightCount (region c) * t
def size (t : ℕ) (c : Fin 6) := (profile c).length (scale t c)

def toPhysical (t : ℕ) (c : Fin 6) : Fin (size t c) ≃ Fin (length c * t) :=
  finCongr (scaled_original_profile_length t c).symm

noncomputable def label (t : ℕ) (a : Addr t) (c : Fin 6) (v : Fin (size t c)) : Fin 6 :=
  (DWZC2CoarseCounts125.splitEquiv c).symm (a c (toPhysical t c v))

noncomputable def left (t : ℕ) (a : Addr t) (c : Fin 6)
    (v : Fin (size t c)) : Fin 3 → Fin 5 := leftShape 0 (label t a c v)

noncomputable def right (t : ℕ) (a : Addr t) (c : Fin 6)
    (v : Fin (size t c)) : Fin 3 → Fin 5 := leftShape 0 (Fin.rev (label t a c v))

theorem left_physical (t : ℕ) (a : Addr t) (c : Fin 6) (v : Fin (size t c)) (i : Fin 3) :
    left t a c v i = (a c (toPhysical t c v)).val (sigma c i) :=
  original_coordinate c (a c (toPhysical t c v)) i

theorem child_sum (t : ℕ) (a : Addr t) (c : Fin 6) (v : Fin (size t c)) (i : Fin 3) :
    (left t a c v i).val + (right t a c v i).val = (cwFourthBlockType 1 2 5 i).val := by
  have h : ∀ s : Fin 6, ∀ i : Fin 3,
      (leftShape 0 s i).val + (leftShape 0 (Fin.rev s) i).val =
        (cwFourthBlockType 1 2 5 i).val := by decide +kernel
  exact h (label t a c v) i

theorem original_profile (t : ℕ) (a : Addr t)
    (ha : a ∈ target (DWZC1CoarseCounts.scaled counts t))
    (c : Fin 6) (g : Fin 5) :
    (Finset.univ.filter (fun v : Fin (size t c) ↦ left t a c v 2 = g)).card =
      (profile c).count g * scale t c := by
  have haA := (mme_recursive_x_hash_family_counts 4 6 parent (fun c ↦ length c*t)
    (DWZC1CoarseCounts.scaled counts t)).1 ha
  have hcount := (Finset.mem_filter.mp haA).2 c (keptMode c) g
  change RecursiveThinSplit.count (fun v ↦ (a c v).val (keptMode c)) g = _ at hcount
  have hc : (Finset.univ.filter (fun v : Fin (size t c) ↦ left t a c v 2 = g)).card =
      (Finset.univ.filter (fun v : Fin (length c*t) ↦ (a c v).val (keptMode c) = g)).card := by
    apply Finset.card_bij (fun v _ ↦ toPhysical t c v)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      simpa only [left_physical, sigma_original_Z] using hv
    · intro v _ w _ h
      exact (toPhysical t c).injective h
    · intro v hv
      refine ⟨(toPhysical t c).symm v, ?_, (toPhysical t c).apply_symm_apply v⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      simpa only [left_physical, sigma_original_Z, Equiv.apply_symm_apply] using hv
  exact hc.trans (hcount.trans (scaled_retained_original_profile t c g))

theorem label_count (t : ℕ) (a : Addr t)
    (ha : a ∈ target (DWZC1CoarseCounts.scaled counts t)) (c : Fin 6) (s : Fin 6) :
    (Finset.univ.filter (fun v : Fin (size t c) ↦ label t a c v = s)).card =
      regionWeightCount (region c) * alphaCount (region c) s * t := by
  have hc : (Finset.univ.filter (fun v : Fin (size t c) ↦ label t a c v = s)).card =
      (Finset.univ.filter (fun v : Fin (length c*t) ↦
        (DWZC2CoarseCounts125.splitEquiv c).symm (a c v) = s)).card := by
    apply Finset.card_bij (fun v _ ↦ toPhysical t c v)
    · intro v hv
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, label] using hv
    · intro v _ w _ h
      exact (toPhysical t c).injective h
    · intro v hv
      refine ⟨(toPhysical t c).symm v, ?_, (toPhysical t c).apply_symm_apply v⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, label,
        Equiv.apply_symm_apply] using hv
  exact hc.trans (target_split_index_count t a ha c s)

theorem induced_original (t k : ℕ) (a : Fin k → Addr t)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ c v, ((a (js 0) c v).val 0).val + ((a (js 1) c v).val 1).val +
        ((a (js 2) c v).val 2).val = 4) → ∃ j, js = fun _ ↦ j) :
    ∀ js : Fin 3 → Fin k,
      (∀ c v, (left t (a (js (sigma c 0))) c v 0).val +
        (left t (a (js (sigma c 1))) c v 1).val +
        (left t (a (js (sigma c 2))) c v 2).val = 4) →
      ∃ j, js = fun _ ↦ j := by
  intro js hs
  apply hInduced js
  intro c v
  have h := hs c ((toPhysical t c).symm v)
  simp only [left_physical, Equiv.apply_symm_apply] at h
  let f := fun i : Fin 3 ↦ ((a (js i) c v).val i).val
  calc
    _ = ∑ i, f i := by simp [f, Fin.sum_univ_succ, Nat.add_assoc]
    _ = ∑ i, f (sigma c i) := (Equiv.sum_comp (sigma c) f).symm
    _ = 4 := by simpa [f, Fin.sum_univ_succ, Nat.add_assoc] using h

theorem indexed_family_restrict {K : Type u} [Field K] (q t k : ℕ)
    (a : Fin k → Addr t)
    (ha : ∀ j, a j ∈ target (DWZC1CoarseCounts.scaled counts t))
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ c v, ((a (js 0) c v).val 0).val + ((a (js 1) c v).val 1).val +
        ((a (js 2) c v).val 2).val = 4) → ∃ j, js = fun _ ↦ j) :
    TensorObj.Restrict
      (bigAdd (fun j : Fin k ↦ kronFin 6 (fun c ↦ permObj (sigma c)
        (DWZC1SimultaneousChild.regionTarget q (size t c) (left t (a j) c) (right t (a j) c)))))
      (kronFin 6 (fun c ↦ permObj (sigma c)
        (DWZC1SimultaneousChild.regionSource (K := K) q 1 2 5 (profile c) (scale t c)))) := by
  exact DWZC1SimultaneousChild.simultaneous_regional_restrict q 6 k
    (fun _ ↦ 1) (fun _ ↦ 2) (fun _ ↦ 5) profile (scale t) sigma
    (fun j ↦ left t (a j)) (fun j ↦ right t (a j))
    (fun j ↦ child_sum t (a j)) (fun j ↦ original_profile t (a j) (ha j))
    (induced_original t k a hInduced)

theorem retained_family_restrict {K : Type u} [Field K] (q t : ℕ)
    (kept : Finset (Addr t))
    (hkept : kept ⊆ target (DWZC1CoarseCounts.scaled counts t))
    (hInduced : ∀ x ∈ kept, ∀ y ∈ kept, ∀ z ∈ kept,
      (∀ c v, ((x c v).val 0).val + ((y c v).val 1).val + ((z c v).val 2).val = 4) →
      x = y ∧ y = z)
    (e : Fin kept.card ≃ ↥kept) :
    TensorObj.Restrict
      (bigAdd (fun j : Fin kept.card ↦ kronFin 6 (fun c ↦ permObj (sigma c)
        (DWZC1SimultaneousChild.regionTarget q (size t c)
          (left t (e j).val c) (right t (e j).val c)))))
      (kronFin 6 (fun c ↦ permObj (sigma c)
        (DWZC1SimultaneousChild.regionSource (K := K) q 1 2 5 (profile c) (scale t c)))) := by
  apply indexed_family_restrict q t kept.card (fun j ↦ (e j).val)
    (fun j ↦ hkept (e j).property)
  intro js hs
  obtain ⟨h01,h12⟩ := hInduced (e (js 0)).val (e (js 0)).property
    (e (js 1)).val (e (js 1)).property (e (js 2)).val (e (js 2)).property hs
  have h01' : js 0 = js 1 := e.injective (Subtype.ext h01)
  have h12' : js 1 = js 2 := e.injective (Subtype.ext h12)
  refine ⟨js 0, ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact h01'.symm
  · exact (h01'.trans h12').symm

end MME.DWZC1LiteralChildExtraction

end


section

open BigOperators MME.DWZC2Exact125
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace MME.DWZC2CoarseCounts125

noncomputable def normalizedMarginal (c : Fin 6) (i : Fin 3) (j : Fin 5) : ℝ :=
  ∑ s : Fin 6, if shape c s i = j then (alpha (region c) s : ℝ) else 0

theorem normalizedMarginal_sum (c : Fin 6) (i : Fin 3) :
    (∑ j, normalizedMarginal c i j) = 1 := by
  simp only [normalizedMarginal]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact_mod_cast exact_finite_data.2.1 (region c)

theorem weighted_alpha (c : Fin 6) (s : Fin 6) :
    (regionWeightCount (region c) : ℝ) * (alphaCount (region c) s : ℝ) =
      (length c : ℝ) * (alpha (region c) s : ℝ) := by
  simp only [length, alpha, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

theorem marginal_normalized (c : Fin 6) (i : Fin 3) (j : Fin 5) :
    (DWZC1CoarseCounts.marginal (counts c) i j : ℝ) =
      (length c : ℝ) * normalizedMarginal c i j := by
  rw [marginal_counts]
  simp only [normalizedMarginal, Nat.cast_mul, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact weighted_alpha c s
  · simp

theorem entropyMass_eq_length_entropy
    {A : Type*} [Fintype A] (m : A → ℕ) (p : A → ℝ) (N : ℕ)
    (hp : ∑ a, p a = 1) (hm : ∀ a, (m a : ℝ) = (N : ℝ) * p a) :
    DWZC1CoarseCounts.entropyMass m = (N : ℝ) * entropy p := by
  have hsum : ((∑ a, m a : ℕ) : ℝ) = N := by
    rw [Nat.cast_sum]
    simp only [hm, ← Finset.mul_sum, hp, mul_one]
  have hfun : (fun a ↦ (m a : ℝ)) = fun a ↦ (N : ℝ) * p a := funext hm
  have he := entropy_scale p hp (N : ℝ)
  rw [← hfun] at he
  simp only [entropy, Real.negMulLog_def, neg_mul, Finset.sum_neg_distrib] at he
  unfold DWZC1CoarseCounts.entropyMass
  rw [hsum]
  simp only [entropy, Real.negMulLog_def, neg_mul, Finset.sum_neg_distrib]
  linarith

theorem regional_marginal_entropy (c : Fin 6) (i : Fin 3) :
    DWZC1CoarseCounts.entropyMass (DWZC1CoarseCounts.marginal (counts c) i) =
      (length c : ℝ) * entropy (normalizedMarginal c i) :=
  entropyMass_eq_length_entropy _ _ _ (normalizedMarginal_sum c i)
    (marginal_normalized c i)

private theorem sum_six (f : Fin 6 → ℝ) :
    (∑ c, f c) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ring

theorem blockEntropy_sixModeRate (i : Fin 3) :
    DWZC1CoarseCounts.blockEntropy counts i =
      2000000000000002000000000000000 * sixModeRate i := by
  unfold DWZC1CoarseCounts.blockEntropy
  simp only [regional_marginal_entropy]
  rw [sum_six, sixModeRate_actual_marginals, Fin.sum_univ_three]
  let F (r : Fin 3) (h : Fin 3) : ℝ :=
    ∑ g : Fin 5, Real.negMulLog (∑ s : Fin 6,
      if leftShape r s h = g then (alpha r s : ℝ) else 0)
  have h0 : entropy (normalizedMarginal 0 i) = F 0 i := by fin_cases i <;> rfl
  have h1 : entropy (normalizedMarginal 1 i) = F 0 (coarseSwapXY i) := by fin_cases i <;> rfl
  have h2 : entropy (normalizedMarginal 2 i) = F 1 i := by fin_cases i <;> rfl
  have h3 : entropy (normalizedMarginal 3 i) = F 1 (coarseSwapXY i) := by fin_cases i <;> rfl
  have h4 : entropy (normalizedMarginal 4 i) = F 2 i := by fin_cases i <;> rfl
  have h5 : entropy (normalizedMarginal 5 i) = F 2 (coarseSwapXY i) := by fin_cases i <;> rfl
  rw [h0, h1, h2, h3, h4, h5]
  change
    ((regionWeightCount 0 * 1000000000000000 : ℕ) : ℝ) * F 0 i +
    ((regionWeightCount 0 * 1000000000000000 : ℕ) : ℝ) * F 0 (coarseSwapXY i) +
    ((regionWeightCount 1 * 1000000000000000 : ℕ) : ℝ) * F 1 i +
    ((regionWeightCount 1 * 1000000000000000 : ℕ) : ℝ) * F 1 (coarseSwapXY i) +
    ((regionWeightCount 2 * 1000000000000000 : ℕ) : ℝ) * F 2 i +
    ((regionWeightCount 2 * 1000000000000000 : ℕ) : ℝ) * F 2 (coarseSwapXY i) =
      2000000000000002000000000000000 *
        ((regionWeightCount 0 : ℝ) / 1000000000000001 / 2 * (F 0 i + F 0 (coarseSwapXY i)) +
          (regionWeightCount 1 : ℝ) / 1000000000000001 / 2 * (F 1 i + F 1 (coarseSwapXY i)) +
          (regionWeightCount 2 : ℝ) / 1000000000000001 / 2 * (F 2 i + F 2 (coarseSwapXY i)))
  push_cast
  ring

theorem blockEntropy_positive (i : Fin 3) :
    0 < DWZC1CoarseCounts.blockEntropy counts i := by
  rw [blockEntropy_sixModeRate]
  have h := sixModeRate_lower i
  positivity

theorem blockEntropy_floor (i : Fin 3) :
    2000000000000002000000000000000 * (383836115467 / 500000000000 : ℝ) <
      DWZC1CoarseCounts.blockEntropy counts i := by
  rw [blockEntropy_sixModeRate]
  exact mul_lt_mul_of_pos_left (sixModeRate_lower i) (by norm_num)

end MME.DWZC2CoarseCounts125

end


section

open BigOperators MME MME.TensorObj
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1Orientation

theorem cyclic_kronFin_isomorphic {K : Type u} [Field K] {n : ℕ}
    (A : Fin n → TensorObj K 3) :
    Isomorphic (cyclicSymmetrization (kronFin n A))
      (kronFin n (fun r ↦ cyclicSymmetrization (A r))) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    mme_toQ_kronFin, ← TensorQ.permAut_toQ, map_prod, Finset.prod_mul_distrib]

/-- Apply the mode rotations to the projected tensor itself, so its prescribed
Z filter is transported to the corresponding mode without changing its profile. -/
noncomputable def regionRotation {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) : Fin 3 → TensorObj K 3 :=
  ![A 0, permObj cyclicPerm (A 1),
    permObj (cyclicPerm.trans cyclicPerm) (A 2)]

noncomputable def asymmetricRegionalTensor {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) : TensorObj K 3 :=
  kronFin 3 (fun r ↦ kron (regionRotation A r)
    (permObj swapFirstTwoPerm (regionRotation A r)))

theorem rotated_six_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) (r : Fin 3) :
    Isomorphic (sixSymmetrization (regionRotation A r)) (sixSymmetrization (A r)) := by
  fin_cases r
  · exact Isomorphic.refl _
  · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit (A 1)).1
  · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit (A 2)).2

/-- Claims 7.2--7.3's six-region rearrangement, before extraction of child tensors. -/
theorem asymmetric_cyclic_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) :
    Isomorphic (cyclicSymmetrization (asymmetricRegionalTensor A))
      (sixSymmetrization (kronFin 3 A)) := by
  apply Isomorphic.trans (cyclic_kronFin_isomorphic _)
  apply Isomorphic.trans _ (mme_sixSymmetrization_kronFin_isomorphic A)
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  apply Finset.prod_congr rfl
  intro r _
  apply TensorQ.toQ_eq_iff.mpr
  exact (mme_sixSymmetrization_isomorphic_cyclic_paired_swap
    (regionRotation A r)).symm.trans (rotated_six_isomorphic A r)

theorem asymmetric_regional_restrict {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) (T : TensorObj K 3)
    (h : TensorObj.Restrict (kronFin 3 A) T) :
    TensorObj.Restrict (cyclicSymmetrization (asymmetricRegionalTensor A)) (sixSymmetrization T) :=
  (asymmetric_cyclic_isomorphic A).1.trans (mme_sixSymmetrization_restrict h)

open MME.DWZRestrictedValue MME.DWZComponentRestriction
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent125

theorem original125_asymmetric_restrict {K : Type u} [Field K] (q m : ℕ) :
    let A := fun r : Fin 3 ↦ prescribedZPower
      (cwFourthConstituent K q 1 2 5) (constituentBasis K q 1 2 5 2)
      (fun a : LiftedCoarseCoordinate.{u} q 5 ↦ cwSquarePairGrade q a.down.val.1)
      (regionalProfile r) (regionalWeight r * m)
    TensorObj.Restrict (cyclicSymmetrization (asymmetricRegionalTensor A))
      (sixSymmetrization (prescribedZPower
        (cwFourthConstituent K q 1 2 5) (constituentBasis K q 1 2 5 2)
        (fun a : LiftedCoarseCoordinate.{u} q 5 ↦ cwSquarePairGrade q a.down.val.1)
        parentProfile m)) := by
  dsimp only
  exact asymmetric_regional_restrict _ _
    (mme_dwz_positive_125_original_profile_regional_restrict q m).2.2.2

end MME.DWZC1Orientation

end


section

open BigOperators MME MME.TensorObj
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace MME.DWZC1LiteralOrientation

theorem cyclic_square_eq_inverse : cyclicPerm.trans cyclicPerm = cyclicPerm.symm := by decide

/-- This order gives the literal regional shapes (see parent table). The inverse
cyclic rotation is applied to region1 without swapping its profile or weight. -/
noncomputable def regionRotation {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) : Fin 3 → TensorObj K 3 :=
  ![A 0, permObj cyclicPerm.symm (A 1), permObj cyclicPerm (A 2)]

noncomputable def asymmetricRegionalTensor {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) : TensorObj K 3 :=
  kronFin 3 (fun r ↦ kron (regionRotation A r)
    (permObj swapFirstTwoPerm (regionRotation A r)))

theorem rotated_six_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) (r : Fin 3) :
    Isomorphic (sixSymmetrization (regionRotation A r)) (sixSymmetrization (A r)) := by
  fin_cases r
  · exact Isomorphic.refl _
  · change Isomorphic (sixSymmetrization (permObj cyclicPerm.symm (A 1))) _
    rw [← cyclic_square_eq_inverse]
    exact (mme_sixSymmetrization_isomorphic_cyclic_orbit (A 1)).2
  · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit (A 2)).1

theorem asymmetric_cyclic_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) :
    Isomorphic (cyclicSymmetrization (asymmetricRegionalTensor A))
      (sixSymmetrization (kronFin 3 A)) := by
  apply Isomorphic.trans (MME.DWZC1Orientation.cyclic_kronFin_isomorphic _)
  apply Isomorphic.trans _ (mme_sixSymmetrization_kronFin_isomorphic A)
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  apply Finset.prod_congr rfl
  intro r _
  apply TensorQ.toQ_eq_iff.mpr
  exact (mme_sixSymmetrization_isomorphic_cyclic_paired_swap
    (regionRotation A r)).symm.trans (rotated_six_isomorphic A r)

open MME.DWZRestrictedValue MME.DWZComponentRestriction
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent125

theorem original125_asymmetric_restrict {K : Type u} [Field K] (q m : ℕ) :
    let A := fun r : Fin 3 ↦ prescribedZPower
      (cwFourthConstituent K q 1 2 5) (constituentBasis K q 1 2 5 2)
      (fun a : LiftedCoarseCoordinate.{u} q 5 ↦ cwSquarePairGrade q a.down.val.1)
      (regionalProfile r) (regionalWeight r * m)
    TensorObj.Restrict (cyclicSymmetrization (asymmetricRegionalTensor A))
      (sixSymmetrization (prescribedZPower
        (cwFourthConstituent K q 1 2 5) (constituentBasis K q 1 2 5 2)
        (fun a : LiftedCoarseCoordinate.{u} q 5 ↦ cwSquarePairGrade q a.down.val.1)
        parentProfile m)) := by
  dsimp only
  exact (asymmetric_cyclic_isomorphic _).1.trans
    (mme_sixSymmetrization_restrict
      (mme_dwz_positive_125_original_profile_regional_restrict q m).2.2.2)

end MME.DWZC1LiteralOrientation

end


section

open BigOperators Filter MME MME.TensorObj MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace MME.DWZC1LiteralAsymptotic

open DWZC2CoarseCounts125 DWZC2Exact125 DWZC1LiteralChildExtraction

theorem perm_refl_iso {K : Type u} [Field K] (T : TensorObj K 3) :
    Isomorphic (permObj (Equiv.refl _) T) T := by
  have ht : (permObj (Equiv.refl (Fin 3)) T).t = T.t := by
    change (PiTensorProduct.reindex K T.V (Equiv.refl _)) T.t = _
    rw [PiTensorProduct.reindex_refl]
    rfl
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    erw [PiTensorProduct.map_id]
    exact ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    erw [PiTensorProduct.map_id]
    exact ht

theorem perm_trans_iso {K : Type u} [Field K] (T : TensorObj K 3)
    (σ τ : Equiv.Perm (Fin 3)) :
    Isomorphic (permObj (σ.trans τ) T) (permObj τ (permObj σ T)) := by
  have ht : (permObj τ (permObj σ T)).t = (permObj (σ.trans τ) T).t := by
    exact PiTensorProduct.reindex_reindex σ τ T.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    erw [PiTensorProduct.map_id]
    exact ht
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    erw [PiTensorProduct.map_id]
    exact ht.symm

theorem six_region_iso {K : Type u} [Field K] (A : Fin 3 → TensorObj K 3) :
    Isomorphic (kronFin 6 (fun c ↦ permObj (sigma c) (A (region c))))
      (DWZC1LiteralOrientation.asymmetricRegionalTensor A) := by
  apply TensorQ.toQ_eq_iff.mp
  let B := fun c : Fin 6 ↦ permObj (sigma c) (A (region c))
  let C := DWZC1LiteralOrientation.regionRotation A
  have h0 : TensorQ.toQ (B 0) = TensorQ.toQ (C 0) :=
    TensorQ.toQ_eq_iff.mpr (perm_refl_iso (A 0))
  have h1 : TensorQ.toQ (B 1) = TensorQ.toQ (permObj swapFirstTwoPerm (C 0)) := rfl
  have h2 : TensorQ.toQ (B 2) = TensorQ.toQ (C 1) := rfl
  have h3 : TensorQ.toQ (B 3) = TensorQ.toQ (permObj swapFirstTwoPerm (C 1)) :=
    TensorQ.toQ_eq_iff.mpr (perm_trans_iso (A 1) cyclicPerm.symm swapFirstTwoPerm)
  have h4 : TensorQ.toQ (B 4) = TensorQ.toQ (C 2) := rfl
  have h5 : TensorQ.toQ (B 5) = TensorQ.toQ (permObj swapFirstTwoPerm (C 2)) :=
    TensorQ.toQ_eq_iff.mpr (perm_trans_iso (A 2) cyclicPerm swapFirstTwoPerm)
  change TensorQ.toQ (kronFin 6 B) = TensorQ.toQ
    (kronFin 3 (fun r ↦ kron (C r) (permObj swapFirstTwoPerm (C r))))
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  simp only [TensorQ.toQ_kron, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change TensorQ.toQ (B 0) * (TensorQ.toQ (B 1) * (TensorQ.toQ (B 2) *
    (TensorQ.toQ (B 3) * (TensorQ.toQ (B 4) * TensorQ.toQ (B 5))))) = _
  rw [h0,h1,h2,h3,h4,h5]
  change TensorQ.toQ (C 0) * (TensorQ.toQ (permObj swapFirstTwoPerm (C 0)) *
    (TensorQ.toQ (C 1) * (TensorQ.toQ (permObj swapFirstTwoPerm (C 1)) *
    (TensorQ.toQ (C 2) * TensorQ.toQ (permObj swapFirstTwoPerm (C 2)))))) =
    (TensorQ.toQ (C 0) * TensorQ.toQ (permObj swapFirstTwoPerm (C 0))) *
    ((TensorQ.toQ (C 1) * TensorQ.toQ (permObj swapFirstTwoPerm (C 1))) *
    (TensorQ.toQ (C 2) * TensorQ.toQ (permObj swapFirstTwoPerm (C 2))))
  ring

theorem kron_restrict {K : Type u} [Field K] {X X' Y Y' : TensorObj K 3}
    (hx : TensorObj.Restrict X X') (hy : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (kron X Y) (kron X' Y') := by
  obtain ⟨f,hf⟩ := hx
  obtain ⟨g,hg⟩ := hy
  refine ⟨fun i ↦ TensorProduct.map (f i) (g i), ?_⟩
  change PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (g i))
    (interchange X'.t Y'.t) = interchange X.t Y.t
  rw [TensorObj.TypeGrading.kronMap_interchange, hf, hg]

theorem cyclic_restrict {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (cyclicSymmetrization X) (cyclicSymmetrization Y) := by
  rw [cyclicSymmetrization_eq_public_perm, cyclicSymmetrization_eq_public_perm]
  exact kron_restrict h (kron_restrict (permObj_restrict cyclicPerm h)
    (permObj_restrict (cyclicPerm.trans cyclicPerm) h))

noncomputable def source {K : Type u} [Field K] (q t : ℕ) : TensorObj K 3 :=
  kronFin 6 (fun c ↦ permObj (sigma c)
    (DWZC1SimultaneousChild.regionSource q 1 2 5 (profile c) (scale t c)))

noncomputable def family {K : Type u} [Field K] (q t : ℕ)
    (kept : Finset (Addr t)) (e : Fin kept.card ≃ ↥kept) : TensorObj K 3 :=
  bigAdd (fun j : Fin kept.card ↦ kronFin 6 (fun c ↦ permObj (sigma c)
    (DWZC1SimultaneousChild.regionTarget q (size t c)
      (left t (e j).val c) (right t (e j).val c))))

noncomputable def original {K : Type u} [Field K] (q t : ℕ) : TensorObj K 3 :=
  prescribedZPower (cwFourthConstituent K q 1 2 5) (constituentBasis K q 1 2 5 2)
    (fun a : LiftedCoarseCoordinate.{u} q 5 ↦ cwSquarePairGrade q a.down.val.1)
    DWZPositiveComponent125.parentProfile t

theorem original_source_restrict {K : Type u} [Field K] (q t : ℕ) :
    TensorObj.Restrict (cyclicSymmetrization (source (K := K) q t))
      (sixSymmetrization (original q t)) := by
  let A := fun r : Fin 3 ↦ DWZC1SimultaneousChild.regionSource (K := K) q 1 2 5
    (DWZPositiveComponent125.regionalProfile r) (regionWeightCount r*t)
  have heq : source q t = kronFin 6 (fun c ↦ permObj (sigma c) (A (region c))) := rfl
  rw [heq]
  apply (cyclic_restrict (six_region_iso A).1).trans
  exact DWZC1LiteralOrientation.original125_asymmetric_restrict q t

theorem eventual_actual_child_families {K : Type u} [Field K] (q : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hupper : ρ ≤ 383836115467 / 500000000000) :
    ∀ᶠ t : ℕ in atTop,
      ∃ (kept : Finset (Addr t)) (e : Fin kept.card ≃ ↥kept),
        kept ⊆ target (DWZC1CoarseCounts.scaled counts t) ∧
        Real.exp (2000000000000002000000000000000 * ρ * (t : ℝ)) ≤ (kept.card : ℝ) ∧
        TensorObj.Restrict (family (K := K) q t kept e) (source q t) ∧
        TensorObj.Restrict (cyclicSymmetrization (family (K := K) q t kept e))
          (sixSymmetrization (original (K := K) q t)) := by
  classical
  have hsmall (i : Fin 3) : 2000000000000002000000000000000 * ρ <
      DWZC1CoarseCounts.blockEntropy counts i := by
    exact (mul_le_mul_of_nonneg_left hupper (by norm_num)).trans_lt (blockEntropy_floor i)
  have hgap := lt_min (lt_min (hsmall 0) (hsmall 1)) (hsmall 2)
  have h := mme_recursive_thin_regional_induced_families_below_marginal_rate
    6 parent parent_thin length counts counts_mass total_mass_pos
    (2000000000000002000000000000000 * ρ) (mul_nonneg (by norm_num) hρ) hgap
  filter_upwards [h] with t ht
  obtain ⟨kept,hkept,_hinj,hinduced,hcard⟩ := ht
  let e : Fin kept.card ≃ ↥kept := Fintype.equivOfCardEq (by simp)
  have hR : TensorObj.Restrict (family (K := K) q t kept e) (source q t) := by
    apply retained_family_restrict q t kept hkept _ e
    intro x hx y hy z hz hs
    obtain ⟨hxy,hyz⟩ := hinduced ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩ hs
    exact ⟨congrArg Subtype.val hxy, congrArg Subtype.val hyz⟩
  exact ⟨kept,e,hkept,hcard,hR,(cyclic_restrict hR).trans (original_source_restrict q t)⟩

end MME.DWZC1LiteralAsymptotic

end


section

open BigOperators MME MME.TensorObj
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace MME.DWZC1ChildGrouping

/-- Exact type grouping with both halves retained.  No symmetry of the
histogram is assumed: the exponent is the sum along the involution. -/
theorem paired_word_grouping {K : Type u} [Field K] {d N k : ℕ}
    (X : Fin k → TensorObj K d) (rev : Equiv.Perm (Fin k))
    (hrev : ∀ s, rev (rev s) = s)
    (w : Fin N → Fin k) (n : Fin k → ℕ)
    (hw : ∀ s, (Finset.univ.filter (fun v ↦ w v = s)).card = n s) :
    Isomorphic
      (kronFin N (fun v ↦ kron (X (w v)) (X (rev (w v)))))
      (kronFin k (fun s ↦ (X s).kronPow (n s + n (rev s)))) := by
  have hleft := mme_kronFin_group_by_exact_fibers_iso X w n
    (fun s ↦ by simpa only [Fintype.card_subtype] using hw s)
  have hright := mme_kronFin_group_by_exact_fibers_iso X (fun v ↦ rev (w v))
    (fun s ↦ n (rev s)) (fun s ↦ by
      have heq : (fun v ↦ rev (w v) = s) = (fun v ↦ w v = rev s) := by
        funext v
        apply propext
        constructor
        · intro h
          simpa only [hrev] using congrArg rev h
        · intro h
          rw [h, hrev]
      simpa only [Fintype.card_subtype, heq] using hw (rev s))
  apply TensorQ.toQ_eq_iff.mp
  simp only [mme_toQ_kronFin, TensorQ.toQ_kron, Finset.prod_mul_distrib]
  have hl := TensorQ.toQ_eq_iff.mpr hleft
  have hr := TensorQ.toQ_eq_iff.mpr hright
  simp only [mme_toQ_kronFin, TensorQ.toQ_kronPow] at hl hr
  rw [hl, hr, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  rw [TensorQ.toQ_kronPow, pow_add]

theorem perm_kronFin_isomorphic {K : Type u} [Field K] {d n : ℕ}
    (σ : Equiv.Perm (Fin d)) (X : Fin n → TensorObj K d) :
    Isomorphic (permObj σ (kronFin n X)) (kronFin n (fun s ↦ permObj σ (X s))) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [← TensorQ.permAut_toQ, mme_toQ_kronFin, map_prod]

theorem perm_kronPow_isomorphic {K : Type u} [Field K] {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (X : TensorObj K d) (n : ℕ) :
    Isomorphic (permObj σ (X.kronPow n)) ((permObj σ X).kronPow n) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [← TensorQ.permAut_toQ, TensorQ.toQ_kronPow, map_pow]

theorem cyclic_respects_isomorphic {K : Type u} [Field K]
    {X Y : TensorObj K 3} (h : Isomorphic X Y) :
    Isomorphic (cyclicSymmetrization X) (cyclicSymmetrization Y) := by
  apply TensorQ.toQ_eq_iff.mp
  have hq := TensorQ.toQ_eq_iff.mpr h
  simp only [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    ← TensorQ.permAut_toQ, hq]

theorem perm_trans_isomorphic {K : Type u} [Field K] {d : ℕ}
    (σ τ : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    Isomorphic (permObj (σ.trans τ) X) (permObj τ (permObj σ X)) := by
  have he : (permObj (σ.trans τ) X).t = (permObj τ (permObj σ X)).t := by
    change PiTensorProduct.reindex K X.V (σ.trans τ) X.t =
      PiTensorProduct.reindex K (fun i ↦ X.V (σ.symm i)) τ
        (PiTensorProduct.reindex K X.V σ X.t)
    exact (PiTensorProduct.reindex_reindex σ τ X.t).symm
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    change PiTensorProduct.map
      (fun i ↦ (LinearMap.id : X.V (σ.symm (τ.symm i)) →ₗ[K] X.V (σ.symm (τ.symm i))))
      (permObj τ (permObj σ X)).t = _
    exact (LinearMap.congr_fun (PiTensorProduct.map_id (R := K)
      (s := fun i ↦ X.V (σ.symm (τ.symm i)))) _).trans he.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    change PiTensorProduct.map
      (fun i ↦ (LinearMap.id : X.V (σ.symm (τ.symm i)) →ₗ[K] X.V (σ.symm (τ.symm i))))
      (permObj (σ.trans τ) X).t = _
    exact (LinearMap.congr_fun (PiTensorProduct.map_id (R := K)
      (s := fun i ↦ X.V (σ.symm (τ.symm i)))) _).trans he

theorem perm_refl_isomorphic {K : Type u} [Field K] {d : ℕ}
    (X : TensorObj K d) : Isomorphic (permObj (Equiv.refl _) X) X := by
  have he : (permObj (Equiv.refl _) X).t = X.t := by
    change PiTensorProduct.reindex K X.V (Equiv.refl _) X.t = X.t
    rw [PiTensorProduct.reindex_refl]
    rfl
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    change PiTensorProduct.map (fun i ↦ (LinearMap.id : X.V i →ₗ[K] X.V i)) X.t = _
    exact (LinearMap.congr_fun (PiTensorProduct.map_id (R := K) (s := X.V)) X.t).trans he.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    change PiTensorProduct.map (fun i ↦ (LinearMap.id : X.V i →ₗ[K] X.V i))
      (permObj (Equiv.refl _) X).t = _
    exact (LinearMap.congr_fun (PiTensorProduct.map_id (R := K) (s := X.V)) _).trans he

theorem kronFin_respects_isomorphic {K : Type u} [Field K] {d n : ℕ}
    {X Y : Fin n → TensorObj K d} (h : ∀ s, Isomorphic (X s) (Y s)) :
    Isomorphic (kronFin n X) (kronFin n Y) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  exact Finset.prod_congr rfl (fun s _ ↦ TensorQ.toQ_eq_iff.mpr (h s))

/-- Pairing the physical regional product with its XY swap and then applying
the cyclic symmetrization produces exactly the full six-symmetrization. -/
theorem paired_regional_cyclic {K : Type u} [Field K] {R : ℕ}
    (X : Fin R → TensorObj K 3) :
    Isomorphic
      (cyclicSymmetrization (kronFin R
        (fun r ↦ kron (X r) (permObj swapFirstTwoPerm (X r)))))
      (sixSymmetrization (kronFin R X)) := by
  have hdistribute : Isomorphic
      (cyclicSymmetrization (kronFin R (fun r ↦ kron (X r) (permObj swapFirstTwoPerm (X r)))))
      (kronFin R (fun r ↦ cyclicSymmetrization (kron (X r) (permObj swapFirstTwoPerm (X r))))) := by
    apply TensorQ.toQ_eq_iff.mp
    simp only [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
      mme_toQ_kronFin, ← TensorQ.permAut_toQ, map_mul, map_prod, Finset.prod_mul_distrib]
  exact hdistribute.trans ((kronFin_respects_isomorphic
    (fun r ↦ (mme_sixSymmetrization_isomorphic_cyclic_paired_swap (X r)).symm)).trans
      (mme_sixSymmetrization_kronFin_isomorphic X))

end MME.DWZC1ChildGrouping

end


section

open BigOperators MME MME.TensorObj
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace MME.DWZC2ChildGrouping125

open DWZC1ChildGrouping DWZC2CoarseCounts125 DWZC2Exact125
  DWZC1LiteralChildExtraction

def gamma (t : ℕ) (r : Fin 3) (s : Fin 6) : ℕ :=
  regionWeightCount r * (alphaCount r s + alphaCount r (Fin.rev s)) * t

noncomputable def oldChild {K : Type u} [Field K] (q : ℕ) (s : Fin 6) : TensorObj K 3 :=
  (cwSquareCanonicalGrading K q).blockSubtensor (leftShape 0 s)

noncomputable def oldProduct {K : Type u} [Field K] (q t : ℕ) (r : Fin 3) : TensorObj K 3 :=
  kronFin 6 (fun s ↦ (oldChild q s).kronPow (gamma t r s))

def rotation : Fin 3 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, cyclicPerm.symm, cyclicPerm]

noncomputable def physicalProduct {K : Type u} [Field K]
    (q t : ℕ) (r : Fin 3) : TensorObj K 3 := permObj (rotation r) (oldProduct q t r)

noncomputable def ownerTarget {K : Type u} [Field K]
    (q t : ℕ) (a : Addr t) : TensorObj K 3 :=
  kronFin 6 (fun c ↦ permObj (sigma c)
    (DWZC1SimultaneousChild.regionTarget q (size t c) (left t a c) (right t a c)))

noncomputable def fixedTarget {K : Type u} [Field K] (q t : ℕ) : TensorObj K 3 :=
  kronFin 6 (fun c ↦ permObj (sigma c) (oldProduct q t (region c)))

theorem regional_word_isomorphic {K : Type u} [Field K]
    (q t : ℕ) (a : Addr t)
    (ha : a ∈ RecursiveXHash.target (DWZC1CoarseCounts.scaled counts t)) (c : Fin 6) :
    Isomorphic
      (DWZC1SimultaneousChild.regionTarget (K := K) q (size t c) (left t a c) (right t a c))
      (oldProduct q t (region c)) := by
  let e : Equiv.Perm (Fin 6) := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
  have h := paired_word_grouping (oldChild (K := K) q) e
    Fin.rev_rev (label t a c)
    (fun s ↦ regionWeightCount (region c) * alphaCount (region c) s * t)
    (label_count t a ha c)
  have hgamma (s : Fin 6) : regionWeightCount (region c) * alphaCount (region c) s * t +
      regionWeightCount (region c) * alphaCount (region c) (Fin.rev s) * t =
      gamma t (region c) s := by
    simp only [gamma]
    ring
  simpa only [DWZC1SimultaneousChild.regionTarget, left, right, oldChild,
    e, Equiv.coe_fn_mk, hgamma, oldProduct] using h

theorem owner_fixed_isomorphic {K : Type u} [Field K]
    (q t : ℕ) (a : Addr t)
    (ha : a ∈ RecursiveXHash.target (DWZC1CoarseCounts.scaled counts t)) :
    Isomorphic (ownerTarget (K := K) q t a)
      (fixedTarget q t) := by
  exact kronFin_respects_isomorphic (fun c ↦
    permObj_isomorphic (sigma c) (regional_word_isomorphic q t a ha c))

theorem six_regions_paired_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) :
    Isomorphic (kronFin 6 (fun c ↦ permObj (sigma c) (A (region c))))
      (kronFin 3 (fun r ↦ kron (permObj (rotation r) (A r))
        (permObj swapFirstTwoPerm (permObj (rotation r) (A r))))) := by
  have h1 := TensorQ.toQ_eq_iff.mpr
    (permObj_isomorphic swapFirstTwoPerm (perm_refl_isomorphic (A 0)))
  have h3 := TensorQ.toQ_eq_iff.mpr
    (perm_trans_isomorphic cyclicPerm.symm swapFirstTwoPerm (A 1))
  have h5 := TensorQ.toQ_eq_iff.mpr
    (perm_trans_isomorphic cyclicPerm swapFirstTwoPerm (A 2))
  apply TensorQ.toQ_eq_iff.mp
  simp only [mme_toQ_kronFin, TensorQ.toQ_kron, Fin.prod_univ_succ]
  simp only [sigma, region, rotation, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.isValue, h3, h5, h1]
  ac_rfl

/-- Every retained owner's cyclically symmetrized raw child tensor is the same
six-symmetrized physical regional product, with exact paired frequencies. -/
theorem owner_cyclic_six_isomorphic {K : Type u} [Field K]
    (q t : ℕ) (a : Addr t)
    (ha : a ∈ RecursiveXHash.target (DWZC1CoarseCounts.scaled counts t)) :
    Isomorphic (cyclicSymmetrization (ownerTarget (K := K) q t a))
      (sixSymmetrization (kronFin 3 (physicalProduct q t))) := by
  exact (cyclic_respects_isomorphic
    ((owner_fixed_isomorphic q t a ha).trans (six_regions_paired_isomorphic _))).trans
      (paired_regional_cyclic (physicalProduct q t))

private theorem isomorphic_of_mode_equiv {K : Type u} [Field K] {d : ℕ}
    (X Y : TensorObj K d) (e : ∀ i, X.V i ≃ₗ[K] Y.V i)
    (he : PiTensorProduct.map (fun i ↦ (e i).toLinearMap) X.t = Y.t) :
    Isomorphic X Y := by
  constructor
  · refine ⟨fun i ↦ (e i).symm.toLinearMap, ?_⟩
    rw [← he, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    have h : (fun i ↦ (e i).symm.toLinearMap.comp (e i).toLinearMap) =
        (fun i ↦ (LinearMap.id : X.V i →ₗ[K] X.V i)) := by
      funext i
      ext x
      exact (e i).symm_apply_apply x
    rw [h, PiTensorProduct.map_id]
    rfl
  · exact ⟨fun i ↦ (e i).toLinearMap, he⟩

theorem square_cyclic_isomorphic {K : Type u} [Field K]
    (q : ℕ) (rho : Fin 3 → Fin 5) :
    Isomorphic (permObj cyclicPerm ((cwSquareCanonicalGrading K q).blockSubtensor rho))
      ((cwSquareCanonicalGrading K q).blockSubtensor (fun i ↦ rho (cyclicPerm.symm i))) := by
  obtain ⟨e,he,_⟩ := mme_complete_split_CW_square_cyclic_basis_transport K q rho
  exact isomorphic_of_mode_equiv _ _ e he

theorem square_inverse_cyclic_isomorphic {K : Type u} [Field K]
    (q : ℕ) (rho : Fin 3 → Fin 5) :
    Isomorphic (permObj cyclicPerm.symm ((cwSquareCanonicalGrading K q).blockSubtensor rho))
      ((cwSquareCanonicalGrading K q).blockSubtensor (fun i ↦ rho (cyclicPerm i))) := by
  let Y := (cwSquareCanonicalGrading K q).blockSubtensor (fun i ↦ rho (cyclicPerm i))
  have h := square_cyclic_isomorphic (K := K) q (fun i ↦ rho (cyclicPerm i))
  simp only [Equiv.apply_symm_apply] at h
  have hcancel : Isomorphic Y (permObj cyclicPerm.symm (permObj cyclicPerm Y)) := by
    have ht := perm_trans_isomorphic cyclicPerm cyclicPerm.symm Y
    rw [Equiv.self_trans_symm] at ht
    exact (perm_refl_isomorphic Y).symm.trans ht
  exact ((hcancel.trans (permObj_isomorphic cyclicPerm.symm h))).symm

/-- Actual canonical square constituents, not an abstract rotation label. -/
theorem physical_child_isomorphic {K : Type u} [Field K]
    (q : ℕ) (r : Fin 3) (s : Fin 6) :
    Isomorphic (permObj (rotation r) (oldChild (K := K) q s))
      ((cwSquareCanonicalGrading K q).blockSubtensor (leftShape r s)) := by
  fin_cases r
  · exact perm_refl_isomorphic _
  · have hshape : (fun i ↦ leftShape 0 s (cyclicPerm i)) = leftShape 1 s := by
      funext i
      fin_cases s <;> fin_cases i <;> rfl
    simpa only [rotation, Matrix.cons_val_one, oldChild, hshape] using
      (square_inverse_cyclic_isomorphic (K := K) q (leftShape 0 s))
  · have hshape : (fun i ↦ leftShape 0 s (cyclicPerm.symm i)) = leftShape 2 s := by
      funext i
      fin_cases s <;> fin_cases i <;> rfl
    simpa only [rotation, Matrix.cons_val_two, oldChild, hshape] using
      (square_cyclic_isomorphic (K := K) q (leftShape 0 s))

noncomputable def canonicalProduct {K : Type u} [Field K]
    (q t : ℕ) (r : Fin 3) : TensorObj K 3 :=
  kronFin 6 (fun s ↦ ((cwSquareCanonicalGrading K q).blockSubtensor (leftShape r s)).kronPow
    (gamma t r s))

theorem physical_product_isomorphic {K : Type u} [Field K]
    (q t : ℕ) (r : Fin 3) :
    Isomorphic (physicalProduct (K := K) q t r) (canonicalProduct q t r) := by
  refine (perm_kronFin_isomorphic (rotation r) _).trans ?_
  apply kronFin_respects_isomorphic
  intro s
  apply (perm_kronPow_isomorphic (rotation r) _ _).trans
  apply TensorQ.toQ_eq_iff.mp
  simp only [TensorQ.toQ_kronPow, TensorQ.toQ_eq_iff.mpr (physical_child_isomorphic q r s)]

theorem six_respects_isomorphic {K : Type u} [Field K]
    {X Y : TensorObj K 3} (h : Isomorphic X Y) :
    Isomorphic (sixSymmetrization X) (sixSymmetrization Y) := by
  exact TensorQ.mul_respects_iso (cyclic_respects_isomorphic h)
    (permObj_isomorphic swapFirstTwoPerm (cyclic_respects_isomorphic h))

theorem rotation_six_isomorphic {K : Type u} [Field K]
    (X : TensorObj K 3) (r : Fin 3) :
    Isomorphic (sixSymmetrization (permObj (rotation r) X)) (sixSymmetrization X) := by
  fin_cases r
  · exact six_respects_isomorphic (perm_refl_isomorphic X)
  · have hcyc : cyclicPerm.trans cyclicPerm = cyclicPerm.symm := by decide
    simpa only [rotation, Matrix.cons_val_one, hcyc] using
      (mme_sixSymmetrization_isomorphic_cyclic_orbit X).2
  · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit X).1

theorem kronPow_respects_isomorphic {K : Type u} [Field K] {d : ℕ}
    {X Y : TensorObj K d} (h : Isomorphic X Y) (n : ℕ) :
    Isomorphic (X.kronPow n) (Y.kronPow n) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [TensorQ.toQ_kronPow, TensorQ.toQ_eq_iff.mpr h]

/-- The raw physical square-power six-symmetrization is identical in value to
the original orientation.  This does not transport a prescribed Z profile. -/
theorem physical_child_six_power_isomorphic {K : Type u} [Field K]
    (q : ℕ) (r : Fin 3) (s : Fin 6) (n : ℕ) :
    Isomorphic
      (sixSymmetrization (((cwSquareCanonicalGrading K q).blockSubtensor (leftShape r s)).kronPow n))
      (sixSymmetrization ((oldChild q s).kronPow n)) := by
  exact (six_respects_isomorphic
    ((kronPow_respects_isomorphic (physical_child_isomorphic q r s).symm n).trans
      (perm_kronPow_isomorphic (rotation r) (oldChild q s) n).symm)).trans
        (rotation_six_isomorphic _ r)

noncomputable def flatProduct {K : Type u} [Field K] (q t : ℕ) : TensorObj K 3 :=
  kronFin 18 (fun j ↦
    let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
    ((cwSquareCanonicalGrading K q).blockSubtensor (leftShape rs.1 rs.2)).kronPow
      (gamma t rs.1 rs.2))

theorem canonical_flat_isomorphic {K : Type u} [Field K] (q t : ℕ) :
    Isomorphic (kronFin 3 (canonicalProduct (K := K) q t)) (flatProduct q t) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [flatProduct, canonicalProduct, mme_toQ_kronFin]
  let f : Fin 3 × Fin 6 → TensorQ K 3 := fun rs ↦
    TensorQ.toQ (((cwSquareCanonicalGrading K q).blockSubtensor (leftShape rs.1 rs.2)).kronPow
      (gamma t rs.1 rs.2))
  change (∏ r, ∏ s, f (r,s)) = ∏ j, f (finProdFinEquiv.symm j)
  calc
    _ = ∏ rs, f rs := (Fintype.prod_prod_type f).symm
    _ = _ := Fintype.prod_equiv finProdFinEquiv _ _
      (fun _ ↦ by simp only [Equiv.symm_apply_apply])

/-- The literal selected owner's symmetrized child product is the fixed product
of the twelve physical canonical square constituents with paired exponents. -/
theorem owner_cyclic_canonical_six_isomorphic {K : Type u} [Field K]
    (q t : ℕ) (a : Addr t)
    (ha : a ∈ RecursiveXHash.target (DWZC1CoarseCounts.scaled counts t)) :
    Isomorphic (cyclicSymmetrization (ownerTarget (K := K) q t a))
      (sixSymmetrization (kronFin 3 (canonicalProduct q t))) := by
  exact (owner_cyclic_six_isomorphic q t a ha).trans
    (six_respects_isomorphic (kronFin_respects_isomorphic (physical_product_isomorphic q t)))

theorem owner_cyclic_flat_six_isomorphic {K : Type u} [Field K]
    (q t : ℕ) (a : Addr t)
    (ha : a ∈ RecursiveXHash.target (DWZC1CoarseCounts.scaled counts t)) :
    Isomorphic (cyclicSymmetrization (ownerTarget (K := K) q t a))
      (sixSymmetrization (flatProduct q t)) :=
  (owner_cyclic_canonical_six_isomorphic q t a ha).trans
    (six_respects_isomorphic (canonical_flat_isomorphic q t))

/-- The fixed target has this six-symmetrized normal form independently of the
selected address. This is the interface for preserving every direct-sum copy. -/
theorem fixed_cyclic_flat_six_isomorphic {K : Type u} [Field K] (q t : ℕ) :
    Isomorphic (cyclicSymmetrization (fixedTarget (K := K) q t))
      (sixSymmetrization (flatProduct q t)) := by
  exact ((cyclic_respects_isomorphic (six_regions_paired_isomorphic (oldProduct q t))).trans
    (paired_regional_cyclic (physicalProduct q t))).trans
      ((six_respects_isomorphic (kronFin_respects_isomorphic (physical_product_isomorphic q t))).trans
        (six_respects_isomorphic (canonical_flat_isomorphic q t)))

end MME.DWZC2ChildGrouping125

end


section

open MME MME.TensorObj BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1CopyValue

theorem kron_restrict {K : Type u} [Field K]
    {A B C D : TensorObj K 3} (hAB : TensorObj.Restrict A B)
    (hCD : TensorObj.Restrict C D) :
    TensorObj.Restrict (kron A C) (kron B D) := by
  have h1 := (TensorQ.tensorStrassen K 3 (by omega)).mul_right
    (TensorQ.toQ A) (TensorQ.toQ B) hAB (TensorQ.toQ C)
  have h2 := (TensorQ.tensorStrassen K 3 (by omega)).mul_right
    (TensorQ.toQ C) (TensorQ.toQ D) hCD (TensorQ.toQ B)
  change TensorQ.le (TensorQ.toQ (kron A C)) (TensorQ.toQ (kron B D))
  simp only [TensorQ.toQ_kron]
  exact TensorQ.le_trans _ _ _ h1 (by simpa only [mul_comm] using h2)

theorem cyclic_restrict {K : Type u} [Field K] {A B : TensorObj K 3}
    (h : TensorObj.Restrict A B) :
    TensorObj.Restrict (cyclicSymmetrization A) (cyclicSymmetrization B) := by
  rw [cyclicSymmetrization_eq_public_perm, cyclicSymmetrization_eq_public_perm]
  exact kron_restrict h (kron_restrict (permObj_restrict cyclicPerm h)
    (permObj_restrict (cyclicPerm.trans cyclicPerm) h))

theorem cyclic_copies_isomorphic {K : Type u} [Field K]
    (T : TensorObj K 3) (k : ℕ) :
    Isomorphic (cyclicSymmetrization (bigAdd (fun _ : Fin k ↦ T)))
      (bigAdd (fun _ : Fin (k ^ 3) ↦ cyclicSymmetrization T)) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_bigAdd,
    TensorQ.toQ_kron, ← TensorQ.permAut_toQ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, map_mul, map_natCast]
  ring

theorem finite_MM_copies {K : Type u} [Field K]
    (T : TensorObj K 3) (copies : ℕ) (tau lower : ℝ)
    (hextract : ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j))) T ∧
        lower ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (bigAdd (fun _ : Fin copies ↦ T)) ∧
      (copies : ℝ) * lower ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨k, a, b, c, hres, hbound⟩ := hextract
  let index : Fin (copies * k) → Fin k := fun j ↦ (finProdFinEquiv.symm j).2
  refine ⟨copies * k, a ∘ index, b ∘ index, c ∘ index, ?_, ?_⟩
  · have hiso : Isomorphic
        (bigAdd (fun j : Fin (copies * k) ↦
          MMObj K (a (index j)) (b (index j)) (c (index j))))
        (bigAdd (fun _ : Fin copies ↦ bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))) := by
      apply TensorQ.toQ_eq_iff.mp
      simp only [TensorQ.toQ_bigAdd]
      rw [← finProdFinEquiv.sum_comp]
      simp only [index, Equiv.symm_apply_apply, Fintype.sum_prod_type,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hiso.1.trans (mme_bigAdd_mono_restrict (fun _ ↦ hres))
  · have hsum : (∑ j : Fin (copies * k),
        (((a (index j) * b (index j) * c (index j) : ℕ) : ℝ) ^ tau)) =
        (copies : ℝ) * ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
      rw [← finProdFinEquiv.sum_comp]
      simp only [index, Equiv.symm_apply_apply, Fintype.sum_prod_type,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (copies : ℝ) * lower ≤ ∑ j : Fin (copies * k),
      (((a (index j) * b (index j) * c (index j) : ℕ) : ℝ) ^ tau)
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg copies)

/-- Preserve all cubed copy indices when passing from six-region extraction
to a matrix witness for the original parent's six symmetrization. -/
theorem finite_parent_of_cyclic_copies {K : Type u} [Field K]
    (A B P : TensorObj K 3) (copies : ℕ) (tau lower : ℝ)
    (hcopy : TensorObj.Restrict (bigAdd (fun _ : Fin copies ↦ B)) P)
    (hparent : TensorObj.Restrict (cyclicSymmetrization P) (sixSymmetrization A))
    (hchild : ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (cyclicSymmetrization B) ∧
      lower ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization A) ∧
      ((copies ^ 3 : ℕ) : ℝ) * lower ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨k, a, b, c, hres, hbound⟩ :=
    finite_MM_copies (cyclicSymmetrization B) (copies ^ 3) tau lower hchild
  exact ⟨k, a, b, c,
    hres.trans ((cyclic_copies_isomorphic B copies).2.trans
      ((cyclic_restrict hcopy).trans hparent)), hbound⟩

end MME.DWZC1CopyValue

end


section

open MME MME.TensorObj BigOperators Filter
open MME.DWZPositiveComponent125 MME.DWZC1LiteralChildExtraction
open MME.DWZC2ChildGrouping125
open MME.DWZC2Exact125
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1FixedTensorExtraction

/-- Actual square constituents in physical regional orientation. -/
noncomputable def physicalChild {K : Type u} [Field K] (q : ℕ)
    (j : Fin 18) : TensorObj K 3 :=
  let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
  (cwSquareCanonicalGrading K q).blockSubtensor (leftShape rs.1 rs.2)

/-- Literal paired count, prior to the common integer scaling. -/
def childCount (j : Fin 18) : ℕ :=
  let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
  regionWeightCount rs.1 * (alphaCount rs.1 rs.2 + alphaCount rs.1 (Fin.rev rs.2))

theorem flatProduct_eq {K : Type u} [Field K] (q t : ℕ) :
    flatProduct (K := K) q t =
      kronFin 18 (fun j ↦ (physicalChild q j).kronPow (childCount j * t)) := rfl

/-- Normalize every owner before distributing cyclic symmetrization, retaining
all three independent owner indices, not only the diagonal ones. -/
theorem family_fixed_restrict {K : Type u} [Field K] (q t : ℕ)
    (kept : Finset (Addr t)) (e : Fin kept.card ≃ ↥kept)
    (hkept : kept ⊆ RecursiveXHash.target (DWZC1CoarseCounts.scaled
      DWZC2CoarseCounts125.counts t)) :
    TensorObj.Restrict (bigAdd (fun _ : Fin kept.card ↦ fixedTarget (K := K) q t))
      (DWZC1LiteralAsymptotic.family q t kept e) := by
  apply mme_bigAdd_mono_restrict
  intro j
  exact (owner_fixed_isomorphic q t (e j).val (hkept (e j).property)).2

theorem eventual_fixed_child_products {K : Type u} [Field K] (q : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hupper : ρ ≤ 383836115467 / 500000000000) :
    ∀ᶠ t : ℕ in atTop, ∃ k : ℕ,
      Real.exp (2000000000000002000000000000000 * ρ * (t : ℝ)) ≤ (k : ℝ) ∧
      TensorObj.Restrict
        (bigAdd (fun _ : Fin (k ^ 3) ↦ sixSymmetrization
          (kronFin 18 (fun j ↦ (physicalChild q j).kronPow (childCount j * t)))))
        (sixSymmetrization (DWZC1LiteralAsymptotic.original (K := K) q t)) := by
  classical
  filter_upwards [DWZC1LiteralAsymptotic.eventual_actual_child_families
    (K := K) q ρ hρ hupper] with t ht
  obtain ⟨kept,e,hkept,hcard,_hraw,hcyclic⟩ := ht
  have hfixed := family_fixed_restrict (K := K) q t kept e hkept
  have hcyfixed := (DWZC1CopyValue.cyclic_restrict hfixed).trans hcyclic
  have hcopies := (DWZC1CopyValue.cyclic_copies_isomorphic
    (fixedTarget (K := K) q t) kept.card).2.trans hcyfixed
  refine ⟨kept.card,hcard,?_⟩
  have hnormal := mme_bigAdd_mono_restrict (fun _ : Fin (kept.card ^ 3) ↦
    (fixed_cyclic_flat_six_isomorphic (K := K) q t).2)
  rw [flatProduct_eq] at hnormal
  exact hnormal.trans hcopies

/-- The normalization used by the cofinal parent-value interface. -/
theorem eventual_fixed_child_products_normalized {K : Type u} [Field K] (q : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hupper : ρ ≤ 383836115467 / 500000000000) :
    ∀ᶠ t : ℕ in atTop, ∃ k : ℕ,
      Real.exp ((2 : ℝ) * (1000000000000001000000000000000 : ℕ) * ρ * t) ≤ k ∧
      TensorObj.Restrict
        (bigAdd (fun _ : Fin (k ^ 3) ↦ sixSymmetrization
          (kronFin 18 (fun j ↦ (physicalChild q j).kronPow (childCount j * t)))))
        (sixSymmetrization (DWZC1LiteralAsymptotic.original (K := K) q t)) := by
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 1000000000000001000000000000000 =
    2000000000000002000000000000000 by norm_num]
  exact
    eventual_fixed_child_products (K := K) q ρ hρ hupper

end MME.DWZC1FixedTensorExtraction

end


section

open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace MME.DWZC2Exact125

def childCoefficient (r : Fin 3) (s : Fin 6) : ℚ :=
  (regionWeightCount r : ℚ) / 1000000000000001 *
    (alpha r s + alpha r (Fin.rev s))

def childLogRate : Fin 3 → Fin 6 → ℚ := ![
  ![0,1820522261843/1000000000000,2605830347207/1000000000000,1820522261843/1000000000000,1503893725497/500000000000,75535540347/25000000000],
  ![0,1820522261843/1000000000000,2605830347207/1000000000000,1820522261843/1000000000000,75535540347/25000000000,3021421613803/1000000000000],
  ![0,1820522261843/1000000000000,2605830347207/1000000000000,1820522261843/1000000000000,3021421613803/1000000000000,1503893725497/500000000000]]

/-- Original paired-child multiplicities, including the slight asymmetry
between slot s and its complement. -/
theorem childCoefficient_exact :
    (∀ r s, 0 < childCoefficient r s) ∧
    (∑ r : Fin 3, ∑ s : Fin 6, childCoefficient r s) = 2 := by
  decide +kernel

theorem child_weighted_log_exact :
    (∑ r : Fin 3, ∑ s : Fin 6, childCoefficient r s * childLogRate r s) =
      (669942334787390032566882531838026488019749 /
        142857142857143000000000000000000000000000 : ℚ) := by
  decide +kernel

/-- A uniform strict log decrement is permitted by the original retained
floor; no decimal rounding or updated quarter-entropy estimate is used. -/
theorem child_strict_log_margin_rat :
    (1091453673843 / 200000000000 : ℚ) <
      383836115467 / 500000000000 +
        ∑ r : Fin 3, ∑ s : Fin 6, childCoefficient r s *
          (childLogRate r s - 1 / 100000000000000) := by
  decide +kernel

theorem child_strict_log_margin :
    (1091453673843 / 200000000000 : ℝ) <
      383836115467 / 500000000000 +
        ∑ r : Fin 3, ∑ s : Fin 6, (childCoefficient r s : ℝ) *
          ((childLogRate r s : ℝ) - 1 / 100000000000000) := by
  have h := (Rat.cast_lt (K := ℝ)).2 child_strict_log_margin_rat
  push_cast at h
  exact h

theorem childCoefficient_sum_real :
    (∑ r : Fin 3, ∑ s : Fin 6, (childCoefficient r s : ℝ)) = 2 := by
  exact_mod_cast childCoefficient_exact.2

end MME.DWZC2Exact125

end


section

open MME MME.TensorObj MME.DWZRestrictedValue MME.DWZComponentRestriction
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.DWZC2Exact125
open MME.DWZC2ChildGrouping125

/-- (2,2,0) is a cyclic rotation of (2,0,2). -/
theorem block220_iso {K : Type u} [Field K] :
    Isomorphic (permObj cyclicPerm ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 2 0 2)))
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 2 2 0)) := by
  have h := square_cyclic_isomorphic (K := K) 5 (cwSquareBlockType 2 0 2)
  have hs : (fun i ↦ cwSquareBlockType 2 0 2 (cyclicPerm.symm i)) = cwSquareBlockType 2 2 0 := by
    funext i; fin_cases i <;> rfl
  rwa [hs] at h

theorem sq220_six_value (K : Type u) [Field K] (tau : ℝ) :
    HasSixSymmetricTauValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 2 2 0)) tau ((27 : ℝ) ^ tau) := by
  have h202 : TensorObj.Restrict (MMObj K 27 1 1)
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 2 0 2)) := by
    simpa using mme_CW_square_canonical_central202_restrict (K := K) 5
  have hMM := mme_MMObj_tau_value (K := K) (27 ^ 2) (27 ^ 2) (27 ^ 2) tau
  have hiso := mme_sixSymmetrization_MMObj_isomorphic (K := K) 27 1 1
  have hrot := six_respects_isomorphic (block220_iso (K := K))
  have hcyc := (mme_sixSymmetrization_isomorphic_cyclic_orbit
    ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 2 0 2))).1
  -- MMObj (27^2)^3  ≤  sym6 ⟨27,1,1⟩  ≤  sym6 block202  ≅  sym6 (perm block202)  ≅  sym6 block220
  have hchain : TensorObj.Restrict (MMObj K (27 ^ 2) (27 ^ 2) (27 ^ 2))
      (sixSymmetrization ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 2 2 0))) := by
    have a : TensorObj.Restrict (MMObj K (27 ^ 2) (27 ^ 2) (27 ^ 2)) (sixSymmetrization (MMObj K 27 1 1)) := by
      simpa using hiso.2
    exact ((a.trans (mme_sixSymmetrization_restrict h202)).trans hcyc.2).trans hrot.1
  change HasTauValueAtLeast _ tau (((27 : ℝ) ^ tau) ^ (6 : ℕ))
  have hval : ((27 : ℝ) ^ tau) ^ (6 : ℕ) = (((27 ^ 2 * 27 ^ 2 * 27 ^ 2 : ℕ) : ℝ) ^ tau) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm tau,
      Real.rpow_mul (by norm_num)]
    norm_num
  rw [hval]
  exact mme_HasTauValueAtLeast_mono_restrict hchain hMM



/-- The one-hot Z profile at left grade 0 (the Z index of (2,2,0) is 0). -/
def oneHot0 : IntegerZSplitProfile 3 where
  denominator := 1
  denominator_pos := by decide
  count := ![1, 0, 0]
  count_sum := by decide

theorem sq220_prescribed_value (K : Type u) [Field K] (tau : ℝ) :
    HasPrescribedZSixRestrictionValueAtLeast
      (CompleteSplitCanonicalSquare.obj K 5 (cwSquareBlockType 2 2 0))
      (CompleteSplitCanonicalSquare.basis K 5 (cwSquareBlockType 2 2 0) 2)
      LiftedCoarsePair.leftGrade oneHot0 tau ((27 : ℝ) ^ tau) := by
  apply mme_HasPrescribedZSix_of_constant_grade_oneHot _ _ _ _ (0 : Fin 3) ?_ ?_ tau _
    (by positivity) (sq220_six_value K tau)
  · intro x
    apply Fin.ext
    have hx := congrArg Fin.val x.down.property
    change (cwSquareCoordGrade 5 x.down.val.1).val +
      (cwSquareCoordGrade 5 x.down.val.2).val = 0 at hx
    change (cwSquareCoordGrade 5 x.down.val.1).val = 0
    omega
  · intro a
    fin_cases a <;> rfl

theorem prescribed_value_mono {K : Type u} [Field K] {T : TensorObj K 3} {ι : Type u} {t : ℕ}
    {bZ : Module.Basis ι K (T.V 2)} {grade : ι → Fin t} {p : IntegerZSplitProfile t}
    {tau V V' : ℝ} (h : HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V)
    (h0 : 0 ≤ V') (hle : V' ≤ V) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V' := by
  obtain ⟨_, h2⟩ := h
  exact ⟨h0, fun v hv hvV cutoff ↦ h2 v hv (lt_of_lt_of_le hvV hle) cutoff⟩

theorem log_inv27_cert :
    Real.log (370370370371 / 10000000000000 : ℝ) ≤ -(3295836865952900 / 1000000000000000 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (370370370371 / 10000000000000)
    (((370370370371 / 10000000000000) * 2^5 - 1) / ((370370370371 / 10000000000000) * 2^5 + 1))
    (-4) (-3295836865952900 / 1000000000000000) 5 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := h.2
  push_cast at h2
  linarith

theorem rho_le_tau_log27 :
    (2605830347207 / 1000000000000 : ℝ) ≤ (790643 / 1000000 : ℝ) * Real.log 27 := by
  have hq : Real.log (1 / 27 : ℝ) ≤ Real.log (370370370371 / 10000000000000 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hinv : Real.log (1 / 27 : ℝ) = -Real.log 27 := by
    rw [one_div, Real.log_inv]
  have := log_inv27_cert
  nlinarith

theorem sq220_prescribed_value_rho (K : Type u) [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (CompleteSplitCanonicalSquare.obj K 5 (cwSquareBlockType 2 2 0))
      (CompleteSplitCanonicalSquare.basis K 5 (cwSquareBlockType 2 2 0) 2)
      LiftedCoarsePair.leftGrade oneHot0 (790643 / 1000000 : ℝ)
      (Real.exp (2605830347207 / 1000000000000 : ℝ)) := by
  apply prescribed_value_mono (sq220_prescribed_value K _) (Real.exp_pos _).le
  rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  exact Real.exp_le_exp.mpr rho_le_tau_log27

end MME.DWZC2Exact125


end


section

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.DWZC2Exact125

theorem blockType_eq_vector (I J L : Fin 5) : cwSquareBlockType I J L = ![I,J,L] := by
  funext i
  fin_cases i <;> rfl

def scalarProfile : IntegerZSplitProfile 3 where
  denominator := 1
  denominator_pos := by decide
  count := ![0,0,1]
  count_sum := by decide

theorem scalar_prescribed_value (K : Type u) [Field K] (tau : ℝ) :
    HasPrescribedZSixRestrictionValueAtLeast
      (CompleteSplitCanonicalSquare.obj K 5 (cwSquareBlockType 0 0 4))
      (CompleteSplitCanonicalSquare.basis K 5 (cwSquareBlockType 0 0 4) 2)
      LiftedCoarsePair.leftGrade scalarProfile tau 1 := by
  have hscalar := (mme_CW_square_canonical_support_and_scalar_blocks
    (K := K) 5).2.1
  have hMM : HasTauValueAtLeast (MMObj K 1 1 1) tau 1 := by
    simpa using mme_MMObj_tau_value (K := K) 1 1 1 tau
  have hSix : HasSixSymmetricTauValueAtLeast
      (CompleteSplitCanonicalSquare.obj K 5 (cwSquareBlockType 0 0 4)) tau 1 := by
    change HasTauValueAtLeast _ tau (1 ^ (6 : ℕ))
    rw [one_pow]
    apply mme_HasTauValueAtLeast_mono_restrict _ hMM
    have hMMsix : TensorObj.Restrict (MMObj K 1 1 1)
        (sixSymmetrization (MMObj K 1 1 1)) := by
      simpa using (mme_sixSymmetrization_MMObj_isomorphic (K := K) 1 1 1).2
    exact hMMsix.trans (mme_sixSymmetrization_restrict hscalar)
  apply mme_HasPrescribedZSix_of_constant_grade_oneHot _ _ _ _ (2 : Fin 3)
    ?_ ?_ tau 1 zero_le_one hSix
  · intro x
    apply Fin.ext
    have hx := congrArg Fin.val x.down.property
    change (cwSquareCoordGrade 5 x.down.val.1).val +
      (cwSquareCoordGrade 5 x.down.val.2).val = 4 at hx
    have hright := (cwSquareCoordGrade 5 x.down.val.2).isLt
    change (cwSquareCoordGrade 5 x.down.val.1).val = 2
    have hleft := (cwSquareCoordGrade 5 x.down.val.1).isLt
    omega
  · intro a
    fin_cases a <;> rfl

/-- Child inputs. Boundary slots use a fixed orientation carrying an accepted endpoint:
the scalar (0,0,4) block, the elementary (0,1,3)/(1,0,3) endpoints, and the (2,2,0)
block (value 27^tau via <27,1,1>). Interior slots use this consumer's accepted coupled63
rows in their physical shape. Physical children are reached by cyclic covariance of
the six-symmetrization. -/
def interiorRow : Fin 3 → Fin 6 → Fin 63 :=
  ![![0,0,0,0,3,4],![0,0,0,0,4,5],![0,0,0,0,5,3]]

def childInputShape (r : Fin 3) (s : Fin 6) : Fin 3 → Fin 5 :=
  ![cwSquareBlockType 0 0 4, cwSquareBlockType 0 1 3, cwSquareBlockType 2 2 0, cwSquareBlockType 1 0 3, Coupled63Scalar.rho (interiorRow r 4), Coupled63Scalar.rho (interiorRow r 5)] s

def childInputProfile (r : Fin 3) (s : Fin 6) : IntegerZSplitProfile 3 :=
  ![scalarProfile, ElementaryFourScalar.profile 0, oneHot0, ElementaryFourScalar.profile 3, Coupled63Scalar.profile (interiorRow r 4), Coupled63Scalar.profile (interiorRow r 5)] s

noncomputable def childInput (K : Type u) [Field K] (r : Fin 3) (s : Fin 6) :
    TensorObj K 3 := CompleteSplitCanonicalSquare.obj K 5 (childInputShape r s)

noncomputable def childInputBasis (K : Type u) [Field K] (r : Fin 3) (s : Fin 6) :=
  CompleteSplitCanonicalSquare.basis K 5 (childInputShape r s) 2

theorem childInput_values (K : Type u) [Field K] (r : Fin 3) (s : Fin 6) :
    HasPrescribedZSixRestrictionValueAtLeast
      (childInput K r s) (childInputBasis K r s)
      LiftedCoarsePair.leftGrade (childInputProfile r s)
      (790643 / 1000000 : ℝ) (Real.exp (childLogRate r s : ℝ)) := by
  have hs : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · have hr : childLogRate r 0 = 0 := by fin_cases r <;> rfl
    rw [hr]
    simp only [Rat.cast_zero,Real.exp_zero]
    exact scalar_prescribed_value K (790643 / 1000000 : ℝ)
  · have hr : childLogRate r 1 = 1820522261843/1000000000000 := by fin_cases r <;> rfl
    rw [hr]
    push_cast
    exact (mme_dwz_fourth_elementary_four_actual_prescribed_z_endpoints K).1
  · have hr : childLogRate r 2 = 2605830347207/1000000000000 := by fin_cases r <;> rfl
    rw [hr]
    push_cast
    exact sq220_prescribed_value_rho K
  · have hr : childLogRate r 3 = 1820522261843/1000000000000 := by fin_cases r <;> rfl
    rw [hr]
    push_cast
    exact (mme_dwz_fourth_elementary_four_actual_prescribed_z_endpoints K).2.2.2
  · have hr : childLogRate r 4 = (Coupled63Scalar.rows (interiorRow r 4)).rate := by
      fin_cases r <;> rfl
    rw [hr]
    exact mme_dwz_fourth_coupled63_prescribedZ_six_values K (interiorRow r 4)
  · have hr : childLogRate r 5 = (Coupled63Scalar.rows (interiorRow r 5)).rate := by
      fin_cases r <;> rfl
    rw [hr]
    exact mme_dwz_fourth_coupled63_prescribedZ_six_values K (interiorRow r 5)

theorem child_strict_bases (r : Fin 3) (s : Fin 6) :
    0 < Real.exp ((childLogRate r s : ℝ) - 1 / 100000000000000) ∧
      Real.exp ((childLogRate r s : ℝ) - 1 / 100000000000000) <
        Real.exp (childLogRate r s : ℝ) := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_lt_exp.mpr
    linarith

end MME.DWZC2Exact125

end


section

open MME MME.TensorObj MME.DWZRestrictedValue Module BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1ChildValue

/-- All prescribed child certificates yield simultaneous actual matrix
extractions from arbitrary integer-multiplicity products at common lengths.
The projection is used in its valid direction: prescribed children restrict
from the unfiltered children left after coarse parent extraction. -/
theorem common_multiplicity_product
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) {ι : Fin n → Type u} {d : Fin n → ℕ}
    (bZ : (i : Fin n) → Basis (ι i) K ((T i).V 2))
    (grade : (i : Fin n) → ι i → Fin (d i))
    (p : (i : Fin n) → IntegerZSplitProfile (d i))
    (tau : ℝ) (V v : Fin n → ℝ)
    (hpos : ∀ i, 0 < v i) (hstrict : ∀ i, v i < V i)
    (hvalue : ∀ i, HasPrescribedZSixRestrictionValueAtLeast
      (T i) (bZ i) (grade i) (p i) tau (V i)) :
    ∃ L : ℕ, 0 < L ∧ ∀ (r : ℕ) (count : Fin n → ℕ),
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          (sixSymmetrization (kronFin n (fun i ↦ (T i).kronPow (L * r * count i)))) ∧
        (∏ i, (v i) ^ (6 * (L * r * count i))) ≤
          ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨L, hL, hcommon⟩ := mme_dwz_prescribed_z_six_finite_common_physical_length
    T bZ grade p tau V v hpos hstrict hvalue
  refine ⟨L, hL, ?_⟩
  intro r count
  have hone (i : Fin n) :
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          (sixSymmetrization ((T i).kronPow (L * r * count i))) ∧
        (v i) ^ (6 * (L * r * count i)) ≤
          ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    obtain ⟨m, hm, k, a, b, c, hres, hbound⟩ := hcommon (r * count i) i
    have hlen : (p i).length m = L * r * count i := by simpa [Nat.mul_assoc] using hm
    refine ⟨k, a, b, c, ?_, ?_⟩
    · have hproj := mme_sixSymmetrization_restrict
        (mme_dwz_prescribed_z_power_projection (T i) (bZ i) (grade i) (p i) m)
      rw [hlen] at hproj
      exact hres.trans hproj
    · simpa [Nat.mul_assoc] using hbound
  obtain ⟨k, a, b, c, hres, hbound⟩ := mme_finite_MM_extractions_kronFin_tau_product
    (fun i ↦ sixSymmetrization ((T i).kronPow (L * r * count i))) tau
    (fun i ↦ (v i) ^ (6 * (L * r * count i)))
    (fun i ↦ pow_nonneg (hpos i).le _) hone
  exact ⟨k, a, b, c, hres.trans
    (mme_sixSymmetrization_kronFin_isomorphic
      (fun i ↦ (T i).kronPow (L * r * count i))).1, hbound⟩

end MME.DWZC1ChildValue

end


section

open MME MME.TensorObj MME.DWZRestrictedValue MME.DWZComponentRestriction Module BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.DWZC2Exact125

open DWZC1ChildGrouping DWZC2ChildGrouping125

def childMultiplicity (j : Fin 18) : ℕ :=
  let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
  regionWeightCount rs.1 * (alphaCount rs.1 rs.2 + alphaCount rs.1 (Fin.rev rs.2))

noncomputable def strictChildLogRate (j : Fin 18) : ℝ :=
  let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
  (childLogRate rs.1 rs.2 : ℝ) - 1 / 100000000000000

theorem child_input_physical_six_power_isomorphic
    {K : Type u} [Field K] (r : Fin 3) (s : Fin 6) (n : ℕ) :
    Isomorphic (sixSymmetrization ((childInput K r s).kronPow n))
      (sixSymmetrization
        (((cwSquareCanonicalGrading K 5).blockSubtensor (leftShape r s)).kronPow n)) := by
  have hs : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · have hshape : cwSquareBlockType 0 0 4 = leftShape 0 0 := by
      funext i
      fin_cases i <;> rfl
    show Isomorphic (sixSymmetrization ((CompleteSplitCanonicalSquare.obj K 5
      (cwSquareBlockType 0 0 4)).kronPow n)) _
    rw [hshape]
    exact (physical_child_six_power_isomorphic (K := K) 5 0 0 n).trans
      (physical_child_six_power_isomorphic (K := K) 5 r 0 n).symm
  · have hshape : cwSquareBlockType 0 1 3 = leftShape 0 1 := by
      funext i
      fin_cases i <;> rfl
    show Isomorphic (sixSymmetrization ((CompleteSplitCanonicalSquare.obj K 5
      (cwSquareBlockType 0 1 3)).kronPow n)) _
    rw [hshape]
    exact (physical_child_six_power_isomorphic (K := K) 5 0 1 n).trans
      (physical_child_six_power_isomorphic (K := K) 5 r 1 n).symm
  · have hshape : cwSquareBlockType 2 2 0 = leftShape 1 2 := by
      funext i
      fin_cases i <;> rfl
    show Isomorphic (sixSymmetrization ((CompleteSplitCanonicalSquare.obj K 5
      (cwSquareBlockType 2 2 0)).kronPow n)) _
    rw [hshape]
    exact (physical_child_six_power_isomorphic (K := K) 5 1 2 n).trans
      (physical_child_six_power_isomorphic (K := K) 5 r 2 n).symm
  · have hshape : cwSquareBlockType 1 0 3 = leftShape 0 3 := by
      funext i
      fin_cases i <;> rfl
    show Isomorphic (sixSymmetrization ((CompleteSplitCanonicalSquare.obj K 5
      (cwSquareBlockType 1 0 3)).kronPow n)) _
    rw [hshape]
    exact (physical_child_six_power_isomorphic (K := K) 5 0 3 n).trans
      (physical_child_six_power_isomorphic (K := K) 5 r 3 n).symm
  · have hshape : Coupled63Scalar.rho (interiorRow r 4) = leftShape r 4 := by
      funext i
      fin_cases r <;> fin_cases i <;> rfl
    show Isomorphic (sixSymmetrization ((CompleteSplitCanonicalSquare.obj K 5
      (Coupled63Scalar.rho (interiorRow r 4))).kronPow n)) _
    rw [hshape]
    exact Isomorphic.refl _
  · have hshape : Coupled63Scalar.rho (interiorRow r 5) = leftShape r 5 := by
      funext i
      fin_cases r <;> fin_cases i <;> rfl
    show Isomorphic (sixSymmetrization ((CompleteSplitCanonicalSquare.obj K 5
      (Coupled63Scalar.rho (interiorRow r 5))).kronPow n)) _
    rw [hshape]
    exact Isomorphic.refl _

/-- Simultaneous actual matrix extractions from all twelve physical child
factors. Prescribed projection is forgotten before any cyclic rotation. -/
theorem actual_child_common_extractions {K : Type u} [Field K] :
    ∃ L : ℕ, 0 < L ∧ ∀ r : ℕ,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          (sixSymmetrization (flatProduct 5 (L * r))) ∧
        (∏ j : Fin 18, Real.exp (strictChildLogRate j) ^
          (6 * (childMultiplicity j * (L * r)))) ≤
          ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ (790643 / 1000000 : ℝ)) := by
  let T (j : Fin 18) : TensorObj K 3 :=
    let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
    childInput K rs.1 rs.2
  let p (j : Fin 18) : IntegerZSplitProfile 3 :=
    let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
    childInputProfile rs.1 rs.2
  let bZ (j : Fin 18) :=
    let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
    childInputBasis K rs.1 rs.2
  let V (j : Fin 18) : ℝ :=
    let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
    Real.exp (childLogRate rs.1 rs.2 : ℝ)
  let v (j : Fin 18) : ℝ := Real.exp (strictChildLogRate j)
  obtain ⟨L,hL,hcommon⟩ := DWZC1ChildValue.common_multiplicity_product
    T bZ (fun _ ↦ LiftedCoarsePair.leftGrade) p (790643 / 1000000 : ℝ) V v
    (fun j ↦ (child_strict_bases (finProdFinEquiv.symm j : Fin 3 × Fin 6).1
      (finProdFinEquiv.symm j : Fin 3 × Fin 6).2).1)
    (fun j ↦ (child_strict_bases (finProdFinEquiv.symm j : Fin 3 × Fin 6).1
      (finProdFinEquiv.symm j : Fin 3 × Fin 6).2).2)
    (fun j ↦ childInput_values K (finProdFinEquiv.symm j : Fin 3 × Fin 6).1
      (finProdFinEquiv.symm j : Fin 3 × Fin 6).2)
  refine ⟨L,hL,?_⟩
  intro r
  obtain ⟨k,a,b,c,hres,hbound⟩ := hcommon r childMultiplicity
  have hfactor (j : Fin 18) :
      Isomorphic (sixSymmetrization ((T j).kronPow (L * r * childMultiplicity j)))
        (sixSymmetrization
          (((cwSquareCanonicalGrading K 5).blockSubtensor
            (leftShape (finProdFinEquiv.symm j : Fin 3 × Fin 6).1 (finProdFinEquiv.symm j : Fin 3 × Fin 6).2)).kronPow
              (gamma (L*r) (finProdFinEquiv.symm j : Fin 3 × Fin 6).1 (finProdFinEquiv.symm j : Fin 3 × Fin 6).2))) := by
    have hn : L * r * childMultiplicity j =
        gamma (L*r) (finProdFinEquiv.symm j : Fin 3 × Fin 6).1 (finProdFinEquiv.symm j : Fin 3 × Fin 6).2 := by
      simp only [childMultiplicity,gamma]
      ring
    rw [hn]
    exact child_input_physical_six_power_isomorphic
      (finProdFinEquiv.symm j : Fin 3 × Fin 6).1 (finProdFinEquiv.symm j : Fin 3 × Fin 6).2 _
  have hsource : Isomorphic
      (sixSymmetrization (kronFin 18 (fun j ↦ (T j).kronPow (L*r*childMultiplicity j))))
      (sixSymmetrization (flatProduct (K := K) 5 (L*r))) :=
    (mme_sixSymmetrization_kronFin_isomorphic _).symm.trans
      ((kronFin_respects_isomorphic hfactor).trans
        (mme_sixSymmetrization_kronFin_isomorphic _))
  refine ⟨k,a,b,c,hres.trans hsource.1,?_⟩
  simpa only [v,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hbound

end MME.DWZC2Exact125

end


section

open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

namespace MME.DWZC1ChildGroupingFloor

open DWZC2Exact125

def count (j : Fin 18) : ℕ :=
  let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
  regionWeightCount rs.1 * (alphaCount rs.1 rs.2 + alphaCount rs.1 (Fin.rev rs.2))

noncomputable def rate (j : Fin 18) : ℝ :=
  let rs : Fin 3 × Fin 6 := finProdFinEquiv.symm j
  (childLogRate rs.1 rs.2 : ℝ) - 1 / 100000000000000

theorem coefficient_normalization (r : Fin 3) (s : Fin 6) :
    ((regionWeightCount r * (alphaCount r s + alphaCount r (Fin.rev s)) : ℕ) : ℝ) =
      1000000000000001000000000000000 * (childCoefficient r s : ℝ) := by
  simp only [childCoefficient, alpha]
  push_cast
  ring

theorem weighted_sum :
    (∑ j : Fin 18, (count j : ℝ) * rate j) =
      1000000000000001000000000000000 *
        ∑ r : Fin 3, ∑ s : Fin 6, (childCoefficient r s : ℝ) *
          ((childLogRate r s : ℝ) - 1 / 100000000000000) := by
  rw [← (finProdFinEquiv : Fin 3 × Fin 6 ≃ Fin 18).sum_comp]
  simp only [count, rate, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  simp only [coefficient_normalization, Finset.mul_sum, mul_assoc]

/-- Exact coefficient/data interface for the cofinal parent-value theorem.
The margin was proved over rational numbers by kernel evaluation. -/
theorem parent_floor_strict :
    (1000000000000001000000000000000 : ℝ) * (1091453673843 / 200000000000) <
      1000000000000001000000000000000 * (383836115467 / 500000000000) +
        ∑ j : Fin 18, (count j : ℝ) * rate j := by
  rw [weighted_sum]
  have h := mul_lt_mul_of_pos_left child_strict_log_margin
    (show (0 : ℝ) < 1000000000000001000000000000000 by norm_num)
  simpa only [mul_add] using h

theorem parent_floor :
    (1000000000000001000000000000000 : ℝ) * (1091453673843 / 200000000000) ≤
      1000000000000001000000000000000 * (383836115467 / 500000000000) +
        ∑ j : Fin 18, (count j : ℝ) * rate j :=
  parent_floor_strict.le

end MME.DWZC1ChildGroupingFloor

end


section

open MME MME.TensorObj MME.DWZRestrictedValue Module BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1ValueRate

theorem product_exp_pow {n : ℕ} (a : Fin n → ℝ) (m : Fin n → ℕ) :
    (∏ i, (Real.exp (a i)) ^ (m i)) =
      Real.exp (∑ i, (m i : ℝ) * a i) := by
  simp only [← Real.exp_nat_mul]
  exact (Real.exp_sum _ _).symm

/-- An exact finite certificate at the target base is enough; this keeps
the subsequent strict-below quantifier from consuming the numerical margin. -/
theorem sequence_of_cofinal_exact_witness
    {K : Type u} [Field K]
    (A : ℕ → TensorObj K 3) (length : ℕ → ℕ) (tau V : ℝ)
    (hV : 0 ≤ V)
    (h : ∀ cutoff : ℕ, ∃ m : ℕ, cutoff ≤ m ∧ cutoff ≤ length m ∧
      SixFiniteWitness TensorObj.Restrict (A m) (length m) tau V) :
    HasSixSequenceRate TensorObj.Restrict A length tau V := by
  refine ⟨hV, ?_⟩
  intro v hv hvV cutoff
  obtain ⟨m, hm, hlength, k, a, b, c, hres, hmass⟩ := h cutoff
  refine ⟨m, hm, hlength, k, a, b, c, hres, ?_⟩
  exact (pow_le_pow_left₀ hv.le hvV.le _).trans hmass

theorem combined_mass_bound {n : ℕ} (D t k : ℕ) (rho target : ℝ)
    (rate : Fin n → ℝ) (count : Fin n → ℕ)
    (hk : Real.exp ((2 : ℝ) * D * rho * t) ≤ k)
    (hfloor : (D : ℝ) * target ≤ D * rho + ∑ i, (count i : ℝ) * rate i) :
    (Real.exp target) ^ (6 * (D * t)) ≤
      ((k ^ 3 : ℕ) : ℝ) *
        ∏ i, (Real.exp (rate i)) ^ (6 * (count i * t)) := by
  have hkp : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk3 := pow_le_pow_left₀ (Real.exp_pos _).le hk 3
  rw [← Real.exp_nat_mul] at hk3
  rw [← Real.exp_nat_mul, product_exp_pow]
  have hsum : (∑ i, ((6 * (count i * t) : ℕ) : ℝ) * rate i) =
      6 * t * ∑ i, (count i : ℝ) * rate i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hsum, Nat.cast_pow]
  have hrate := mul_le_mul_of_nonneg_left hfloor (show 0 ≤ (6 : ℝ) * t by positivity)
  calc
    _ ≤ Real.exp (3 * ((2 : ℝ) * D * rho * t) +
        6 * t * ∑ i, (count i : ℝ) * rate i) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [hrate]
    _ = Real.exp (3 * ((2 : ℝ) * D * rho * t)) *
        Real.exp (6 * t * ∑ i, (count i : ℝ) * rate i) := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hk3 (Real.exp_pos _).le

end MME.DWZC1ValueRate

end


section

open MME MME.TensorObj MME.DWZRestrictedValue BigOperators Filter
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1ValueTransfer

/-- The finite tensor and child-value interfaces compose without exchanging
limsup quantifiers: choose an actual common child length beyond the eventual
tensor threshold, and retain every cubed direct-sum copy. -/
theorem cofinal_parent_value
    {K : Type u} [Field K] {n : ℕ}
    (A : ℕ → TensorObj K 3) (T : Fin n → TensorObj K 3)
    (D : ℕ) (hD : 0 < D) (count : Fin n → ℕ)
    (tau rho target : ℝ) (rate : Fin n → ℝ)
    (htensor : ∀ᶠ t : ℕ in atTop, ∃ k : ℕ,
      Real.exp ((2 : ℝ) * D * rho * t) ≤ k ∧
      TensorObj.Restrict
        (bigAdd (fun _ : Fin (k ^ 3) ↦
          sixSymmetrization (kronFin n (fun i ↦ (T i).kronPow (count i * t)))))
        (sixSymmetrization (A t)))
    (hchild : ∃ L : ℕ, 0 < L ∧ ∀ r : ℕ,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          (sixSymmetrization (kronFin n (fun i ↦ (T i).kronPow (count i * (L * r))))) ∧
        (∏ i, (Real.exp (rate i)) ^ (6 * (count i * (L * r)))) ≤
          ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau))
    (hfloor : (D : ℝ) * target ≤ D * rho + ∑ i, (count i : ℝ) * rate i) :
    HasSixSequenceRate TensorObj.Restrict A (fun t ↦ D * t) tau (Real.exp target) := by
  obtain ⟨L, hL, hcommon⟩ := hchild
  obtain ⟨t0, ht0⟩ := Filter.eventually_atTop.mp htensor
  apply DWZC1ValueRate.sequence_of_cofinal_exact_witness A (fun t ↦ D * t)
    tau (Real.exp target) (Real.exp_pos _).le
  intro cutoff
  let r := cutoff + t0
  let t := L * r
  have hrt : r ≤ t := Nat.le_mul_of_pos_left r hL
  have hcut : cutoff ≤ t := (Nat.le_add_right cutoff t0).trans hrt
  have hstart : t0 ≤ t := (Nat.le_add_left t0 cutoff).trans hrt
  have hlen : cutoff ≤ D * t := hcut.trans (Nat.le_mul_of_pos_left t hD)
  obtain ⟨copies, hcopies, hres⟩ := ht0 t hstart
  obtain ⟨k, a, b, c, hmat, hmass⟩ := DWZC1CopyValue.finite_MM_copies
    (sixSymmetrization (kronFin n (fun i ↦ (T i).kronPow (count i * t))))
    (copies ^ 3) tau
    (∏ i, (Real.exp (rate i)) ^ (6 * (count i * t))) (hcommon r)
  refine ⟨t, hcut, hlen, k, a, b, c, hmat.trans hres, ?_⟩
  exact (DWZC1ValueRate.combined_mass_bound D t copies rho target rate count
    hcopies hfloor).trans hmass

end MME.DWZC1ValueTransfer

end


section

open MME MME.TensorObj MME.DWZRestrictedValue
open MME.StothersFourth MME.CompleteSplit.CWFourth BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1Endpoint

open DWZC1FixedTensorExtraction

theorem original125_value {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 1 2 5)
      (constituentBasis K 5 1 2 5 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 5 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent125.parentProfile
      (790643 / 1000000) (Real.exp (1091453673843 / 200000000000)) := by
  have hchild : ∃ L : ℕ, 0 < L ∧ ∀ r : ℕ,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict (bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          (sixSymmetrization (kronFin 18
            (fun i ↦ (physicalChild 5 i).kronPow (childCount i * (L * r))))) ∧
        (∏ i, (Real.exp (DWZC1ChildGroupingFloor.rate i)) ^
          (6 * (childCount i * (L * r)))) ≤
          ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ (790643 / 1000000 : ℝ)) := by
    obtain ⟨L, hL, hcommon⟩ := DWZC2Exact125.actual_child_common_extractions (K := K)
    refine ⟨L, hL, ?_⟩
    intro r
    obtain ⟨k, a, b, c, hres, hbound⟩ := hcommon r
    refine ⟨k, a, b, c, ?_, ?_⟩
    · simpa only [flatProduct_eq] using hres
    · simpa only [DWZC1ChildGroupingFloor.rate, DWZC2Exact125.strictChildLogRate,
        childCount, DWZC2Exact125.childMultiplicity, Nat.mul_assoc] using hbound
  have hfloor : (1000000000000001000000000000000 : ℝ) *
      (1091453673843 / 200000000000) ≤
      1000000000000001000000000000000 * (383836115467 / 500000000000) +
        ∑ i, (childCount i : ℝ) * DWZC1ChildGroupingFloor.rate i :=
    DWZC1ChildGroupingFloor.parent_floor
  change HasSixSequenceRate TensorObj.Restrict
    (DWZC1LiteralAsymptotic.original (K := K) 5)
    (fun t ↦ 1000000000000001000000000000000 * t)
    (790643 / 1000000) (Real.exp (1091453673843 / 200000000000))
  exact DWZC1ValueTransfer.cofinal_parent_value
    (DWZC1LiteralAsymptotic.original (K := K) 5) (physicalChild 5)
    1000000000000001000000000000000 (by norm_num) childCount
    (790643 / 1000000) (383836115467 / 500000000000) (1091453673843 / 200000000000)
    DWZC1ChildGroupingFloor.rate
    (eventual_fixed_child_products_normalized (K := K) 5
      (383836115467 / 500000000000) (by norm_num) le_rfl)
    hchild hfloor

end MME.DWZC1Endpoint

end



open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 1 2 5)
      (constituentBasis K 5 1 2 5 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 5 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent125.parentProfile
      (790643 / 1000000) (Real.exp (1091453673843 / 200000000000)) := by
  exact MME.DWZC1Endpoint.original125_value
