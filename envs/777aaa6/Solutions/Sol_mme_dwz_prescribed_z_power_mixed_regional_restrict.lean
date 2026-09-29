-- Prove2me | solution 1 for mme_dwz_prescribed_z_power_mixed_regional_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T10:14:35.744499+00:00
-- url     : https://prove2.me/submissions/a8c9f4ba-82b8-4677-abff-6879cfb080ca

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_kron_pow_word_reindex

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open PiTensorProduct TensorProduct BigOperators
open MME.TensorObj
open scoped Classical

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZPositiveComponent

private theorem disallowed_Z_projection_zero
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop) [DecidablePred allowed]
    (j : ι) (hj : ¬ allowed j) :
    (T.basisZAllowedGrading bZ allowed).blockProj 2 0 (bZ j) = 0 := by
  classical
  let G := T.basisZAllowedGrading bZ allowed
  have hx : bZ j ∈ G.classOf 2 1 := by
    change bZ j ∈ cwBasisGrade bZ
      (fun k ↦ if allowed k then (0 : Fin 2) else 1) 1
    exact Submodule.subset_span
      ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
  exact (G.is_internal 2).ofBijective_coeLinearMap_of_mem_ne
    (show (1 : Fin 2) ≠ 0 by decide) hx


theorem word_basis_succ {K : Type u} [Field K] (T : TensorObj K 3)
    (i : Fin 3) {I : Type u} (b : Basis I K (T.V i))
    (n : ℕ) (w : Fin (n + 1) → I) :
    kronPowModeWordBasis T i b (n + 1) w =
      b (w 0) ⊗ₜ[K] kronPowModeWordBasis T i b n (Fin.tail w) := by
  letI : IsScalarTower K K (T.V i) := IsScalarTower.of_algebraMap_smul (by simp)
  exact (Basis.reindex_apply (b.tensorProduct (kronPowModeWordBasis T i b n))
    (Fin.consEquiv (fun _ : Fin (n+1) ↦ I)) w).trans
      (Basis.tensorProduct_apply b (kronPowModeWordBasis T i b n) (w 0) (Fin.tail w))

theorem recursive_basis_succ {K : Type u} [Field K] (T : TensorObj K 3)
    (i : Fin 3) {I : Type u} (b : Basis I K (T.V i))
    (n : ℕ) (w : PowIndex I (n + 1)) :
    kronPowModeBasis T i b (n + 1) w =
      b w.1 ⊗ₜ[K] kronPowModeBasis T i b n w.2 := by
  letI : IsScalarTower K K (T.V i) := IsScalarTower.of_algebraMap_smul (by simp)
  exact Basis.tensorProduct_apply b (kronPowModeBasis T i b n) w.1 w.2

theorem word_basis_eq_recursive
    {K : Type u} [Field K] (T : TensorObj K 3)
    (i : Fin 3) {I : Type u} (b : Basis I K (T.V i))
    (n : ℕ) (w : Fin n → I) :
    kronPowModeWordBasis T i b n w =
      kronPowModeBasis T i b n (PowIndex.ofFun n w) := by
  induction n with
  | zero =>
      exact (Basis.singleton_apply _ K w).trans
        (Basis.singleton_apply _ K _).symm
  | succ n ih =>
      rw [word_basis_succ, recursive_basis_succ]
      change b (w 0) ⊗ₜ[K] kronPowModeWordBasis T i b n (fun r ↦ w r.succ) =
        b (w 0) ⊗ₜ[K] kronPowModeBasis T i b n (PowIndex.ofFun n (fun r ↦ w r.succ))
      rw [ih]


theorem family_basis_succ
    {K : Type u} [Field K] {k : ℕ}
    (X : Fin (k+1) → TensorObj K 3) (i : Fin 3)
    {I : Fin (k+1) → Type u} (b : ∀ r, Basis (I r) K ((X r).V i))
    (w : ∀ r, I r) :
    kronFinModePiBasis (k+1) X i b w =
      b 0 (w 0) ⊗ₜ[K] kronFinModePiBasis k (fun r ↦ X r.succ) i
        (fun r ↦ b r.succ) (fun r ↦ w r.succ) := by
  change (((b 0).tensorProduct (kronFinModePiBasis k
    (fun r ↦ X r.succ) i (fun r ↦ b r.succ))).reindex (Fin.consEquiv I)) w = _
  rw [Basis.reindex_apply, Fin.consEquiv_symm_apply, Basis.tensorProduct_apply]
  rfl

theorem family_word_basis_eq_recursive
    {K : Type u} [Field K] (T : TensorObj K 3)
    (i : Fin 3) {I : Type u} (b : Basis I K (T.V i))
    (k : ℕ) (n : Fin k → ℕ) (w : ∀ r, Fin (n r) → I) :
    kronFinModePiBasis k (fun r ↦ T.kronPow (n r)) i
      (fun r ↦ kronPowModeWordBasis T i b (n r)) w =
    kronFinModePiBasis k (fun r ↦ T.kronPow (n r)) i
      (fun r ↦ kronPowModeBasis T i b (n r))
      (fun r ↦ PowIndex.ofFun (n r) (w r)) := by
  induction k with
  | zero =>
    exact (Basis.singleton_apply _ K w).trans
      (Basis.singleton_apply _ K _).symm
  | succ k ih =>
    rw [family_basis_succ, family_basis_succ, word_basis_eq_recursive, ih]

theorem grouped_grade_count
    {I : Type u} {t N k : ℕ} (grade : I → Fin t)
    (n : Fin k → ℕ) (positions : Fin N ≃ Σ r, Fin (n r))
    (w : PowIndex I N) (a : Fin t) :
    leftGradeCount grade w a =
      ∑ r, leftGradeCount grade
        (PowIndex.ofFun (n r) (fun s ↦ PowIndex.get N w (positions.symm ⟨r,s⟩))) a := by
  classical
  simp only [leftGradeCount, Finset.card_filter, PowIndex.get_ofFun]
  calc
    _ = ∑ rs : Σ r, Fin (n r),
        if grade (PowIndex.get N w (positions.symm rs)) = a then 1 else 0 := by
      exact (Equiv.sum_comp positions.symm
        (fun s ↦ if grade (PowIndex.get N w s) = a then 1 else 0)).symm
    _ = _ := Fintype.sum_sigma _

/-- The raw power maps to the independently projected regional powers with
the literal grouped recursive-word action. No entropy or dimension argument
is used in constructing these maps. -/
theorem regional_projection_maps
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    {t N k : ℕ} (grade : I 2 → Fin t)
    (p : Fin k → IntegerZSplitProfile t) (m : Fin k → ℕ)
    (positions : Fin N ≃ Σ r, Fin ((p r).length (m r))) :
    let X := fun r ↦ T.kronPow ((p r).length (m r))
    let Y := fun r ↦ prescribedZPower T (b 2) grade (p r) (m r)
    let B := fun r ↦ kronPowModeBasis T 2 (b 2) ((p r).length (m r))
    let G := fun r ↦ (X r).basisZAllowedGrading (B r)
      (prescribedZWord grade (p r) (m r))
    ∃ f : ∀ i, (T.kronPow N).V i →ₗ[K] (kronFin k Y).V i,
      PiTensorProduct.map f (T.kronPow N).t = (kronFin k Y).t ∧
      ∀ w : PowIndex (I 2) N,
        f 2 (kronPowModeBasis T 2 (b 2) N w) =
          kronFinFamilyModeMap k X Y (fun r i ↦ (G r).blockProj i 0) 2
            (kronFinModePiBasis k X 2 B
              (fun r ↦ PowIndex.ofFun ((p r).length (m r))
                (fun s ↦ PowIndex.get N w (positions.symm ⟨r,s⟩)))) := by
  classical
  dsimp only
  let n := fun r ↦ (p r).length (m r)
  let X := fun r ↦ T.kronPow (n r)
  let Y := fun r ↦ prescribedZPower T (b 2) grade (p r) (m r)
  let B := fun r ↦ kronPowModeBasis T 2 (b 2) (n r)
  let G := fun r ↦ (X r).basisZAllowedGrading (B r)
    (prescribedZWord grade (p r) (m r))
  let proj := fun r i ↦ (G r).blockProj i 0
  obtain ⟨E, ht, hb⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis
    T b n positions
  let F := kronFinFamilyModeMap k X Y proj
  refine ⟨fun i ↦ (F i).comp (E i).toLinearMap, ?_, ?_⟩
  · rw [PiTensorProduct.map_comp, LinearMap.comp_apply, ht]
    exact kronFinFamilyModeMap_preserves_tensor X Y proj (fun _ ↦ rfl)
  · intro w
    change F 2 (E 2 (kronPowModeBasis T 2 (b 2) N w)) = _
    have hword : kronPowModeBasis T 2 (b 2) N w =
        kronPowModeWordBasis T 2 (b 2) N (PowIndex.get N w) := by
      rw [word_basis_eq_recursive, PowIndex.ofFun_get]
    rw [hword, hb, family_word_basis_eq_recursive]


/-- Exact finite mixed-profile decomposition. The parent profile is the
count-weighted mixture of the regional profiles, with all denominators and
zero-length regions retained explicitly. -/
theorem mixed_regional_profile_restrict
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    {t k : ℕ} (grade : I 2 → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ)
    (region : Fin k → IntegerZSplitProfile t) (multiple : Fin k → ℕ)
    (hlength : p.length m = ∑ r, (region r).length (multiple r))
    (hcounts : ∀ a, p.count a * m =
      ∑ r, (region r).count a * multiple r) :
    TensorObj.Restrict
      (kronFin k (fun r ↦ prescribedZPower T (b 2) grade (region r) (multiple r)))
      (prescribedZPower T (b 2) grade p m) := by
  classical
  let n := fun r ↦ (region r).length (multiple r)
  let positions : Fin (p.length m) ≃ Σ r, Fin (n r) :=
    (finCongr hlength).trans finSigmaFinEquiv.symm
  let X := fun r ↦ T.kronPow (n r)
  let Y := fun r ↦ prescribedZPower T (b 2) grade (region r) (multiple r)
  let B := fun r ↦ kronPowModeBasis T 2 (b 2) (n r)
  let G := fun r ↦ (X r).basisZAllowedGrading (B r)
    (prescribedZWord grade (region r) (multiple r))
  let proj := fun r i ↦ (G r).blockProj i 0
  obtain ⟨f, hf, hw⟩ := regional_projection_maps T b grade region multiple positions
  apply mme_restrict_basisZAllowedSubtensor_of_vanishes
    (T.kronPow (p.length m)) (kronFin k Y)
    (kronPowModeBasis T 2 (b 2) (p.length m)) (prescribedZWord grade p m) f hf
  intro w hnot
  rw [hw]
  let words := fun r ↦ PowIndex.ofFun (n r)
    (fun s ↦ PowIndex.get (p.length m) w (positions.symm ⟨r,s⟩))
  have hbad : ∃ r, ¬ prescribedZWord grade (region r) (multiple r) (words r) := by
    by_contra h
    push_neg at h
    apply hnot
    intro a
    rw [grouped_grade_count grade n positions w a]
    exact (Finset.sum_congr rfl (fun r _ ↦ h r a)).trans (hcounts a).symm
  apply kronFinFamilyModeMap_basis_eq_zero_of_exists X Y 2 B proj words
  obtain ⟨r, hr⟩ := hbad
  exact ⟨r, disallowed_Z_projection_zero (X r) (B r) _ (words r) hr⟩

theorem mixed_profile_length_eq
    {t k : ℕ} (p : IntegerZSplitProfile t) (m : ℕ)
    (region : Fin k → IntegerZSplitProfile t) (multiple : Fin k → ℕ)
    (hcounts : ∀ a, p.count a * m =
      ∑ r, (region r).count a * multiple r) :
    p.length m = ∑ r, (region r).length (multiple r) := by
  calc
    p.length m = ∑ a, p.count a * m := by
      rw [← Finset.sum_mul, p.count_sum]
      rfl
    _ = ∑ a, ∑ r, (region r).count a * multiple r :=
      Finset.sum_congr rfl (fun a _ ↦ hcounts a)
    _ = ∑ r, ∑ a, (region r).count a * multiple r := Finset.sum_comm
    _ = _ := by simp only [← Finset.sum_mul, IntegerZSplitProfile.count_sum,
      IntegerZSplitProfile.length]

end MME.DWZPositiveComponent


open MME MME.DWZComponentRestriction MME.DWZRestrictedValue MME.TensorObj Module BigOperators

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    {t k : ℕ} (grade : I 2 → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ)
    (region : Fin k → IntegerZSplitProfile t) (multiple : Fin k → ℕ)
    (hlength : p.length m = ∑ r, (region r).length (multiple r))
    (hcounts : ∀ a, p.count a * m =
      ∑ r, (region r).count a * multiple r) :
    TensorObj.Restrict
      (kronFin k (fun r ↦ prescribedZPower T (b 2) grade (region r) (multiple r)))
      (prescribedZPower T (b 2) grade p m) := by
  exact MME.DWZPositiveComponent.mixed_regional_profile_restrict T b grade p m region multiple hlength hcounts

