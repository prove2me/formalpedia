-- Prove2me | solution 1 for mme_CW_atomic_fourth_component_grouping_projection_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:56:35.040146+00:00
-- url     : https://prove2.me/submissions/d6cb82e9-b55b-4cbe-95f7-f25d4348594e

import Theorems.Thm_mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_dwz_simultaneous_CW_projection_data

open MME MME.TensorObj MME.StothersFourth MME.DWZStep1Support MME.DWZSimultaneous
open Module PiTensorProduct TensorProduct BigOperators
universe u v
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace MME.DWZAtomicFourth
variable {K : Type u} [Field K] {d : ℕ}

noncomputable def familyToPow (X Y : TensorObj K d)
    (φ : ∀ i, X.V i ≃ₗ[K] Y.V i) :
    ∀ n i, (kronFin n (fun _ ↦ X)).V i ≃ₗ[K] (Y.kronPow n).V i
  | 0, _ => LinearEquiv.refl K K
  | n + 1, i => TensorProduct.congr (φ i) (familyToPow X Y φ n i)

theorem familyToPow_tensor (X Y : TensorObj K d)
    (φ : ∀ i, X.V i ≃ₗ[K] Y.V i)
    (hφ : PiTensorProduct.map (fun i ↦ (φ i).toLinearMap) X.t = Y.t) (n : ℕ) :
    PiTensorProduct.map (fun i ↦ (familyToPow X Y φ n i).toLinearMap)
      (kronFin n (fun _ ↦ X)).t = (Y.kronPow n).t := by
  induction n with
  | zero =>
      change PiTensorProduct.map (fun _ : Fin d ↦ LinearMap.id)
        (TensorObj.oneObj (K := K) (d := d)).t = _
      rw [PiTensorProduct.map_id]
      rfl
  | succ n ih =>
      change PiTensorProduct.map
        (fun i ↦ TensorProduct.map (φ i).toLinearMap
          (familyToPow X Y φ n i).toLinearMap)
        (interchange X.t (kronFin n (fun _ ↦ X)).t) = _
      rw [TypeGrading.kronMap_interchange, hφ, ih]
      rfl

private theorem pi_basis_succ (T : TensorObj K d) (i : Fin d)
    {I : Type u} (b : Basis I K (T.V i)) (n : ℕ) (w : Fin (n+1) → I) :
    kronFinModePiBasis (n+1) (fun _ ↦ T) i (fun _ ↦ b) w =
      b (w 0) ⊗ₜ[K] kronFinModePiBasis n (fun _ ↦ T) i (fun _ ↦ b) (Fin.tail w) := by
  exact (Basis.reindex_apply
    (b.tensorProduct (kronFinModePiBasis n (fun _ ↦ T) i (fun _ ↦ b)))
    (Fin.consEquiv (fun _ : Fin (n+1) ↦ I)) w).trans
      (Basis.tensorProduct_apply b
        (kronFinModePiBasis n (fun _ ↦ T) i (fun _ ↦ b)) (w 0) (Fin.tail w))

private theorem word_basis_succ (T : TensorObj K d) (i : Fin d)
    {I : Type u} (b : Basis I K (T.V i)) (n : ℕ) (w : Fin (n+1) → I) :
    kronPowModeWordBasis T i b (n+1) w =
      b (w 0) ⊗ₜ[K] kronPowModeWordBasis T i b n (Fin.tail w) := by
  exact (Basis.reindex_apply
    (b.tensorProduct (kronPowModeWordBasis T i b n))
    (Fin.consEquiv (fun _ : Fin (n+1) ↦ I)) w).trans
      (Basis.tensorProduct_apply b (kronPowModeWordBasis T i b n) (w 0) (Fin.tail w))

theorem familyToPow_basis (X Y : TensorObj K d)
    (φ : ∀ i, X.V i ≃ₗ[K] Y.V i) (i : Fin d)
    {I J : Type u} (b : Basis I K (X.V i)) (c : Basis J K (Y.V i))
    (e : I → J) (he : ∀ x, φ i (b x) = c (e x))
    (n : ℕ) (w : Fin n → I) :
    familyToPow X Y φ n i (kronFinModePiBasis n (fun _ ↦ X) i (fun _ ↦ b) w) =
      kronPowModeWordBasis Y i c n (fun t ↦ e (w t)) := by
  induction n with
  | zero =>
      change (Basis.singleton (Fin 0 → I) K) w =
        (Basis.singleton (Fin 0 → J) K) (fun t ↦ e (w t))
      rw [Basis.singleton_apply, Basis.singleton_apply]
  | succ n ih =>
      rw [pi_basis_succ, word_basis_succ]
      change TensorProduct.congr (φ i) (familyToPow X Y φ n i)
        (b (w 0) ⊗ₜ[K] kronFinModePiBasis n (fun _ ↦ X) i (fun _ ↦ b) (Fin.tail w)) = _
      rw [TensorProduct.congr_tmul, he, ih]
      rfl

def router (q N : ℕ) :
    (Fin (N*4) → ULift.{u} (Fin (q+2))) ≃
      (Fin N → ULift.{u} ((Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2)))) where
  toFun w t := ⟨(((w (finProdFinEquiv (t, 0))).down, (w (finProdFinEquiv (t, 1))).down),
    ((w (finProdFinEquiv (t, 2))).down, (w (finProdFinEquiv (t, 3))).down))⟩
  invFun w z :=
    let tr := finProdFinEquiv.symm z
    ⟨![(w tr.1).down.1.1, (w tr.1).down.1.2,
      (w tr.1).down.2.1, (w tr.1).down.2.2] tr.2⟩
  left_inv w := by
    funext z
    obtain ⟨⟨t,r⟩, rfl⟩ := finProdFinEquiv.surjective z
    fin_cases r <;> simp
  right_inv w := by
    funext t
    simp

theorem atomic_fourth_tensor_basis (q N : ℕ) :
    ∃ Φ : ∀ i, ((CWObj K q).kronPow (N*4)).V i ≃ₗ[K]
        ((cwFourthObj K q).kronPow N).V i,
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap)
        ((CWObj K q).kronPow (N*4)).t = ((cwFourthObj K q).kronPow N).t ∧
      ∀ i (w : Fin (N*4) → ULift.{u} (Fin (q+2))),
        Φ i (kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N*4) w) =
        kronPowModeWordBasis (cwFourthObj K q) i
          ((cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm) N (router q N w) := by
  obtain ⟨β, hβ, hb, _⟩ :=
    mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades (K := K) q
  let pos : Fin (N*4) ≃ (Σ _ : Fin N, Fin 4) :=
    finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin N) (Fin 4)).symm
  obtain ⟨α, hα, ha⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis
    (CWObj K q) (fun i ↦ (cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
    (fun _ : Fin N ↦ 4) pos
  refine ⟨fun i ↦ (α i).trans
    (familyToPow ((CWObj K q).kronPow 4) (cwFourthObj K q) β N i), ?_, ?_⟩
  · change PiTensorProduct.map
      (fun i ↦ (familyToPow ((CWObj K q).kronPow 4) (cwFourthObj K q) β N i).toLinearMap
        ∘ₗ (α i).toLinearMap) _ = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hα]
    exact familyToPow_tensor _ _ β hβ N
  · intro i w
    change familyToPow ((CWObj K q).kronPow 4) (cwFourthObj K q) β N i
      (α i (kronPowModeWordBasis (CWObj K q) i
        ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N*4) w)) = _
    rw [ha]
    exact familyToPow_basis _ _ β i
      (kronPowModeWordBasis (CWObj K q) i
        ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) 4)
      ((cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm)
      (fun x ↦ ULift.up (((x 0).down, (x 1).down), ((x 2).down, (x 3).down)))
      (by
        intro x
        simpa only [Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply]
          using (hb i x)) N (fun t r ↦ w (pos.symm ⟨t,r⟩))

theorem router_grade (q N : ℕ) (w : Fin (N*4) → ULift.{u} (Fin (q+2))) (t : Fin N) :
    (cwFourthPairGrade q (router q N w t).down).val =
      ∑ r : Fin 4, (label q 3 N w t r).val := by
  change ((label q 3 N w t 0).val + (label q 3 N w t 1).val) +
    ((label q 3 N w t 2).val + (label q 3 N w t 3).val) = _
  simp [Fin.sum_univ_succ, Nat.add_assoc]

theorem router_left (q N : ℕ) (w : Fin (N*4) → ULift.{u} (Fin (q+2))) (t : Fin N) :
    cwSquarePairGrade q (router q N w t).down.1 = fourthLeftTag (label q 3 N w t) := by
  apply Fin.ext
  rfl

theorem router_graded {C : Type v} {q N k : ℕ}
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (j : Fin k) (i : Fin 3) (w : Fin (N*4) → ULift.{u} (Fin (q+2))) :
    Graded component shape j i (label q 3 N w) ↔
      ∀ t, (cwFourthPairGrade q (router q N w t).down).val = shape (component j t) i := by
  change (∀ t, ∑ r : Fin 4, (label q 3 N w t r).val = shape (component j t) i) ↔ _
  simp only [router_grade]

theorem router_profile {C : Type v} [DecidableEq C] {q N k : ℕ}
    (component : Fin k → Fin N → C) (mu : Fin 3 → C → Fin 5 → ℕ)
    (j : Fin k) (i : Fin 3) (w : Fin (N*4) → ULift.{u} (Fin (q+2))) :
    Profile component fourthLeftTag mu j i (label q 3 N w) ↔
      ∀ c a, Fintype.card {t : Fin N // component j t = c ∧
        cwSquarePairGrade q (router q N w t).down.1 = a} = mu i c a := by
  simp only [Profile, router_left]

def groupedRouter (q : ℕ) {N k : ℕ} (count : Fin k → ℕ)
    (positions : Fin N ≃ (Σ c, Fin (count c))) :
    (Fin (N*4) → ULift.{u} (Fin (q+2))) ≃
      (∀ c, Fin (count c) →
        ULift.{u} ((Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2)))) :=
  (router q N).trans
    { toFun := fun w c r ↦ w (positions.symm ⟨c,r⟩)
      invFun := fun w t ↦ w (positions t).1 (positions t).2
      left_inv := by
        intro w
        funext t
        exact congrArg w (positions.symm_apply_apply t)
      right_inv := by
        intro w
        funext c r
        exact congrArg (fun a : Σ c, Fin (count c) ↦ w a.1 a.2)
          (positions.apply_symm_apply ⟨c,r⟩) }

theorem grouped_tensor_basis (q : ℕ) {N k : ℕ} (count : Fin k → ℕ)
    (positions : Fin N ≃ (Σ c, Fin (count c))) :
    ∃ Φ : ∀ i, ((CWObj K q).kronPow (N*4)).V i ≃ₗ[K]
        (kronFin k (fun c ↦ (cwFourthObj K q).kronPow (count c))).V i,
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap)
        ((CWObj K q).kronPow (N*4)).t =
          (kronFin k (fun c ↦ (cwFourthObj K q).kronPow (count c))).t ∧
      ∀ i (w : Fin (N*4) → ULift.{u} (Fin (q+2))),
        Φ i (kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N*4) w) =
        kronFinModePiBasis k (fun c ↦ (cwFourthObj K q).kronPow (count c)) i
          (fun c ↦ kronPowModeWordBasis (cwFourthObj K q) i
            ((cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm) (count c))
          (groupedRouter q count positions w) := by
  obtain ⟨α, ht, hb⟩ := atomic_fourth_tensor_basis (K := K) q N
  obtain ⟨β, hβ, hβb⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis
    (cwFourthObj K q) (fun i ↦ (cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm)
    count positions
  refine ⟨fun i ↦ (α i).trans (β i), ?_, ?_⟩
  · change PiTensorProduct.map (fun i ↦ (β i).toLinearMap ∘ₗ (α i).toLinearMap) _ = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, ht, hβ]
  · intro i w
    change β i (α i _) = _
    rw [hb, hβb]
    rfl

end MME.DWZAtomicFourth

open MME.DWZAtomicFourth

theorem solution {K : Type u} [Field K] (q : ℕ) {N k : ℕ}
    (count : Fin k → ℕ) (positions : Fin N ≃ (Σ c, Fin (count c))) :
    let T := (CWObj K q).kronPow (N*4)
    let U := kronFin k (fun c ↦ (cwFourthObj K q).kronPow (count c))
    let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N*4)
    let D := fun i ↦ kronFinModePiBasis k (fun c ↦ (cwFourthObj K q).kronPow (count c)) i
      (fun c ↦ kronPowModeWordBasis (cwFourthObj K q) i
        ((cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm) (count c))
    ∃ e : (Fin (N*4) → ULift.{u} (Fin (q+2))) ≃
        (∀ c, Fin (count c) →
          ULift.{u} ((Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2)))),
      (∀ w c r, let t := positions.symm ⟨c,r⟩
        (e w c r).down =
          (((w (finProdFinEquiv (t,0))).down, (w (finProdFinEquiv (t,1))).down),
           ((w (finProdFinEquiv (t,2))).down, (w (finProdFinEquiv (t,3))).down))) ∧
      ∃ Φ : ∀ i, T.V i ≃ₗ[K] U.V i,
        PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) T.t = U.t ∧
        (∀ i w, Φ i (B i w) = D i (e w)) ∧
        (∀ w c r, (cwFourthPairGrade q (e w c r).down).val =
          ∑ s : Fin 4, (label q 3 N w (positions.symm ⟨c,r⟩) s).val) ∧
        (∀ w c r, cwSquarePairGrade q (e w c r).down.1 =
          fourthLeftTag (label q 3 N w (positions.symm ⟨c,r⟩))) ∧
        ∀ P : Fin 3 → (Fin (N*4) → ULift.{u} (Fin (q+2))) → Prop,
          let Q := fun i w ↦ P i (e.symm w)
          ∃ f : ∀ i, (T.basisAllAllowedGrading B P).classOf i 0 ≃ₗ[K]
              (U.basisAllAllowedGrading D Q).classOf i 0,
            PiTensorProduct.map (fun i ↦ (f i).toLinearMap)
              (T.basisAllAllowedSubtensor B P).t = (U.basisAllAllowedSubtensor D Q).t ∧
            (∀ i w, f i ((T.basisAllAllowedGrading B P).blockProj i 0 (B i w)) =
              (U.basisAllAllowedGrading D Q).blockProj i 0 (D i (e w))) ∧
            ∀ i x, (f i x : U.V i) = Φ i (x : T.V i) := by
  dsimp only
  obtain ⟨Φ, ht, hb⟩ := grouped_tensor_basis (K := K) q count positions
  refine ⟨groupedRouter q count positions, fun _ _ _ ↦ rfl, Φ, ht, hb, ?_, ?_, ?_⟩
  · intro w c r
    exact router_grade q N w (positions.symm ⟨c,r⟩)
  · intro w c r
    exact router_left q N w (positions.symm ⟨c,r⟩)
  · intro P
    exact mme_basisAllAllowedSubtensor_basis_equiv_transport _ _ _ _ Φ
      (fun _ ↦ groupedRouter q count positions) hb ht P
      (fun i w ↦ P i ((groupedRouter q count positions).symm w))
      (fun i w ↦ by simp)


