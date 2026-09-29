-- Prove2me | solution 1 for mme_dwz_standard_prescribed_product_exact_once_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:52:59.456522+00:00
-- url     : https://prove2.me/submissions/4c3c4d55-88e5-447f-a8d9-bca2ecbf9250

import Theorems.Thm_mme_dwz_prescribed_Z_product_uniform_basis_shuffle
import Theorems.Thm_mme_dwz_generic_basis_label_hole_cover_tensor_repair
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME MME.TensorObj MME.DWZSquare MME.DWZRestrictedValue MME.DWZComponentRestriction
  Module PiTensorProduct BigOperators
open scoped Classical

universe u v
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZStandardProductRepair

theorem literal_restrict_selected {K : Type u} [Field K] (X : TensorObj K 3)
    {ι : Type u} {Block : Type v} [DecidableEq Block] (b : Basis ι K (X.V 2))
    (label : ι → Block) (blocks : Finset Block)
    (allowed : ι → Prop) (hmask : ∀ a, allowed a ↔ label a ∈ blocks) :
    TensorObj.Restrict
      { V := X.V
        t := PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label blocks)) X.t }
      (X.basisZAllowedSubtensor b allowed) := by
  classical
  let G := X.basisZAllowedGrading b allowed
  refine ⟨fun i ↦ (G.classOf i 0).subtype, ?_⟩
  have hp : b.constr K (fun a ↦ if allowed a then b a else 0) =
      basisLabelProjection b label blocks := by
    unfold basisLabelProjection
    congr 1
    funext a
    rw [hmask a]
    by_cases ha : label a ∈ blocks <;> simp [ha]
  simpa only [hp] using mme_basisZAllowed_blockSubtensor_inclusion_tensor X b allowed

end MME.DWZStandardProductRepair

theorem solution {K : Type u} [Field K] (k : ℕ)
    (T : Fin k → TensorObj K 3) {I : Fin k → Fin 3 → Type u}
    (b : ∀ c i, Basis (I c i) K ((T c).V i)) (t : Fin k → ℕ)
    (grade : ∀ c, I c 2 → Fin (t c))
    (p : ∀ c, IntegerZSplitProfile (t c)) (m : Fin k → ℕ) :
    let Coord := fun c ↦ {w : PowIndex (I c 2) ((p c).length (m c)) //
      prescribedZWord (grade c) (p c) (m c) w}
    let Block := fun c ↦ {w : PowIndex (Fin (t c)) ((p c).length (m c)) //
      prescribedZWord id (p c) (m c) w}
    let S := fun c ↦ prescribedZPower (T c) (b c 2) (grade c) (p c) (m c)
    let G := fun c ↦ ((T c).kronPow ((p c).length (m c))).basisZAllowedGrading
      (kronPowModeBasis (T c) 2 (b c 2) ((p c).length (m c)))
      (prescribedZWord (grade c) (p c) (m c))
    let P := TensorObj.kronFin k S
    ∃ factorBasis : ∀ c, Basis (Coord c) K ((G c).classOf 2 0),
    ∃ label : (∀ c, Coord c) → (∀ c, Block c),
      (∀ c w, (factorBasis c w : ((T c).kronPow ((p c).length (m c))).V 2) =
        kronPowModeBasis (T c) 2 (b c 2) ((p c).length (m c)) w.1) ∧
      (∀ w c, (label w c).1 = PowIndex.ofFun ((p c).length (m c))
        (fun r ↦ grade c (PowIndex.get ((p c).length (m c)) (w c).1 r))) ∧
      (Nonempty (∀ c, Coord c) → Function.Surjective label) ∧
      ∀ (_ : Nonempty (∀ c, Coord c)) (N ell s : ℕ)
        (_ : 0 < N) (_ : 0 < ell)
        (copies : Fin s → BrokenBlockCopy (∀ c, Block c)),
        Fintype.card (∀ c, Block c) ≤ 2 ^ (N * ell) →
        ((N * ell + 1 : ℕ) : ℝ) ≤ ∑ j : Fin s, nonholeFraction (copies j) →
        let B := kronFinModePiBasis k S 2 factorBasis
        let broken : Fin s → TensorObj K 3 := fun j ↦
          { V := P.V
            t := PiTensorProduct.map
              (Function.update (fun _ ↦ LinearMap.id) 2
                (basisLabelProjection B label (copies j).nonholes)) P.t }
        TensorObj.Restrict P (TensorObj.bigAdd broken) ∧
        ∀ allowed : Fin s → (∀ c, Coord c) → Prop,
          (∀ j w, allowed j w ↔ label w ∈ (copies j).nonholes) →
          (∀ j, TensorObj.Restrict (broken j) (P.basisZAllowedSubtensor B (allowed j))) ∧
          TensorObj.Restrict P (TensorObj.bigAdd
            (fun j ↦ P.basisZAllowedSubtensor B (allowed j))) := by
  classical
  dsimp only
  let S := fun c ↦ prescribedZPower (T c) (b c 2) (grade c) (p c) (m c)
  let P := TensorObj.kronFin k S
  obtain ⟨factorBasis, label, system, hBasis, hlabel, hsurj, _, hshuffle⟩ :=
    mme_dwz_prescribed_Z_product_uniform_basis_shuffle k T b t grade p m
  refine ⟨factorBasis, label, hBasis, hlabel, hsurj, ?_⟩
  intro hcoord N ell s hN hell copies hcard hsum
  let B := kronFinModePiBasis k S 2 factorBasis
  letI : Nonempty (∀ c, {w : PowIndex (Fin (t c)) ((p c).length (m c)) //
      prescribedZWord id (p c) (m c) w}) := ⟨label (Classical.choice hcoord)⟩
  choose F perm hF _ hFB hcov using hshuffle
  have hr := mme_dwz_generic_basis_label_hole_cover_tensor_repair P B label system
    (fun g i ↦ (F g i).toLinearMap) perm hFB hcov hF N ell s hN hell copies hcard hsum
  obtain ⟨_, _, _, _, _, _, _, hrepair⟩ := hr
  refine ⟨hrepair, ?_⟩
  intro allowed hmask
  have hpad (j : Fin s) := MME.DWZStandardProductRepair.literal_restrict_selected
    P B label (copies j).nonholes (allowed j) (hmask j)
  exact ⟨hpad, hrepair.trans (mme_bigAdd_mono_restrict hpad)⟩
