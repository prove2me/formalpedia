-- Prove2me | solution 1 for mme_tensor_family_direct_sum_restrict_of_mixed_maps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:43:33.833536+00:00
-- url     : https://prove2.me/submissions/628d9e22-fe78-4423-901b-441dd127c3df

import Mathlib.LinearAlgebra.PiTensorProduct
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_tensor_rank

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

variable {K : Type u} [Field K]

private theorem map_sum_modes
    {k : ℕ} {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, Fin k → V i →ₗ[K] W i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i ↦ ∑ j, f i j) x =
      ∑ js : Fin 3 → Fin k,
        PiTensorProduct.map (fun i ↦ f i (js i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul]
      simp only [PiTensorProduct.map_tprod, LinearMap.coe_sum,
        Finset.sum_apply]
      rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _]
      rw [Finset.smul_sum]
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, Finset.sum_add_distrib]

private theorem bigAdd_t_eq_sum_slot :
    ∀ (k : ℕ) (B : Fin k → TensorObj K 3),
      (TensorObj.bigAdd B).t =
        ∑ j : Fin k,
          PiTensorProduct.map
            (fun i ↦ gradedBigAddSlot k B j i) (B j).t
  | 0, _ => by
      change (TensorObj.zeroObj : TensorObj K 3).t = ∑ j : Fin 0, _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rfl
  | 1, B => by
      change (B 0).t =
        ∑ j : Fin 1,
          PiTensorProduct.map
            (fun i ↦ gradedBigAddSlot 1 B j i) (B j).t
      rw [Fin.sum_univ_one]
      change (B 0).t =
        PiTensorProduct.map (fun _ ↦ LinearMap.id) (B 0).t
      rw [PiTensorProduct.map_id]
      rfl
  | n + 2, B => by
      change PiTensorProduct.map (fun i ↦
              LinearMap.inl K ((B 0).V i)
                ((TensorObj.bigAdd (fun j ↦ B j.succ)).V i)) (B 0).t +
          PiTensorProduct.map (fun i ↦
              LinearMap.inr K ((B 0).V i)
                ((TensorObj.bigAdd (fun j ↦ B j.succ)).V i))
            (TensorObj.bigAdd (fun j ↦ B j.succ)).t =
        ∑ j : Fin (n + 2),
          PiTensorProduct.map
            (fun i ↦ gradedBigAddSlot (n + 2) B j i) (B j).t
      rw [Fin.sum_univ_succ]
      rw [bigAdd_t_eq_sum_slot (n + 1) (fun j ↦ B j.succ)]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl

theorem solution
    (S : TensorObj K 3) {k : ℕ}
    (B : Fin k → TensorObj K 3)
    (f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K] (B j).V i)
    (hDiagonal : ∀ j : Fin k,
      PiTensorProduct.map (f j) S.t = (B j).t)
    (hMixedZero : ∀ js : Fin 3 → Fin k,
      (∀ j : Fin k, js ≠ fun _ ↦ j) →
      PiTensorProduct.map (fun i ↦ f (js i) i) S.t = 0) :
    TensorObj.Restrict (TensorObj.bigAdd B) S := by
  classical
  let slotMap : ∀ i : Fin 3, Fin k →
      S.V i →ₗ[K] (TensorObj.bigAdd B).V i :=
    fun i j ↦ (gradedBigAddSlot k B j i).comp (f j i)
  refine ⟨fun i ↦ ∑ j, slotMap i j, ?_⟩
  rw [map_sum_modes slotMap S.t]
  rw [bigAdd_t_eq_sum_slot]
  let constChoice : Fin k → Fin 3 → Fin k := fun j _ ↦ j
  let diagonalChoices : Finset (Fin 3 → Fin k) :=
    Finset.univ.image constChoice
  have htermZero : ∀ js : Fin 3 → Fin k,
      js ∉ diagonalChoices →
      PiTensorProduct.map (fun i ↦ slotMap i (js i)) S.t = 0 := by
    intro js hjs
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    have hnonconstant : ∀ j : Fin k, js ≠ fun _ ↦ j := by
      intro j heq
      apply hjs
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, heq.symm⟩
    rw [hMixedZero js hnonconstant]
    exact LinearMap.map_zero _
  have hsplit :
      (∑ js : Fin 3 → Fin k,
          PiTensorProduct.map (fun i ↦ slotMap i (js i)) S.t) =
        ∑ js ∈ diagonalChoices,
          PiTensorProduct.map (fun i ↦ slotMap i (js i)) S.t := by
    symm
    apply Finset.sum_subset
    · exact Finset.subset_univ _
    · intro js _ hjs
      exact htermZero js hjs
  rw [hsplit]
  have hconstInjective : Function.Injective constChoice := by
    intro j₁ j₂ h
    exact congrFun h 0
  refine (Finset.sum_bij
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) ↦ constChoice j)
    (fun j _ ↦ Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    ?_ ?_ ?_).symm
  · intro j₁ _ j₂ _ h
    exact hconstInjective h
  · intro js hjs
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hjs
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro j _
    dsimp only [constChoice, slotMap]
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    rw [hDiagonal]
