-- Prove2me | solution 1 for mme_direct_sum_component_assembly_iff_mixed_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:38:50.319986+00:00
-- url     : https://prove2.me/submissions/0f1de433-102a-4532-8fec-d26e85191477

import Definitions.Def_mme_induced_word_zeroing
import Mathlib.LinearAlgebra.PiTensorProduct

open MME PiTensorProduct BigOperators
universe u
set_option autoImplicit false

namespace MME.DirectSumAssembly
variable {K : Type u} [Field K]

/-- Projection to one summand of the recursively represented direct sum. -/
noncomputable def slotProj :
    (k : ℕ) → (B : Fin k → TensorObj K 3) → (j : Fin k) →
      (i : Fin 3) → (TensorObj.bigAdd B).V i →ₗ[K] (B j).V i
  | 0, _, j, _ => j.elim0
  | 1, B, j, i =>
      Fin.cases (motive := fun j => (B 0).V i →ₗ[K] (B j).V i)
        LinearMap.id (fun j' => j'.elim0) j
  | n + 2, B, j, i =>
      Fin.cases (motive := fun j =>
          (TensorObj.add (B 0) (TensorObj.bigAdd (fun k => B k.succ))).V i →ₗ[K]
            (B j).V i)
        (LinearMap.fst K ((B 0).V i) ((TensorObj.bigAdd (fun k => B k.succ)).V i))
        (fun j' => (slotProj (n + 1) (fun k => B k.succ) j' i).comp
          (LinearMap.snd K ((B 0).V i) ((TensorObj.bigAdd (fun k => B k.succ)).V i))) j

private theorem slotProj_slot_self :
    ∀ (k : ℕ) (B : Fin k → TensorObj K 3) (j : Fin k) (i : Fin 3),
      (slotProj k B j i).comp (gradedBigAddSlot k B j i) = LinearMap.id
  | 0, _, j, _ => j.elim0
  | 1, B, j, i => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
  | n + 2, B, j, i => by
      refine Fin.cases ?_ (fun j' => ?_) j
      · rfl
      · simp only [slotProj, gradedBigAddSlot, Fin.cases_succ]
        ext x
        change slotProj (n + 1) (fun k => B k.succ) j' i
          (gradedBigAddSlot (n + 1) (fun k => B k.succ) j' i x) = x
        exact LinearMap.congr_fun (slotProj_slot_self (n + 1) (fun k => B k.succ) j' i) x

private theorem slotProj_slot_ne :
    ∀ (k : ℕ) (B : Fin k → TensorObj K 3) (j l : Fin k) (i : Fin 3),
      j ≠ l → (slotProj k B j i).comp (gradedBigAddSlot k B l i) = 0
  | 0, _, j, _, _, _ => j.elim0
  | 1, _, j, l, _, h => (h (Subsingleton.elim _ _)).elim
  | n + 2, B, j, l, i, h => by
      revert h
      refine Fin.cases ?_ (fun j' => ?_) j <;>
        refine Fin.cases ?_ (fun l' => ?_) l
      · intro h
        exact (h rfl).elim
      · intro _
        ext x
        rfl
      · intro _
        ext x
        change slotProj (n + 1) (fun k => B k.succ) j' i 0 = 0
        exact map_zero _
      · intro h
        ext x
        change slotProj (n + 1) (fun k => B k.succ) j' i
          (gradedBigAddSlot (n + 1) (fun k => B k.succ) l' i x) = 0
        exact LinearMap.congr_fun
          (slotProj_slot_ne (n + 1) (fun k => B k.succ) j' l' i (fun he => h (congrArg Fin.succ he))) x

/-- A summand projection recovers its component map from the assembled map. -/
theorem slotProj_sum_slots {k : ℕ} (T : TensorObj K 3)
    (B : Fin k → TensorObj K 3) (f : ∀ j i, T.V i →ₗ[K] (B j).V i)
    (j : Fin k) (i : Fin 3) :
    (slotProj k B j i).comp
      (∑ l, (gradedBigAddSlot k B l i).comp (f l i)) = f j i := by
  classical
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single j]
  · exact LinearMap.congr_fun (slotProj_slot_self k B j i) (f j i x)
  · intro l _ hlj
    exact LinearMap.congr_fun (slotProj_slot_ne k B j l i (Ne.symm hlj)) (f l i x)
  · simp

/-- Tensoring a finite sum of maps in every mode expands as the sum over all
choices of one summand per mode. -/
theorem map_sum_modes
    {k : ℕ} {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, Fin k → V i →ₗ[K] W i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => ∑ j, f i j) x =
      ∑ js : Fin 3 → Fin k,
        PiTensorProduct.map (fun i => f i (js i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul]
      simp only [PiTensorProduct.map_tprod, LinearMap.coe_sum,
        Finset.sum_apply]
      rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _]
      rw [Finset.smul_sum]
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, Finset.sum_add_distrib]

/-- The tensor of a finite direct sum is the sum of the tensors inserted in
their respective slots. -/
theorem bigAdd_t_eq_sum_slot :
    ∀ (k : ℕ) (B : Fin k → TensorObj K 3),
      (TensorObj.bigAdd B).t =
        ∑ j : Fin k,
          PiTensorProduct.map (fun i => gradedBigAddSlot k B j i) (B j).t
  | 0, _ => by
      change (TensorObj.zeroObj : TensorObj K 3).t = ∑ j : Fin 0, _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rfl
  | 1, B => by
      change (B 0).t =
        ∑ j : Fin 1,
          PiTensorProduct.map (fun i => gradedBigAddSlot 1 B j i) (B j).t
      rw [Fin.sum_univ_one]
      change (B 0).t = PiTensorProduct.map (fun _ => LinearMap.id) (B 0).t
      rw [PiTensorProduct.map_id]
      rfl
  | n + 2, B => by
      change PiTensorProduct.map (fun i =>
              LinearMap.inl K ((B 0).V i)
                ((TensorObj.bigAdd (fun j => B j.succ)).V i)) (B 0).t +
          PiTensorProduct.map (fun i =>
              LinearMap.inr K ((B 0).V i)
                ((TensorObj.bigAdd (fun j => B j.succ)).V i))
            (TensorObj.bigAdd (fun j => B j.succ)).t =
        ∑ j : Fin (n + 2),
          PiTensorProduct.map (fun i => gradedBigAddSlot (n + 2) B j i) (B j).t
      rw [Fin.sum_univ_succ]
      rw [bigAdd_t_eq_sum_slot (n + 1) (fun j => B j.succ)]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl

/-- Component maps with vanishing mixed terms assemble into a direct-sum restriction. -/
private theorem blocks_map
    {k : ℕ} (T : TensorObj K 3) (B : Fin k → TensorObj K 3)
    (proj : ∀ j i, T.V i →ₗ[K] (B j).V i)
    (hdiag : ∀ j, PiTensorProduct.map (proj j) T.t = (B j).t)
    (hzero : ∀ js : Fin 3 → Fin k, (¬ ∃ j, js = fun _ => j) →
      PiTensorProduct.map (fun i => proj (js i) i) T.t = 0) :
    PiTensorProduct.map (fun i ↦ ∑ j : Fin k,
      (gradedBigAddSlot k B j i).comp (proj j i)) T.t =
      (TensorObj.bigAdd B).t := by
  classical
  rw [bigAdd_t_eq_sum_slot]
  rw [map_sum_modes]
  let constChoice : Fin k → Fin 3 → Fin k := fun j _ => j
  let diagonalChoices : Finset (Fin 3 → Fin k) :=
    Finset.univ.image constChoice
  have hterm_zero : ∀ js : Fin 3 → Fin k,
      js ∉ diagonalChoices →
      PiTensorProduct.map
          (fun i => (gradedBigAddSlot k B (js i) i).comp
            (proj (js i) i))
          T.t = 0 := by
    intro js hjs
    have hnotconst : ¬ ∃ j : Fin k, js = constChoice j := by
      intro h
      obtain ⟨j, hj⟩ := h
      apply hjs
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    rw [hzero js hnotconst]
    exact LinearMap.map_zero _
  have hsplit :
      (∑ js : Fin 3 → Fin k,
        PiTensorProduct.map
          (fun i => (gradedBigAddSlot k B (js i) i).comp
            (proj (js i) i))
          T.t) =
      ∑ js ∈ diagonalChoices,
        PiTensorProduct.map
          (fun i => (gradedBigAddSlot k B (js i) i).comp
            (proj (js i) i))
          T.t := by
    symm
    apply Finset.sum_subset
    · intro js _
      exact Finset.mem_univ js
    · intro js _ hjs
      exact hterm_zero js hjs
  rw [hsplit]
  have hconst_injective : Function.Injective constChoice := by
    intro j₁ j₂ h
    exact congrFun h 0
  have hdiag : ∀ j : Fin k,
      PiTensorProduct.map
          (fun i => (gradedBigAddSlot k B ((constChoice j) i) i).comp
            (proj ((constChoice j) i) i))
          T.t =
        PiTensorProduct.map (fun i => gradedBigAddSlot k B j i) (B j).t := by
    intro j
    dsimp only [constChoice]
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    rw [hdiag j]
  refine (Finset.sum_bij
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => constChoice j)
    (fun j _ => Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    ?_ ?_ ?_).symm
  · intro j₁ _ j₂ _ h
    exact hconst_injective h
  · intro js hjs
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hjs
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro j _
    exact (hdiag j).symm


private theorem map_zero_of_zero_mode
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin 3) (hi : f i = 0)
    (x : PiTensorProduct K V) : PiTensorProduct.map f x = 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      rw [map_smul, PiTensorProduct.map_tprod,
        (PiTensorProduct.tprod K).map_coord_zero i (by rw [hi]; rfl), smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- Distinct summand choices in the three modes annihilate a direct-sum tensor. -/
theorem mixed_slotProj_bigAdd_eq_zero {k : ℕ}
    (B : Fin k → TensorObj K 3) (js : Fin 3 → Fin k)
    (hnot : ¬ ∃ j, js = fun _ => j) :
    PiTensorProduct.map (fun i => slotProj k B (js i) i)
      (TensorObj.bigAdd B).t = 0 := by
  classical
  rw [bigAdd_t_eq_sum_slot, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hne : ∃ i, js i ≠ j := by
    by_contra hn
    push_neg at hn
    exact hnot ⟨j, funext hn⟩
  obtain ⟨i, hi⟩ := hne
  exact map_zero_of_zero_mode _ i (slotProj_slot_ne k B (js i) j i hi) _

end MME.DirectSumAssembly

open MME.DirectSumAssembly

/-- The sum of component maps realizes their direct-sum tensor exactly when
all nonconstant mixed choices vanish. The diagonal images are prescribed. -/
theorem solution
    {K : Type u} [Field K] {k : ℕ}
    (T : TensorObj K 3) (B : Fin k → TensorObj K 3)
    (proj : ∀ j i, T.V i →ₗ[K] (B j).V i)
    (hdiag : ∀ j, PiTensorProduct.map (proj j) T.t = (B j).t) :
    PiTensorProduct.map (fun i => ∑ j,
      (gradedBigAddSlot k B j i).comp (proj j i)) T.t = (TensorObj.bigAdd B).t ↔
      ∀ js : Fin 3 → Fin k, (¬ ∃ j, js = fun _ => j) →
        PiTensorProduct.map (fun i => proj (js i) i) T.t = 0 := by
  constructor
  · intro heq js hnot
    have h := congrArg
      (PiTensorProduct.map (fun i => slotProj k B (js i) i)) heq
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp] at h
    simp only [slotProj_sum_slots] at h
    exact h.trans (mixed_slotProj_bigAdd_eq_zero B js hnot)
  · exact blocks_map T B proj hdiag

#print axioms solution
