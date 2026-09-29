-- Prove2me | solution 1 for mme_induced_graded_address_blocks_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T18:50:25.962873+00:00
-- url     : https://prove2.me/submissions/587bf2c5-23d9-4298-be60-6b43795b823d

import Mathlib.LinearAlgebra.PiTensorProduct
import Definitions.Def_mme_induced_word_zeroing

open MME PiTensorProduct BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

namespace MME

namespace InducedWordZeroing

variable {K : Type u} [Field K]

local notation "addressProj" => MME.gradedAddressProj
local notation "bigAddSlot" => MME.gradedBigAddSlot

/-- Naturality of the mode-wise interchange map. -/
private theorem interchange_tprod
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem map_interchange
    {V₁ V₂ V₃ V₄ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
        (interchange t₁ t₂) =
      interchange (PiTensorProduct.map f t₁) (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      induction t₂ using PiTensorProduct.induction_on with
      | smul_tprod c' v' =>
          simp only [map_smul, LinearMap.smul_apply]
          rw [interchange_tprod, PiTensorProduct.map_tprod,
            PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
            interchange_tprod]
          simp only [TensorProduct.map_tmul]
      | add x y ih₁ ih₂ =>
          simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/-- Projecting a tensor power along an address gives exactly the ordered
Kronecker product of its coordinate blocks. -/
theorem map_addressProj
    {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (a : Fin 3 → Fin N → Fin t) :
    PiTensorProduct.map (addressProj G N a) (T.kronPow N).t =
      (gradedAddressBlock G a).t := by
  induction N with
  | zero =>
      change PiTensorProduct.map (fun _ => LinearMap.id)
          (TensorObj.oneObj : TensorObj K 3).t =
        (TensorObj.oneObj : TensorObj K 3).t
      rw [PiTensorProduct.map_id]
      rfl
  | succ N ih =>
      change PiTensorProduct.map
          (fun i => TensorProduct.map
            (G.blockProj i (a i 0))
            (addressProj G N (fun i j => a i j.succ) i))
          (interchange T.t (T.kronPow N).t) =
        interchange
          (G.blockTensor (fun i => a i 0))
          (gradedAddressBlock G (fun i j => a i j.succ)).t
      rw [map_interchange]
      unfold TensorObj.TypeGrading.blockTensor
      rw [ih]

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
      simp only [map_smul, LinearMap.smul_apply, Finset.sum_smul]
      congr 1
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
          PiTensorProduct.map (fun i => bigAddSlot k B j i) (B j).t
  | 0, _ => by
      change (TensorObj.zeroObj : TensorObj K 3).t = ∑ j : Fin 0, _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rfl
  | 1, B => by
      change (B 0).t =
        ∑ j : Fin 1,
          PiTensorProduct.map (fun i => bigAddSlot 1 B j i) (B j).t
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
          PiTensorProduct.map (fun i => bigAddSlot (n + 2) B j i) (B j).t
      rw [Fin.sum_univ_succ]
      rw [bigAdd_t_eq_sum_slot (n + 1) (fun j => B j.succ)]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl

/-- Assemble one address by taking mode `i` from the address selected by
`js i`. -/
def mixedAddress {k t N : ℕ}
    (A : Fin k → Fin 3 → Fin N → Fin t)
    (js : Fin 3 → Fin k) : Fin 3 → Fin N → Fin t :=
  fun i r => A (js i) i r

/-- If one coordinate block is zero, the entire ordered address block is
zero. -/
theorem gradedAddressBlock_t_eq_zero_of_coord
    {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (a : Fin 3 → Fin N → Fin t)
    (r : Fin N)
    (hr : G.blockTensor (fun i => a i r) = 0) :
    (gradedAddressBlock G a).t = 0 := by
  induction N with
  | zero => exact Fin.elim0 r
  | succ N ih =>
      refine Fin.cases
        (motive := fun r =>
          G.blockTensor (fun i => a i r) = 0 →
            (gradedAddressBlock G a).t = 0)
        ?_ (fun r' => ?_) r hr
      · intro hr0
        change interchange (G.blockTensor (fun i => a i 0))
            (gradedAddressBlock G (fun i j => a i j.succ)).t = 0
        rw [hr0]
        simp only [map_zero, LinearMap.zero_apply]
      · intro hr'
        change interchange (G.blockTensor (fun i => a i 0))
            (gradedAddressBlock G (fun i j => a i j.succ)).t = 0
        have htail :
            (gradedAddressBlock G (fun i j => a i j.succ)).t = 0 :=
          ih (fun i j => a i j.succ) r' hr'
        rw [htail]
        exact LinearMap.map_zero _

/-- A mixed choice of one retained address per tensor mode projects to zero
as soon as one coordinate grading block is zero. -/
theorem mixed_projection_eq_zero_of_coord
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (A : Fin k → Fin 3 → Fin N → Fin t)
    (js : Fin 3 → Fin k) (r : Fin N)
    (hr : G.blockTensor (fun i => A (js i) i r) = 0) :
    PiTensorProduct.map
        (fun i => addressProj G N (A (js i)) i)
        (T.kronPow N).t = 0 := by
  induction N with
  | zero => exact Fin.elim0 r
  | succ N ih =>
      refine Fin.cases
        (motive := fun r =>
          G.blockTensor (fun i => A (js i) i r) = 0 →
          PiTensorProduct.map
              (fun i => addressProj G (N + 1) (A (js i)) i)
              (T.kronPow (N + 1)).t = 0)
        ?_ (fun r' => ?_) r hr
      · intro hr0
        simp only [MME.gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (G.blockProj i (A (js i) i 0))
              (addressProj G N
                (fun i' r => A (js i) i' r.succ) i))
            (interchange T.t (T.kronPow N).t) = 0
        rw [map_interchange]
        have hfirst :
            PiTensorProduct.map
                (fun i => G.blockProj i (A (js i) i 0)) T.t =
              G.blockTensor (fun i => A (js i) i 0) := rfl
        rw [hfirst, hr0]
        simp only [map_zero, LinearMap.zero_apply]
      · intro hr'
        simp only [MME.gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (G.blockProj i (A (js i) i 0))
              (addressProj G N
                (fun i' r => A (js i) i' r.succ) i))
            (interchange T.t (T.kronPow N).t) = 0
        rw [map_interchange]
        have htail := ih (fun j i r => A j i r.succ) r' hr'
        rw [htail]
        exact LinearMap.map_zero _

/-- An induced family of grading-word addresses can be extracted as a true
direct sum from the tensor power. -/
theorem induced_graded_address_blocks_restrict
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (A : Fin k → Fin 3 → Fin N → Fin t)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i => A (js i) i r) ≠ 0) →
      ∃ j : Fin k, js = fun _ => j) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j => gradedAddressBlock G (A j)))
      (T.kronPow N) := by
  classical
  let B : Fin k → TensorObj K 3 :=
    fun j => gradedAddressBlock G (A j)
  refine ⟨fun i =>
    ∑ j : Fin k,
      (bigAddSlot k B j i).comp (addressProj G N (A j) i), ?_⟩
  rw [bigAdd_t_eq_sum_slot]
  rw [map_sum_modes]
  change
    (∑ js : Fin 3 → Fin k,
      PiTensorProduct.map
        (fun i => (bigAddSlot k B (js i) i).comp
          (addressProj G N (A (js i)) i))
        (T.kronPow N).t) =
      ∑ j : Fin k,
        PiTensorProduct.map (fun i => bigAddSlot k B j i) (B j).t
  let constChoice : Fin k → Fin 3 → Fin k := fun j _ => j
  let diagonalChoices : Finset (Fin 3 → Fin k) :=
    Finset.univ.image constChoice
  have hterm_zero : ∀ js : Fin 3 → Fin k,
      js ∉ diagonalChoices →
      PiTensorProduct.map
          (fun i => (bigAddSlot k B (js i) i).comp
            (addressProj G N (A (js i)) i))
          (T.kronPow N).t = 0 := by
    intro js hjs
    have hnotconst : ¬ ∃ j : Fin k, js = constChoice j := by
      intro h
      obtain ⟨j, hj⟩ := h
      apply hjs
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩
    have hbad : ∃ r : Fin N,
        G.blockTensor (fun i => A (js i) i r) = 0 := by
      by_contra h
      have hall : ∀ r : Fin N,
          G.blockTensor (fun i => A (js i) i r) ≠ 0 := by
        intro r hr
        exact h ⟨r, hr⟩
      obtain ⟨j, hj⟩ := hInduced js hall
      exact hnotconst ⟨j, hj⟩
    obtain ⟨r, hr⟩ := hbad
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    rw [mixed_projection_eq_zero_of_coord G A js r hr]
    exact LinearMap.map_zero _
  have hsplit :
      (∑ js : Fin 3 → Fin k,
        PiTensorProduct.map
          (fun i => (bigAddSlot k B (js i) i).comp
            (addressProj G N (A (js i)) i))
          (T.kronPow N).t) =
      ∑ js ∈ diagonalChoices,
        PiTensorProduct.map
          (fun i => (bigAddSlot k B (js i) i).comp
            (addressProj G N (A (js i)) i))
          (T.kronPow N).t := by
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
          (fun i => (bigAddSlot k B ((constChoice j) i) i).comp
            (addressProj G N (A ((constChoice j) i)) i))
          (T.kronPow N).t =
        PiTensorProduct.map (fun i => bigAddSlot k B j i) (B j).t := by
    intro j
    dsimp only [constChoice]
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    rw [map_addressProj]
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

end InducedWordZeroing

end MME

open MME

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (A : Fin k → Fin 3 → Fin N → Fin t)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i => A (js i) i r) ≠ 0) →
      ∃ j : Fin k, js = fun _ => j) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j => gradedAddressBlock G (A j)))
      (T.kronPow N) := by
  exact MME.InducedWordZeroing.induced_graded_address_blocks_restrict
    G A hInduced
