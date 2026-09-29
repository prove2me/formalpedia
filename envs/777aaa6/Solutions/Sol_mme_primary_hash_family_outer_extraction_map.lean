-- Prove2me | solution 1 for mme_primary_hash_family_outer_extraction_map
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:46:01.035736+00:00
-- url     : https://prove2.me/submissions/3c13ed60-a671-4810-b292-0438326d9c8b

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Mathlib.LinearAlgebra.PiTensorProduct

open MME PiTensorProduct BigOperators CoupledCTensorPackaging
universe u
set_option autoImplicit false

variable {K : Type u} [Field K]

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

private theorem map_interchange
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
          simp only [map_add, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/-- Projecting a tensor power along an address gives exactly the ordered
Kronecker product of its coordinate blocks. -/
private theorem map_gradedAddressProj
    {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (a : Fin 3 → Fin N → Fin t) :
    PiTensorProduct.map (gradedAddressProj G N a) (T.kronPow N).t =
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
            (gradedAddressProj G N (fun i j => a i j.succ) i))
          (interchange T.t (T.kronPow N).t) =
        interchange
          (G.blockTensor (fun i => a i 0))
          (gradedAddressBlock G (fun i j => a i j.succ)).t
      rw [map_interchange]
      unfold TensorObj.TypeGrading.blockTensor
      rw [ih]


private theorem mixed_projection_eq_zero_of_coord
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (A : Fin k → Fin 3 → Fin N → Fin t)
    (js : Fin 3 → Fin k) (r : Fin N)
    (hr : G.blockTensor (fun i => A (js i) i r) = 0) :
    PiTensorProduct.map
        (fun i => gradedAddressProj G N (A (js i)) i)
        (T.kronPow N).t = 0 := by
  induction N with
  | zero => exact Fin.elim0 r
  | succ N ih =>
      refine Fin.cases
        (motive := fun r =>
          G.blockTensor (fun i => A (js i) i r) = 0 →
          PiTensorProduct.map
              (fun i => gradedAddressProj G (N + 1) (A (js i)) i)
              (T.kronPow (N + 1)).t = 0)
        ?_ (fun r' => ?_) r hr
      · intro hr0
        simp only [MME.gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (G.blockProj i (A (js i) i 0))
              (gradedAddressProj G N
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
              (gradedAddressProj G N
                (fun i' r => A (js i) i' r.succ) i))
            (interchange T.t (T.kronPow N).t) = 0
        rw [map_interchange]
        have htail := ih (fun j i r => A j i r.succ) r' hr'
        rw [htail]
        exact LinearMap.map_zero _

private theorem map_sum_modes
    {J : Fin 3 → Type} [∀ i, Fintype (J i)] {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, J i → V i →ₗ[K] W i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => ∑ j, f i j) x =
      ∑ js : ∀ i, J i,
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
private theorem bigAdd_t_eq_sum_slot :
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

private theorem modeEquiv_comp_proj {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (n : ℕ)
    (a a' : Fin 3 → Fin n → Fin t) (i : Fin 3) (hi : a i = a' i) :
    (gradedAddressBlockModeEquiv G n a a' i hi).toLinearMap.comp
        (gradedAddressProj G n a i) = gradedAddressProj G n a' i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let tail := fun (j : Fin 3) (r : Fin n) => a j r.succ
    let tail' := fun (j : Fin 3) (r : Fin n) => a' j r.succ
    have ht : tail i = tail' i := by funext r; exact congrFun hi r.succ
    change (TensorProduct.congr
      (LinearEquiv.ofEq (G.classOf i (a i 0)) (G.classOf i (a' i 0))
        (by rw [congrFun hi 0]))
      (gradedAddressBlockModeEquiv G n tail tail' i ht)).toLinearMap.comp
        (TensorProduct.map (G.blockProj i (a i 0)) (gradedAddressProj G n tail i)) =
      TensorProduct.map (G.blockProj i (a' i 0)) (gradedAddressProj G n tail' i)
    apply TensorProduct.ext
    ext x y
    change (LinearEquiv.ofEq (G.classOf i (a i 0)) (G.classOf i (a' i 0))
        (by rw [congrFun hi 0])) (G.blockProj i (a i 0) x) ⊗ₜ[K]
      (gradedAddressBlockModeEquiv G n tail tail' i ht) (gradedAddressProj G n tail i y) =
        G.blockProj i (a' i 0) x ⊗ₜ[K] gradedAddressProj G n tail' i y
    have hhead (j j' : Fin t) (h : j = j') :
        (LinearEquiv.ofEq (G.classOf i j) (G.classOf i j') (congrArg _ h))
          (G.blockProj i j x) = G.blockProj i j' x := by
      subst j'
      rfl
    rw [hhead (a i 0) (a' i 0) (congrFun hi 0)]
    congr 1
    exact LinearMap.congr_fun (ih tail tail' ht) y

private theorem outer_supported_diagonal {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i, outerChoiceType (A := A) (H := H) i)
    (hs : CWQ6CoupledCoordinatewiseSupported (outerMixedAddress family js)) :
    ∃ p : Fin A × Fin H, js = outerDiagonalChoice p.1 p.2 := by
  have he : outerMixedAddress family js = cwQ6CoupledMixedAddress
      (family.entry (js 0)).val (family.entry (js 1)).val
      (family.entry (js 2, firstFiberIndex family)).val := by
    funext i r
    fin_cases i <;>
      simp [outerMixedAddress, outerChosenAddress, componentAddress_eq_entry,
        cwQ6CoupledMixedAddress]
  rw [he] at hs
  obtain ⟨hxy, hxz⟩ := family.induced (js 0) (js 1)
    (js 2, firstFiberIndex family) hs
  refine ⟨js 0, ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact hxy.symm
  · exact hxz.symm

private theorem outer_nondiagonal_zero {T : TensorObj K 3}
    (grading : T.TypeGrading 3) {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] → grading.blockTensor σ = 0)
    (js : ∀ i, outerChoiceType (A := A) (H := H) i)
    (hjs : ¬ ∃ p : Fin A × Fin H, js = outerDiagonalChoice p.1 p.2) :
    PiTensorProduct.map (fun i => outerExtractionSummand grading family i (js i))
      (T.kronPow (2 * N)).t = 0 := by
  classical
  have hbad : ∃ r, grading.blockTensor (fun i => outerMixedAddress family js i r) = 0 := by
    by_contra h
    apply hjs
    apply outer_supported_diagonal family js
    intro r
    have hn : grading.blockTensor (fun i => outerMixedAddress family js i r) ≠ 0 :=
      fun hr => h ⟨r, hr⟩
    have hs : (fun i => outerMixedAddress family js i r) = ![0, 0, 0] ∨
        (fun i => outerMixedAddress family js i r) = ![1, 1, 1] ∨
        (fun i => outerMixedAddress family js i r) = ![0, 1, 2] ∨
        (fun i => outerMixedAddress family js i r) = ![1, 0, 2] := by
      by_contra hs
      push_neg at hs
      exact hn (hSupport _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)
    rcases hs with hs | hs | hs | hs
    · exact Or.inl ⟨congrFun hs 0, congrFun hs 1, congrFun hs 2⟩
    · exact Or.inr (Or.inl ⟨congrFun hs 0, congrFun hs 1, congrFun hs 2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨congrFun hs 0, congrFun hs 1, congrFun hs 2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨congrFun hs 0, congrFun hs 1, congrFun hs 2⟩))
  obtain ⟨r, hr⟩ := hbad
  have hz := mixed_projection_eq_zero_of_coord grading (outerChosenAddress family js)
    (fun i => i) r hr
  have hf : (fun i => outerExtractionSummand grading family i (js i)) =
      fun i => (outerTargetInclusion grading family js i).comp
        (gradedAddressProj grading (2 * N) (outerChosenAddress family js i) i) := by
    funext i
    fin_cases i <;> rfl
  rw [hf, PiTensorProduct.map_comp, LinearMap.comp_apply, hz, map_zero]

private theorem outer_diagonal_term {T : TensorObj K 3}
    (grading : T.TypeGrading 3) {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H) (a : Fin A) (h : Fin H) :
    PiTensorProduct.map
        (fun i => outerExtractionSummand grading family i (outerDiagonalChoice a h i))
        (T.kronPow (2 * N)).t =
      PiTensorProduct.map (fun i => gradedBigAddSlot A (starObj grading family) a i)
        (PiTensorProduct.map (componentInclusion grading family a h)
          (componentObj grading family a h).t) := by
  have hf : (fun i => outerExtractionSummand grading family i (outerDiagonalChoice a h i)) =
      fun i => (gradedBigAddSlot A (starObj grading family) a i).comp
        ((componentInclusion grading family a h i).comp
          (gradedAddressProj grading (2 * N) (componentAddress family a h) i)) := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · apply LinearMap.ext
      intro x
      change gradedBigAddSlot A (starObj grading family) a 2
        (gradedAddressProj grading (2 * N)
          (componentAddress family a (firstFiberIndex family)) 2 x) =
        gradedBigAddSlot A (starObj grading family) a 2
          (componentZEquiv grading family a h
            (gradedAddressProj grading (2 * N) (componentAddress family a h) 2 x))
      congr 1
      exact (LinearMap.congr_fun (modeEquiv_comp_proj grading (2 * N)
        (componentAddress family a h)
        (componentAddress family a (firstFiberIndex family)) 2 rfl) x).symm
  rw [hf, PiTensorProduct.map_comp, LinearMap.comp_apply]
  congr 1
  erw [PiTensorProduct.map_comp, LinearMap.comp_apply, map_gradedAddressProj]
  rfl

/-- The primary family's explicit outer extraction maps produce precisely the
sum of its shared-Z stars from the full graded tensor power. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3}
    (grading : T.TypeGrading 3) {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] → grading.blockTensor σ = 0) :
    PiTensorProduct.map (outerExtractionMap grading family) (T.kronPow (2 * N)).t =
      (TensorObj.bigAdd (starObj grading family)).t := by
  classical
  let term := fun js : ∀ i, outerChoiceType (A := A) (H := H) i =>
    PiTensorProduct.map (fun i => outerExtractionSummand grading family i (js i))
      (T.kronPow (2 * N)).t
  let diag : Fin A × Fin H → ∀ i, outerChoiceType (A := A) (H := H) i :=
    fun p => outerDiagonalChoice p.1 p.2
  let D := Finset.univ.image diag
  have hdiag : Function.Injective diag := by
    intro p q hpq
    exact congrFun hpq 0
  have hsum : (∑ js, term js) = ∑ p, term (diag p) := by
    calc
      (∑ js, term js) = ∑ js ∈ D, term js := by
        symm
        apply Finset.sum_subset (Finset.subset_univ D)
        intro js _ hjs
        apply outer_nondiagonal_zero grading family hSupport js
        rintro ⟨p, hp⟩
        apply hjs
        exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp.symm⟩
      _ = ∑ p, term (diag p) := Finset.sum_image (fun p _ q _ hpq => hdiag hpq)
  change PiTensorProduct.map (fun i => ∑ j, outerExtractionSummand grading family i j)
      (T.kronPow (2 * N)).t = _
  rw [map_sum_modes]
  change (∑ js, term js) = _
  rw [hsum, bigAdd_t_eq_sum_slot]
  have hstar (a : Fin A) : (starObj grading family a).t =
      ∑ h, PiTensorProduct.map (componentInclusion grading family a h)
        (componentObj grading family a h).t := rfl
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [hstar]
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro h _
  exact outer_diagonal_term grading family a h

#print axioms solution
