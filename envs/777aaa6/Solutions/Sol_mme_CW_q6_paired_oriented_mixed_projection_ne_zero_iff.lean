-- Prove2me | solution 1 for mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T00:31:22.838812+00:00
-- url     : https://prove2.me/submissions/a964b979-a8b6-41c6-899a-bba0e8c289ee

import Theorems.Thm_mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_isomorphisms
import Definitions.Def_mme_tensor_bridge
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
Exact support of the literal paired oriented component projections.
A product-basis coefficient proves that a Kronecker product of nonzero tensors
is nonzero. The four allowed coupled blocks are nonzero matrix tensors; this
property propagates through each half-word and then through their product.
Together with the previously proved vanishing direction, this gives an exact
support criterion over every field.
-/

open MME PiTensorProduct Module BigOperators

universe u

set_option autoImplicit false

namespace MME.PairedProjectionExactSupport

variable {K : Type u} [Field K]

private theorem interchange_tprod
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  change PiTensorProduct.lift (interchangeInner v) (tprod K w) = _
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

/-- A product-basis coefficient of the Kronecker tensor is the product of
the corresponding coefficients of its two factors. -/
private theorem interchange_repr
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {ι κ : Fin 3 → Type u}
    (b : ∀ i, Basis (ι i) K (V i)) (c : ∀ i, Basis (κ i) K (W i))
    (x : PiTensorProduct K V) (y : PiTensorProduct K W)
    (p : ∀ i, ι i) (q : ∀ i, κ i) :
    (Basis.piTensorProduct (fun i => (b i).tensorProduct (c i))).repr
        (interchange x y) (fun i => (p i, q i)) =
      (Basis.piTensorProduct b).repr x p * (Basis.piTensorProduct c).repr y q := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod a' w =>
          simp only [map_smul, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
          rw [interchange_tprod]
          simp only [Basis.piTensorProduct_repr_tprod_apply,
            Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, Finset.prod_mul_distrib]
          ring
      | add y z hy hz =>
          simp only [map_add, Finsupp.add_apply, hy, hz, mul_add]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hz, add_mul]

theorem interchange_ne_zero
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {x : PiTensorProduct K V} {y : PiTensorProduct K W}
    (hx : x ≠ 0) (hy : y ≠ 0) : interchange x y ≠ 0 := by
  classical
  let b := fun i => Module.Free.chooseBasis K (V i)
  let c := fun i => Module.Free.chooseBasis K (W i)
  have hbx : (Basis.piTensorProduct b).repr x ≠ 0 := by
    intro h
    exact hx ((Basis.piTensorProduct b).repr.injective (by simpa using h))
  have hcy : (Basis.piTensorProduct c).repr y ≠ 0 := by
    intro h
    exact hy ((Basis.piTensorProduct c).repr.injective (by simpa using h))
  obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp hbx
  obtain ⟨q, hq⟩ := Finsupp.ne_iff.mp hcy
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hp hq
  intro hzero
  have h := interchange_repr b c x y p q
  rw [hzero, map_zero, Finsupp.zero_apply] at h
  exact mul_ne_zero hp hq h.symm

private theorem mm_one_ne_zero : (MMObj K 1 1 1).t ≠ 0 := by
  let f : ∀ i : Fin 3, (MMObj K 1 1 1).V i →ₗ[K] K
    | 0 => LinearMap.proj (0, 0)
    | 1 => LinearMap.proj (0, 0)
    | 2 => LinearMap.proj (0, 0)
  have heval :
      constantBaseRingEquiv (Fin 3) K
        (PiTensorProduct.map f (MMObj K 1 1 1).t) = 1 := by
    rw [MMObj_t, Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
    unfold MMPure
    erw [PiTensorProduct.map_tprod]
    rw [constantBaseRingEquiv_tprod]
    apply Finset.prod_eq_one
    intro i _
    fin_cases i <;>
      change (Pi.single (0, 0) (1 : K) : (Fin 1 × Fin 1) → K) (0, 0) = 1
    all_goals exact Pi.single_eq_same (0, 0) 1
  intro h
  rw [h, map_zero, map_zero] at heval
  exact zero_ne_one heval

private theorem ne_zero_of_restrict {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) (hx : X.t ≠ 0) : Y.t ≠ 0 := by
  obtain ⟨f, hf⟩ := h
  intro hy
  rw [hy, map_zero] at hf
  exact hx hf.symm

private theorem mm_ne_zero {m n p : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hp : 1 ≤ p) : (MMObj K m n p).t ≠ 0 :=
  ne_zero_of_restrict (MMObj_restrict_of_le hm hn hp) mm_one_ne_zero

private theorem coupled_block_ne_zero
    (σ : Fin 3 → Fin 3)
    (h : CWQ6CoupledLocalSupported (σ 0) (σ 1) (σ 2)) :
    (DWZComponentRestriction.dwzQ6CoupledGrading K).blockTensor σ ≠ 0 := by
  have htypes : σ = ![0, 0, 0] ∨ σ = ![1, 1, 1] ∨
      σ = ![0, 1, 2] ∨ σ = ![1, 0, 2] := by
    rcases h with h | h | h | h
    · left; funext i; fin_cases i <;> simp_all
    · right; left; funext i; fin_cases i <;> simp_all
    · right; right; left; funext i; fin_cases i <;> simp_all
    · right; right; right; funext i; fin_cases i <;> simp_all
  obtain ⟨h000, h111, h012, h102⟩ :=
    mme_dwz_q6_explicit_coupled_four_block_isomorphisms (K := K)
  rcases htypes with rfl | rfl | rfl | rfl
  · have ht := ne_zero_of_restrict h000.1 (mm_ne_zero (by decide) (by decide) (by decide))
    exact ht
  · have ht := ne_zero_of_restrict h111.1 (mm_ne_zero (by decide) (by decide) (by decide))
    exact ht
  · have ht := ne_zero_of_restrict h012.1 (mm_ne_zero (by decide) (by decide) (by decide))
    exact ht
  · have ht := ne_zero_of_restrict h102.1 (mm_ne_zero (by decide) (by decide) (by decide))
    exact ht

private theorem permuted_block_ne_zero
    (e : Equiv.Perm (Fin 3)) (σ : Fin 3 → Fin 3)
    (h : CWQ6CoupledLocalSupported (σ (e 0)) (σ (e 1)) (σ (e 2))) :
    (TensorObj.TypeGrading.permObjGrading
      (DWZComponentRestriction.dwzQ6CoupledGrading K) e).blockTensor σ ≠ 0 := by
  let ρ : Fin 3 → Fin 3 := fun i => σ (e i)
  have hσ : σ = fun i => ρ (e.symm i) := by
    funext i
    simp [ρ]
  have hn := coupled_block_ne_zero (K := K) ρ h
  rw [hσ, TensorObj.TypeGrading.permObjGrading_blockTensor]
  exact (PiTensorProduct.reindex K
    (fun i => (DWZComponentRestriction.dwzQ6CoupledGrading K).classOf i (ρ i))
    e).map_ne_zero_iff.mpr hn

/-- Coordinatewise nonvanishing propagates through a mixed word projection.
No compatibility between different word positions is required. -/
theorem mixed_word_projection_ne_zero
    {T : TensorObj K 3} {t N : ℕ} {ι : Type*}
    (G : T.TypeGrading t)
    (A : ι → Fin 3 → Fin N → Fin t)
    (js : Fin 3 → ι)
    (h : ∀ r, G.blockTensor (fun i => A (js i) i r) ≠ 0) :
    PiTensorProduct.map
      (fun i => gradedAddressProj G N (A (js i)) i) (T.kronPow N).t ≠ 0 := by
  induction N with
  | zero =>
      change PiTensorProduct.map (fun _ => LinearMap.id)
        (TensorObj.oneObj : TensorObj K 3).t ≠ 0
      rw [PiTensorProduct.map_id]
      intro hz
      change (TensorObj.oneObj : TensorObj K 3).t = 0 at hz
      have hone :
          constantBaseRingEquiv (Fin 3) K (TensorObj.oneObj : TensorObj K 3).t = 1 := by
        simp [TensorObj.oneObj, constantBaseRingEquiv_tprod]
      rw [hz] at hone
      exact zero_ne_one ((constantBaseRingEquiv (Fin 3) K).map_zero.symm.trans hone)
  | succ N ih =>
      change PiTensorProduct.map
        (fun i => TensorProduct.map
          (G.blockProj i (A (js i) i 0))
          (gradedAddressProj G N (fun j r => A (js i) j r.succ) i))
        (interchange T.t (T.kronPow N).t) ≠ 0
      rw [map_interchange]
      apply interchange_ne_zero
      · exact h 0
      · exact ih (fun a i r => A a i r.succ) (fun r => h r.succ)

open PairedOrientedPackaging

theorem mixed_component_projection_ne_zero
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (js : Fin 3 → Fin A × Fin H)
    (h : family.PairedCyclicSupported halving (js 0) (js 1) (js 2)) :
    PiTensorProduct.map (fun i => componentProj (K := K) family halving (js i) i)
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow N)
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t ≠ 0 := by
  change PiTensorProduct.map
    (fun i => TensorProduct.map
      (gradedAddressProj (leftGrading (K := K)) N
        (leftAddress family halving (js i)) i)
      (gradedAddressProj (rightGrading (K := K)) N
        (rightAddress family halving (js i)) i))
    (interchange _ _) ≠ 0
  rw [map_interchange]
  apply interchange_ne_zero
  · apply mixed_word_projection_ne_zero
    intro r
    apply permuted_block_ne_zero
    simpa [leftAddress, cyclicPerm] using h.1 r
  · apply mixed_word_projection_ne_zero
    intro r
    apply permuted_block_ne_zero
    simpa [rightAddress, cyclicPerm] using h.2 r

end MME.PairedProjectionExactSupport

open MME.PairedOrientedPackaging MME.PairedProjectionExactSupport

/-- Paired cyclic support describes exactly the nonzero mixed projections
of the paired oriented tensor over any field. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (js : Fin 3 → Fin A × Fin H) :
    PiTensorProduct.map (fun i => componentProj (K := K) family halving (js i) i)
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow N)
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t ≠ 0 ↔
      family.PairedCyclicSupported halving (js 0) (js 1) (js 2) := by
  constructor
  · intro hnonzero
    by_contra h
    exact hnonzero
      (mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported family halving js h)
  · exact mixed_component_projection_ne_zero family halving js
