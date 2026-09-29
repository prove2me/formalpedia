-- Prove2me | solution 2 for mme_CW_q6_paired_cyclic_coloring_matrix_direct_sum_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T00:46:54.797577+00:00
-- url     : https://prove2.me/submissions/c6476b0a-df3e-4677-9bfa-9f57818a05b9

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import Theorems.Thm_mme_CW_q6_common_halving_paired_oriented_component_certificate
import Theorems.Thm_mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Mathlib.LinearAlgebra.PiTensorProduct

open MME MME.PairedOrientedPackaging PiTensorProduct BigOperators
universe u
set_option autoImplicit false

namespace MME.PairedColorMatrixExtraction
variable {K : Type u} [Field K]

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
          simp only [map_add, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/-- Projecting a tensor power along an address gives exactly the ordered
Kronecker product of its coordinate blocks. -/
theorem map_gradedAddressProj
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
private theorem blocks_restrict
    {k : ℕ} (T : TensorObj K 3) (B : Fin k → TensorObj K 3)
    (proj : ∀ j i, T.V i →ₗ[K] (B j).V i)
    (hdiag : ∀ j, PiTensorProduct.map (proj j) T.t = (B j).t)
    (hzero : ∀ js : Fin 3 → Fin k, (¬ ∃ j, js = fun _ => j) →
      PiTensorProduct.map (fun i => proj (js i) i) T.t = 0) :
    TensorObj.Restrict (TensorObj.bigAdd B) T := by
  classical
  refine ⟨fun i =>
    ∑ j : Fin k,
      (gradedBigAddSlot k B j i).comp (proj j i), ?_⟩
  rw [bigAdd_t_eq_sum_slot]
  rw [map_sum_modes]
  change
    (∑ js : Fin 3 → Fin k,
      PiTensorProduct.map
        (fun i => (gradedBigAddSlot k B (js i) i).comp
          (proj (js i) i))
        T.t) =
      ∑ j : Fin k,
        PiTensorProduct.map (fun i => gradedBigAddSlot k B j i) (B j).t
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

end MME.PairedColorMatrixExtraction

namespace MME.PairedColorMatrixExtraction

private theorem bigAdd_respects_iso {K : Type u} [Field K] :
    ∀ (k : ℕ) (B C : Fin k → TensorObj K 3),
      (∀ j, TensorObj.Isomorphic (B j) (C j)) →
      TensorObj.Isomorphic (TensorObj.bigAdd B) (TensorObj.bigAdd C)
  | 0, _, _, _ => TensorObj.Isomorphic.refl _
  | 1, _, _, h => h 0
  | k + 2, B, C, h =>
      TensorQ.add_respects_iso (h 0)
        (bigAdd_respects_iso (k + 1) (fun j => B j.succ) (fun j => C j.succ)
          (fun j => h j.succ))

end MME.PairedColorMatrixExtraction

/-- One color class extracts matrix blocks without imposing uniform outer fibers. -/
theorem solution
    {K : Type u} [Field K] {N L G A H k : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (hk : 0 < k)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      A * H ≤ k * q ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow N)
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)) ∧
      ∀ j, a j * b j * c j = 6 ^ (4 * G + 2 * L) := by
  classical
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  obtain ⟨color, hcolor⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card
    (f := fun p : Fin A × Fin H => coloring p) (b := (A * H : ℚ) / k)
    (by simp [nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hkq)])
  let Fiber := {p : Fin A × Fin H // coloring p = color}
  let q := Fintype.card Fiber
  let index (j : Fin q) : Fin A × Fin H := ((Fintype.equivFin Fiber).symm j).val
  have hinj : Function.Injective index :=
    Subtype.val_injective.comp (Fintype.equivFin Fiber).symm.injective
  have hmonochrome (j : Fin q) : coloring (index j) = color :=
    ((Fintype.equivFin Fiber).symm j).property
  have hpaired (p0 p1 p2 : Fin q)
      (hs : family.PairedCyclicSupported halving (index p0) (index p1) (index p2)) :
      p0 = p1 ∧ p1 = p2 := by
    have eq_of_mem (p q : Fin A × Fin H)
        (hp : family.InPairedTriple p (index p0) (index p1) (index p2))
        (hq : family.InPairedTriple q (index p0) (index p1) (index p2))
        (heq : coloring p = coloring q) : p = q := by
      by_contra hne
      have hbad : ¬ (index p0 = index p1 ∧ index p1 = index p2) := by
        rintro ⟨h01, h12⟩
        rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
          exact hne (by simp [hp, hq, h01, h12])
      exact coloring.valid
        ⟨hne, Or.inl ⟨index p0, index p1, index p2, hs, hbad, hp, hq⟩⟩ heq
    exact ⟨hinj (eq_of_mem _ _ (Or.inl rfl) (Or.inr (Or.inl rfl))
      ((hmonochrome p0).trans (hmonochrome p1).symm)),
      hinj (eq_of_mem _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
        ((hmonochrome p1).trans (hmonochrome p2).symm))⟩
  have hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin q => componentObj (K := K) family halving (index j)))
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)) := by
    apply MME.PairedColorMatrixExtraction.blocks_restrict _ _
      (fun j i => componentProj family halving (index j) i)
    · intro j
      change PiTensorProduct.map
          (fun i => TensorProduct.map
            (gradedAddressProj (leftGrading (K := K)) N
              (leftAddress family halving (index j)) i)
            (gradedAddressProj (rightGrading (K := K)) N
              (rightAddress family halving (index j)) i))
          (interchange _ _) = interchange _ _
      rw [MME.PairedColorMatrixExtraction.map_interchange,
        MME.PairedColorMatrixExtraction.map_gradedAddressProj,
        MME.PairedColorMatrixExtraction.map_gradedAddressProj]
    · intro js hnot
      apply mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
      intro hs
      have heq := hpaired _ _ _ hs
      apply hnot
      refine ⟨js 0, funext fun i => ?_⟩
      fin_cases i <;> simp_all
  refine ⟨q, fun j => componentM family halving (index j),
    fun j => componentN family halving (index j),
    fun j => componentP family halving (index j), ?_, ?_, ?_⟩
  · have hb := (div_le_iff₀ hkq).mp hcolor
    have hn : A * H ≤ k *
        (Finset.univ.filter (fun p : Fin A × Fin H => coloring p = color)).card := by
      exact_mod_cast (show (A * H : ℚ) ≤ k *
        ((Finset.univ.filter (fun p : Fin A × Fin H => coloring p = color)).card : ℚ)
        by nlinarith)
    simpa [q, Fiber, Fintype.card_subtype] using hn
  · exact TensorObj.Restrict.trans
      (MME.PairedColorMatrixExtraction.bigAdd_respects_iso q _ _
        (fun j => (mme_CW_q6_common_halving_paired_oriented_component_certificate
          (K := K) family halving (index j)).1)).1 hrestrict
  · intro j
    exact (mme_CW_q6_common_halving_paired_oriented_component_certificate
      (K := K) family halving (index j)).2
