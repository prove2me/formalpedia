-- Prove2me | solution 1 for mme_dwz_q6_paired_induced_restricted_matrix_direct_sum_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:35:46.006385+00:00
-- url     : https://prove2.me/submissions/02a2b097-4886-47c4-892d-ffdcf5469996

import Theorems.Thm_mme_CW_q6_common_halving_paired_oriented_component_certificate
import Theorems.Thm_mme_dwz_q6_121_common_halving_ambient_component_source_maps
import Theorems.Thm_mme_dwz_q6_211_common_halving_ambient_component_source_maps
import Theorems.Thm_mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
import Theorems.Thm_mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Mathlib.LinearAlgebra.PiTensorProduct

open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction PiTensorProduct BigOperators
universe u
set_option autoImplicit false

namespace MME.RestrictedPairedExtraction
variable {K : Type u} [Field K]

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
      rw [TensorObj.TypeGrading.kronMap_interchange]
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

end MME.RestrictedPairedExtraction
/-- A paired-induced common-halving family extracts all its components from
 either literal allowed-word component pair. -/
theorem mme_dwz_q6_paired_induced_restricted_component_direct_sum
    {K : Type u} [Field K] (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hinduced : family.PairedCyclicInduced halving) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin (A * H) ↦
        componentObj (K := K) family halving (finProdFinEquiv.symm j)))
      (componentPairRestricted K s m) := by
  classical
  let N := DWZTable2Counts.component s * m
  let T := TensorObj.kron
    ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
    ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)
  let B := fun j : Fin (A * H) ↦
    componentObj (K := K) family halving (finProdFinEquiv.symm j)
  have hsource : ∃ router : ∀ i, (componentPairAmbient K s m).V i →ₗ[K] T.V i,
      PiTensorProduct.map router (componentPairAmbient K s m).t = T.t ∧
      ∀ w₁ w₂,
        (¬ componentWordAllowed s m w₁ ∨ ¬ componentWordAllowed s m w₂) →
        ∀ p : Fin A × Fin H,
          ((componentProj (K := K) family halving p 2).comp (router 2))
            (componentPowerZBasis K s m w₁ ⊗ₜ[K]
              componentPowerZBasis K s m w₂) = 0 := by
    rcases hs with rfl | rfl
    · exact mme_dwz_q6_121_common_halving_ambient_component_source_maps
        m L G A H family halving
    · exact mme_dwz_q6_211_common_halving_ambient_component_source_maps
        m L G A H family halving
  obtain ⟨router, hrouter, hsourcezero⟩ := hsource
  let proj : ∀ j i, T.V i →ₗ[K] (B j).V i :=
    fun j i ↦ componentProj family halving (finProdFinEquiv.symm j) i
  have hdiag : ∀ j, PiTensorProduct.map (proj j) T.t = (B j).t := by
    intro j
    change PiTensorProduct.map
        (fun i ↦ TensorProduct.map
          (gradedAddressProj (leftGrading (K := K)) N
            (leftAddress family halving (finProdFinEquiv.symm j)) i)
          (gradedAddressProj (rightGrading (K := K)) N
            (rightAddress family halving (finProdFinEquiv.symm j)) i))
        (interchange _ _) = interchange _ _
    rw [TensorObj.TypeGrading.kronMap_interchange,
      MME.RestrictedPairedExtraction.map_gradedAddressProj,
      MME.RestrictedPairedExtraction.map_gradedAddressProj]
  have hmixed : ∀ js : Fin 3 → Fin (A * H), (¬ ∃ j, js = fun _ ↦ j) →
      PiTensorProduct.map (fun i ↦ proj (js i) i) T.t = 0 := by
    intro js hnot
    apply mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
    intro hsupported
    have heq := hinduced _ _ _ hsupported
    apply hnot
    refine ⟨js 0, funext fun i ↦ ?_⟩
    have h01 : js 0 = js 1 := finProdFinEquiv.symm.injective heq.1
    have h02 : js 0 = js 2 := finProdFinEquiv.symm.injective (heq.1.trans heq.2)
    fin_cases i <;> simp_all
  let extract : ∀ i, T.V i →ₗ[K] (TensorObj.bigAdd B).V i :=
    fun i ↦ ∑ j : Fin (A * H), (gradedBigAddSlot (A * H) B j i).comp (proj j i)
  have hextract : PiTensorProduct.map extract T.t = (TensorObj.bigAdd B).t :=
    MME.RestrictedPairedExtraction.blocks_map T B proj hdiag hmixed
  let maps : ∀ i, (componentPairAmbient K s m).V i →ₗ[K]
      (TensorObj.bigAdd B).V i := fun i ↦ (extract i).comp (router i)
  have htensor : PiTensorProduct.map maps (componentPairAmbient K s m).t =
      (TensorObj.bigAdd B).t := by
    change PiTensorProduct.map (fun i ↦ (extract i).comp (router i)) _ = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hrouter, hextract]
  have hzero : ∀ w₁ w₂,
      (¬ componentWordAllowed s m w₁ ∨ ¬ componentWordAllowed s m w₂) →
      maps 2 (componentPowerZBasis K s m w₁ ⊗ₜ[K]
        componentPowerZBasis K s m w₂) = 0 := by
    intro w₁ w₂ hbad
    change (∑ j : Fin (A * H),
      (gradedBigAddSlot (A * H) B j 2).comp (proj j 2))
      (router 2 (componentPowerZBasis K s m w₁ ⊗ₜ[K]
        componentPowerZBasis K s m w₂)) = 0
    rw [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    change gradedBigAddSlot (A * H) B j 2
      (((componentProj (K := K) family halving (finProdFinEquiv.symm j) 2).comp
        (router 2)) (_ ⊗ₜ[K] _)) = 0
    rw [hsourcezero w₁ w₂ hbad, map_zero]
  exact ⟨fun i ↦ (maps i).comp (componentPairInclusion K s m i),
    mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
      s m (TensorObj.bigAdd B) maps htensor hzero⟩

namespace MME.RestrictedPairedExtraction

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

end MME.RestrictedPairedExtraction

/-- A paired-induced family extracts one matrix tensor per entry from the
literal allowed-word source, with the exact common volume. -/
theorem solution
    {K : Type u} [Field K] (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hinduced : family.PairedCyclicInduced halving) :
    ∃ a b c : Fin (A * H) → ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (componentPairRestricted K s m) ∧
      ∀ j, a j * b j * c j = 6 ^ (4 * G + 2 * L) := by
  let index : Fin (A * H) → Fin A × Fin H := finProdFinEquiv.symm
  refine ⟨fun j => componentM family halving (index j),
    fun j => componentN family halving (index j),
    fun j => componentP family halving (index j), ?_, ?_⟩
  · apply TensorObj.Restrict.trans _
      (mme_dwz_q6_paired_induced_restricted_component_direct_sum
        s hs m L G A H family halving hinduced)
    exact (MME.RestrictedPairedExtraction.bigAdd_respects_iso (A * H) _ _
      (fun j => (mme_CW_q6_common_halving_paired_oriented_component_certificate
        (K := K) family halving (index j)).1)).1
  · intro j
    exact (mme_CW_q6_common_halving_paired_oriented_component_certificate
      (K := K) family halving (index j)).2
