-- Prove2me | Theorems.Thm_mme_global_CW_repaired_extraction
-- name    : mme_global_CW_repaired_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:24:45.86295+00:00
-- url     : https://prove2.me/theorems/c551ceb0-00e5-41de-9bae-7417c860d674
-- title:
--   Actual finite hole repair for unpaired global CW blocks
-- statement:
--   Constructs an actual restriction to repaired copies of a common global template, using direct global ownership and same-type cell transport. Hole-cardinality and cell-capacity assumptions are explicit finite inequalities.
-- source:
--   Finite global extraction for More Asymmetry Proposition 5.1 and Theorem 5.3.

import Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_recursive_yz_actual_CW_cell_finite_hole_repair
import Theorems.Thm_mme_global_CW_ownership_extraction
import Theorems.Thm_mme_global_CW_same_type_cell_permutation
import Theorems.Thm_mme_global_CW_nonhole_implies_owned
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Definitions.Def_mme_recursive_yz_CW_cells
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_modern_three_mode_projected_tensor
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.DWZComponentRestriction MME.ModernRepair Module
open MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v w

private theorem count_transport {P C W : Type*} [Fintype P]
    (a b : P → C) (sigma : Equiv.Perm P) (hs : ∀ p, a (sigma p) = b p)
    (f : P → W) (c : C) (w : W) :
    count a (fun p ↦ f (sigma.symm p)) c w = count b f c w := by
  classical
  apply Finset.card_equiv sigma.symm
  intro p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← hs (sigma.symm p),Equiv.apply_symm_apply]

private theorem word_transport {P C W D : Type*} [Fintype P]
    (a b : P → C) (sigma : Equiv.Perm P) (hs : ∀ p, a (sigma p) = b p)
    (grade : W → D) (shape : C → D) (mu : C → W → ℕ)
    (f : P → W) (hf : (∀ p, grade (f p) = shape (b p)) ∧ Useful b mu f) :
    (∀ p, grade (f (sigma.symm p)) = shape (a p)) ∧
      Useful a mu (fun p ↦ f (sigma.symm p)) := by
  constructor
  · intro p
    simpa only [← hs (sigma.symm p),Equiv.apply_symm_apply] using hf.1 (sigma.symm p)
  · intro c w
    exact (count_transport a b sigma hs f c w).trans (hf.2 c w)

private theorem projection_of_owned {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (allow own : ∀ i, I i → Prop)
    (B : ∀ i, Basis {x // allow i x} K ((T.basisAllAllowedSubtensor b allow).V i))
    (hB : ∀ i x, ((T.basisAllAllowedGrading b allow).classOf i 0).subtype (B i x) = b i x.val)
    (blockLabel : ∀ i, {x // allow i x} → Label i)
    (P : ∀ i, T.V i →ₗ[K] T.V i) (idx : ∀ i, I i → I i)
    (hP : ∀ i x, P i (b i x) = b i (idx i x))
    (ht : PiTensorProduct.map P T.t = T.t)
    (keep : ∀ i, Finset (Label i))
    (hown : ∀ i x (ha : allow i (idx i x)), blockLabel i ⟨idx i x,ha⟩ ∈ keep i → own i x) :
    Restrict (projected (T.basisAllAllowedSubtensor b allow) B blockLabel keep)
      (T.basisAllAllowedSubtensor b own) := by
  classical
  let G := T.basisAllAllowedGrading b allow
  let S := T.basisAllAllowedSubtensor b allow
  let F : ∀ i, T.V i →ₗ[K] S.V i := fun i ↦
    (basisLabelProjection (B i) (blockLabel i) (keep i)).comp ((G.blockProj i 0).comp (P i))
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes T
    (projected S B blockLabel keep) b own F
  · change PiTensorProduct.map (fun i ↦
        (basisLabelProjection (B i) (blockLabel i) (keep i)).comp ((G.blockProj i 0).comp (P i))) T.t =
      PiTensorProduct.map (fun i ↦ basisLabelProjection (B i) (blockLabel i) (keep i))
        (PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t)
    rw [PiTensorProduct.map_comp,LinearMap.comp_apply]
    apply congrArg
    calc
      _ = PiTensorProduct.map (fun i ↦ G.blockProj i 0) (PiTensorProduct.map P T.t) :=
        LinearMap.congr_fun (PiTensorProduct.map_comp (f := P) (g := fun i ↦ G.blockProj i 0)) T.t
      _ = _ := by rw [ht]
  · intro i x hx
    change basisLabelProjection (B i) (blockLabel i) (keep i)
      (G.blockProj i 0 (P i (b i x))) = 0
    rw [hP]
    by_cases ha : allow i (idx i x)
    · let y : {x // allow i x} := ⟨idx i x,ha⟩
      have hproj : G.blockProj i 0 (b i y.val) = B i y := by
        rw [← hB i y]
        exact TensorObj.TypeGrading.blockProj_apply_mem G i 0 _ (B i y).property
      rw [hproj]
      have hn : blockLabel i y ∉ keep i := by
        exact fun hk ↦ hx (hown i x ha hk)
      simp [basisLabelProjection, Basis.constr_basis,hn]
    · have hmem : b i (idx i x) ∈ G.classOf i 1 := by
        change b i (idx i x) ∈ Submodule.span K
          (b i '' {w | (if allow i w then (0 : Fin 2) else 1) = 1})
        exact Submodule.subset_span ⟨idx i x,by simp [ha],rfl⟩
      rw [TensorObj.TypeGrading.blockProj_apply_mem_ne G i 0 1 (by decide) _ hmem]
      exact map_zero _

private theorem transported_hole_card {B W : Type*} [Fintype B]
    [DecidableEq B] [DecidableEq W] (U H : Finset W)
    (e : B ≃ U) (hH : H ⊆ U) :
    (Finset.univ.filter (fun b ↦ (e b).val ∈ H)).card = H.card := by
  classical
  apply Finset.card_bij (fun b _ ↦ (e b).val)
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · intro a ha b hb hab
    exact e.injective (Subtype.ext hab)
  · intro w hw
    let b := e.symm ⟨w,hH hw⟩
    refine ⟨b,?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,b,Equiv.apply_symm_apply]
      exact hw
    · simp only [b,Equiv.apply_symm_apply]

private theorem label_reindex {P : Type v} (q ell L : ℕ) (positions : Fin L ≃ P)
    (sigma : Equiv.Perm P) (x : WordIndex.{u} q ell L) :
    CWCells.label q ell L positions (fun r ↦ x (leafPermutation ell L positions sigma r)) =
      fun p ↦ CWCells.label q ell L positions x (sigma p) := by
  funext p r
  simp [CWCells.label, leafPermutation]

theorem mme_global_CW_repaired_extraction {K : Type u} [Field K] (q ell half R N p L d h k : ℕ)
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (positions : Fin L ≃ Place n)
    (S : Finset (ZMod p)) (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m)
    (address : Fin k → Address half R parent n) (hinj : Function.Injective address)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hE : ∀ j, address j ∈ RecursiveXHash.bucketed m e S state)
    (hiso : ∀ j b, b ∈ RecursiveXHash.bucketed m e S state →
      RecursiveXHash.block 0 (address j) = RecursiveXHash.block 0 b → address j = b)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) (hmu : BoundaryProfiles mu)
    (hholes : ∀ j (i : Fin 3), 4 * d *
      (GlobalCW.holes m e S state mu (address j) i).card ≤
        (GlobalCW.words i (address j) (mu i)).card)
    (hcapacity : (∏ i : Fin 3, Nat.card (Block ell (GlobalCW.cell ref)
      (fun c i ↦ (c.2.val i).val) mu i)) < d ^ h) :
    Restrict (bigAdd (fun _ : Fin (k / 8 ^ h) ↦
      unbroken K q ell L positions (GlobalCW.cell ref) (fun c i ↦ (c.2.val i).val) mu))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun _ _ ↦ True)) := by
  sorry
