-- Prove2me | solution 1 for mme_recursive_yz_repaired_CW_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T11:22:16.644961+00:00
-- url     : https://prove2.me/submissions/0dd02e80-212a-44a8-bf98-690e6f5c95c3

import Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_recursive_yz_actual_CW_cell_finite_hole_repair
import Theorems.Thm_mme_recursive_yz_actual_CW_power_extraction
import Theorems.Thm_mme_recursive_yz_same_type_cell_permutation
import Theorems.Thm_mme_recursive_yz_nonhole_implies_owned
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Definitions.Def_mme_recursive_yz_CW_cells
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_modern_three_mode_projected_tensor
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.DWZComponentRestriction MME.ModernRepair Module
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


theorem solution {K : Type u} [Field K] (q ell half R N p L d h k : ℕ)
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (positions : Fin L ≃ Position n)
    (S : Finset (ZMod p)) (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m)
    (address : Fin k → Address half R parent n) (hinj : Function.Injective address)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hE : ∀ j, address j ∈ RecursiveXHash.bucketed m e S state)
    (hHash : ∀ j, address j ∈ RecursiveXHash.hashed m e S state)
    (hiso : ∀ j b, b ∈ RecursiveXHash.bucketed m e S state →
      RecursiveXHash.block 0 (address j) = RecursiveXHash.block 0 b → address j = b)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) (hmu : BoundaryProfiles mu)
    (keep : Fin 2 → Fin k → (Position n → CompleteWord ell) → Prop)
    (hholes : ∀ j i, 4 * d * (filterHoles htotal m e S state i (mu (yzMode i))
      (address j) (keep i j)).card ≤ (unbrokenWords htotal (yzMode i) (address j) (mu (yzMode i))).card)
    (hcapacity : (∏ i : Fin 3, Nat.card (Block ell (fullCell htotal ref)
      (fun c i ↦ (c.2.val i).val) mu i)) < d ^ h) :
    Restrict (bigAdd (fun _ : Fin (k / 8 ^ h) ↦
      unbroken K q ell L positions (fullCell htotal ref) (fun c i ↦ (c.2.val i).val) mu))
      (source K q ell L) := by
  classical
  letI : DecidableEq (Position n) := Classical.decEq _
  let cell := fullCell htotal ref
  let shape : Cell half R parent → Fin 3 → ℕ := fun c i ↦ (c.2.val i).val
  let T := source K q ell L
  let b := basis K q ell L
  let U := unbroken K q ell L positions cell shape mu
  let G := grading K q ell L positions cell shape mu
  obtain ⟨B,blockLabel,hB,hLabel,hrepair⟩ :=
    mme_recursive_yz_actual_CW_cell_finite_hole_repair (K := K) q ell L positions cell shape mu
  have hnorm (j : Fin k) : ∃ sigma : Equiv.Perm (Position n),
      ∀ p, fullCell htotal (address j) (sigma p) = cell p :=
    mme_recursive_yz_same_type_cell_permutation htotal m (address j) ref (hT j) href
  choose sigma hsigma using hnorm
  let words := fun j i ↦ unbrokenWords htotal i (address j) (mu i)
  let E : ∀ j i, Block ell cell shape mu i ≃ (words j i) := fun j i ↦ {
    toFun := fun f ↦ ⟨fun p ↦ f.val ((sigma j).symm p), by
      have H := word_transport (fullCell htotal (address j)) cell (sigma j) (hsigma j)
        CWCells.grade (fun c ↦ shape c i) (mu i) f.val f.property
      simpa only [words,unbrokenWords,Finset.mem_filter,Finset.mem_univ,true_and,Graded,CWCells.grade,shape] using H⟩
    invFun := fun f ↦ ⟨fun p ↦ f.val (sigma j p), by
      have H : (∀ p, CWCells.grade (f.val p) = shape (fullCell htotal (address j) p) i) ∧
          Useful (fullCell htotal (address j)) (mu i) f.val := by
        simpa only [words,unbrokenWords,Finset.mem_filter,Finset.mem_univ,true_and,Graded,CWCells.grade,shape] using f.property
      have H' := word_transport cell (fullCell htotal (address j)) (sigma j).symm
        (fun p ↦ by simpa only [Equiv.apply_symm_apply] using (hsigma j ((sigma j).symm p)).symm)
        CWCells.grade (fun c ↦ shape c i) (mu i) f.val H
      simpa only [Equiv.symm_symm] using H'⟩
    left_inv := by intro f; apply Subtype.ext; funext p; simp
    right_inv := by intro f; apply Subtype.ext; funext p; simp }
  have hcard (j i) : Nat.card (Block ell cell shape mu i) = (words j i).card := by
    rw [Nat.card_congr (E j i), Nat.card_eq_fintype_card, Fintype.card_coe]
  let bad : Fin k → Fin 3 → Finset (Position n → CompleteWord ell) := fun j i ↦
    if i = 1 then filterHoles htotal m e S state 0 (mu 1) (address j) (keep 0 j)
    else if i = 2 then filterHoles htotal m e S state 1 (mu 2) (address j) (keep 1 j) else ∅
  have hbad (j i) : bad j i ⊆ words j i := by
    intro f hf
    fin_cases i
    · simp [bad] at hf
    · simpa only [bad, show (1 : Fin 3) ≠ 2 by decide, if_true, yzMode] using
        (show f ∈ unbrokenWords htotal (yzMode 0) (address j) (mu 1) from by
          have hh : f ∈ filterHoles htotal m e S state 0 (mu 1) (address j) (keep 0 j) := by simpa [bad] using hf
          rcases Finset.mem_union.mp hh with hh | hh <;> exact (Finset.mem_filter.mp hh).1)
    · have hh : f ∈ filterHoles htotal m e S state 1 (mu 2) (address j) (keep 1 j) := by simpa [bad] using hf
      rcases Finset.mem_union.mp hh with hh | hh <;> exact (Finset.mem_filter.mp hh).1
  let holes : Fin k → (i : Fin 3) → Finset (Block ell cell shape mu i) :=
    fun j i ↦ Finset.univ.filter (fun f ↦ (E j i f).val ∈ bad j i)
  have hholes' (j i) : 4 * d * (holes j i).card ≤ Nat.card (Block ell cell shape mu i) := by
    rw [transported_hole_card _ _ (E j i) (hbad j i), hcard j i]
    fin_cases i
    · simp [bad]
    · simpa only [bad, if_true, words, yzMode] using hholes j 0
    · simpa only [bad, show (2 : Fin 3) ≠ 1 by decide, if_false, if_true, words, yzMode] using hholes j 1
  have hcopies (j : Fin k) :
      Restrict (projected U B blockLabel (fun i ↦ Finset.univ \ holes j i))
        (T.basisAllAllowedSubtensor b (fun i x ↦ Owned htotal address mu j i (CWCells.label q ell L positions x))) := by
    let perm := leafPermutation ell L positions (sigma j)
    obtain ⟨P,hP,ht⟩ := mme_kronPow_position_permutation_linear_equiv (CWObj K q)
      (fun i ↦ (MME.DWZStep1Support.cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
      (L * 2 ^ (ell - 1)) perm
    apply projection_of_owned T b (allowed q ell L positions cell shape mu)
      (fun i x ↦ Owned htotal address mu j i (CWCells.label q ell L positions x)) B hB blockLabel
      (fun i ↦ (P i).toLinearMap) (fun _ x r ↦ x (perm r)) hP ht
      (fun i ↦ Finset.univ \ holes j i)
    intro i x ha hn
    let f := blockLabel i ⟨fun r ↦ x (perm r), ha⟩
    have hEF : (E j i f).val = CWCells.label q ell L positions x := by
      change (fun p ↦ f.val ((sigma j).symm p)) = _
      dsimp only [f]
      rw [hLabel, label_reindex]
      simp only [Equiv.apply_symm_apply]
    have hword : CWCells.label q ell L positions x ∈ words j i := by
      rw [← hEF]
      exact (E j i f).property
    have hnot : CWCells.label q ell L positions x ∉ bad j i := by
      rw [← hEF]
      exact fun hh ↦ (Finset.mem_sdiff.mp hn).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    fin_cases i
    · obtain ⟨hg,hu⟩ := by simpa only [words,unbrokenWords,Finset.mem_filter,Finset.mem_univ,true_and] using hword
      exact ⟨hg,hu,by simp,by simp⟩
    · apply mme_recursive_yz_nonhole_implies_owned htotal m e S state address hinj hT hHash mu 0 j (keep 0 j)
        (CWCells.label q ell L positions x) hword
      simpa [bad] using hnot
    · apply mme_recursive_yz_nonhole_implies_owned htotal m e S state address hinj hT hHash mu 1 j (keep 1 j)
        (CWCells.label q ell L positions x) hword
      simpa [bad] using hnot
  have hextract := mme_recursive_yz_actual_CW_power_extraction (K := K) q ell half R k N p L
    parent n htotal hhalf m e positions S state address hT hE hiso mu hmu
  let copies := fun j : Fin k ↦ projected U B blockLabel (fun i ↦ Finset.univ \ holes j i)
  have hkg : (k / 8 ^ h) * 8 ^ h ≤ k := Nat.div_mul_le_self _ _
  let index := fun a : Fin (k / 8 ^ h) ↦ fun b : Fin (8 ^ h) ↦
    Fin.castLE hkg (finProdFinEquiv (a,b))
  let X := fun a b ↦ copies (index a b)
  have hgroup (a : Fin (k / 8 ^ h)) : Restrict U (bigAdd (X a)) :=
    hrepair d h hcapacity (fun b ↦ holes (index a b)) (fun b i ↦ hholes' (index a b) i)
  have HG := mme_bigAdd_fin_mul_grouped_restrict X (fun _ ↦ U) hgroup
  have HE : Restrict (bigAdd (fun r : Fin ((k / 8 ^ h) * 8 ^ h) ↦
      X (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)) (bigAdd copies) := by
    have hfun : (fun r : Fin ((k / 8 ^ h) * 8 ^ h) ↦
        X (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2) =
        (fun r ↦ copies (Fin.castLE hkg r)) := by
      funext r
      apply congrArg copies
      apply congrArg (Fin.castLE hkg)
      exact finProdFinEquiv.apply_symm_apply r
    rw [hfun]
    exact mme_bigAdd_prefix_restrict (by decide : 1 < 3) hkg copies
  exact HG.trans (HE.trans ((mme_bigAdd_mono_restrict hcopies).trans hextract))
