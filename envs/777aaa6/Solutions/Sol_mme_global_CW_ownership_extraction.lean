-- Prove2me | solution 1 for mme_global_CW_ownership_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:17:34.70802+00:00
-- url     : https://prove2.me/submissions/306baba2-a6cc-4261-b25e-7ba6fbb6914d

import Definitions.Def_mme_global_CW_stage_data
import Definitions.Def_mme_recursive_x_hash_families
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_modern_CW_full_word_boundary_histograms
import Theorems.Thm_mme_CW_three_canonical_support
import Theorems.Thm_mme_modern_CW_power_nonzero_coefficient_fine_support
import Theorems.Thm_mme_basis_projected_family_restrict

open BigOperators MME MME.CompleteSplit MME.DWZStep1Support MME.RecursiveYZ
open MME.GlobalCW
open scoped Classical
set_option autoImplicit false
universe u

private theorem count_coarsen {P C W G : Type*} [Fintype P] [Fintype C]
    (cell : P → C) (f : P → W) (group : C → G) (g : G) (w : W) :
    count (group ∘ cell) f g w = ∑ c, if group c = g then count cell f c w else 0 := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  have pull (c : C) :
      (if group c = g then ∑ p, if cell p = c ∧ f p = w then (1 : ℕ) else 0 else 0) =
      ∑ p, if group c = g then (if cell p = c ∧ f p = w then (1 : ℕ) else 0) else 0 := by
    by_cases h : group c = g <;> simp [h]
  simp_rw [pull]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : f p = w
  · simp only [h, and_true, Function.comp_apply]
    rw [Finset.sum_eq_single (cell p)]
    · simp
    · intro c hc hcp
      simp [Ne.symm hcp]
    · simp
  · simp [h]


private theorem group_block_eq {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (i : Fin 3) (a b : Address half R parent n)
    (h : RecursiveXHash.block i a = RecursiveXHash.block i b) :
    modeGroup i ∘ GlobalCW.cell a = modeGroup i ∘ GlobalCW.cell b := by
  funext p
  apply Prod.ext
  · rfl
  have heq := congrFun (congrFun h p.1) p.2
  change (a p.1 p.2).val i = (b p.1 p.2).val i at heq
  exact heq


private theorem useful_aggregate {P C W G : Type*} [Fintype P] [Fintype C]
    (cell : P → C) (group : C → G) (mu : C → W → ℕ) (f : P → W)
    (hu : Useful cell mu f) (g : G) (w : W) :
    count (group ∘ cell) f g w = ∑ c, if group c = g then mu c w else 0 := by
  classical
  rw [count_coarsen]
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs
  · exact hu c w
  · rfl

private theorem histogram_card_eq_count {P C W : Type*} [Fintype P] [DecidableEq C] [DecidableEq W]
    (cell : P → C) (f : P → W) (c : C) (w : W) :
    Fintype.card {p : P // cell p = c ∧ f p = w} = count cell f c w := by
  classical
  rw [Fintype.card_subtype]
  unfold count
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private theorem fine_grade_sum {K : Type u} [Field K] (q ell half : ℕ)
    (hhalf : half = 2 * 2 ^ (ell - 1)) (w : Fin 3 → CompleteWord ell)
    (hsupport : ∀ r, (cwThreeCanonicalGrading K q).blockTensor (fun i ↦ w i r) ≠ 0) :
    (∑ r, (w 0 r).val) + (∑ r, (w 1 r).val) + (∑ r, (w 2 r).val) = half := by
  have hs (r) : (w 0 r).val + (w 1 r).val + (w 2 r).val = 2 := by
    by_contra h
    exact hsupport r (mme_CW_three_canonical_support K q (fun i ↦ w i r) h)
  calc
    _ = ∑ r, ((w 0 r).val + (w 1 r).val + (w 2 r).val) := by
      simp only [Finset.sum_add_distrib]
    _ = ∑ _ : Fin (2 ^ (ell - 1)), 2 := Finset.sum_congr rfl (fun r _ ↦ hs r)
    _ = _ := by simp [hhalf, Nat.mul_comm]

private theorem mixed_address {K : Type u} [Field K] {q half R ell k : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (address : Fin k → Address half R parent n) (js : Fin 3 → Fin k)
    (word : Fin 3 → Place n → CompleteWord ell)
    (hgraded : ∀ i, GlobalCW.Graded i (address (js i)) (word i))
    (hsupport : ∀ p r, (cwThreeCanonicalGrading K q).blockTensor
      (fun i ↦ word i p r) ≠ 0) :
    ∃ a : Address half R parent n, ∀ i,
      RecursiveXHash.block i a = RecursiveXHash.block i (address (js i)) := by
  have hsum (r : Fin R) (t : Fin (n r)) :
      ((address (js 0) r t).val 0).val + ((address (js 1) r t).val 1).val +
        ((address (js 2) r t).val 2).val = half := by
    have h := fine_grade_sum q ell half hhalf (fun i ↦ word i ⟨r,t⟩) (hsupport ⟨r,t⟩)
    have hi (i : Fin 3) : ∑ s, (word i ⟨r,t⟩ s).val =
        ((address (js i) r t).val i).val := by
      simpa only [GlobalCW.Graded, GlobalCW.cell, CWCells.grade] using hgraded i ⟨r,t⟩
    simpa only [hi] using h
  let a : Address half R parent n := fun r t ↦
    ⟨fun i ↦ (address (js i) r t).val i, hsum r t,
      fun i ↦ (address (js i) r t).property.2 i⟩
  exact ⟨a,fun _ ↦ rfl⟩

private theorem mixed_retained {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (owner : Fin 3 → Address half R parent n)
    (hT : ∀ i, owner i ∈ RecursiveXHash.target m)
    (hE : ∀ i, owner i ∈ RecursiveXHash.bucketed m e S state)
    (a : Address half R parent n)
    (hblock : ∀ i, RecursiveXHash.block i a = RecursiveXHash.block i (owner i)) :
    a ∈ RecursiveXHash.bucketed m e S state := by
  classical
  have hTA := (mme_recursive_x_hash_family_counts half R parent n m).1
  have haA : a ∈ RecursiveXHash.ambient m := by
    simp only [RecursiveXHash.ambient, Finset.mem_filter, Finset.mem_univ, true_and]
    intro r i j
    have ho : ∀ r, RecursiveThinSplit.HasMarginalCounts (owner i r) (m r) := by
      simpa only [RecursiveXHash.ambient, Finset.mem_filter, Finset.mem_univ,
        true_and] using hTA (hT i)
    have hh := ho r i j
    have hb := congrFun (hblock i) r
    change (fun t ↦ (a r t).val i) = (fun t ↦ (owner i r t).val i) at hb
    change RecursiveThinSplit.count (fun t ↦ (a r t).val i) j = _
    rw [hb]
    exact hh
  have hf (i : Fin 3) : RecursiveXHash.fieldWord p e i a =
      RecursiveXHash.fieldWord p e i (owner i) := by
    funext t
    exact congrArg (fun v : Fin (half + 1) ↦ (v.val : ZMod p))
      (congrFun (congrFun (hblock i) (e t).1) (e t).2)
  have hx := hE 0
  have hy := hE 1
  have hz := hE 2
  simp only [RecursiveXHash.bucketed, Finset.mem_filter] at hx hy hz ⊢
  refine ⟨haA,?_,?_,?_⟩
  · rw [hf 0]; exact hx.2.1
  · rw [hf 1]; exact hy.2.2.1
  · rw [hf 2]; exact hz.2.2.2

private theorem owned_support_unique {K : Type u} [Field K] {q half R ell k N p : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (address : Fin k → Address half R parent n)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hE : ∀ j, address j ∈ RecursiveXHash.bucketed m e S state)
    (hiso : ∀ j b, b ∈ RecursiveXHash.bucketed m e S state →
      RecursiveXHash.block 0 (address j) = RecursiveXHash.block 0 b → address j = b)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (hmu : BoundaryProfiles mu)
    (js : Fin 3 → Fin k) (word : Fin 3 → Place n → CompleteWord ell)
    (howned : ∀ i, GlobalCW.Owned address mu (js i) i (word i))
    (hsupport : ∀ t r, (cwThreeCanonicalGrading K q).blockTensor
      (fun i ↦ word i t r) ≠ 0) : js 0 = js 1 ∧ js 0 = js 2 := by
  classical
  obtain ⟨a,ha⟩ := mixed_address hhalf address js word (fun i ↦ (howned i).1) hsupport
  have haE := mixed_retained m e S state (fun i ↦ address (js i))
    (fun i ↦ hT (js i)) (fun i ↦ hE (js i)) a ha
  have hae : address (js 0) = a := hiso (js 0) a haE (ha 0).symm
  have hgroup (i : Fin 3) :
      modeGroup i ∘ GlobalCW.cell (address (js i)) =
        modeGroup i ∘ GlobalCW.cell (address (js 0)) := by
    apply group_block_eq
    exact (ha i).symm.trans (congrArg (RecursiveXHash.block i) hae.symm)
  let cell := GlobalCW.cell (address (js 0))
  let coarse : Cell half R parent → Fin 3 → ℕ := fun c i ↦ (c.2.val i).val
  have hc : ∀ i t, ∑ r, (word i t r).val = coarse (cell t) i := by
    intro i t
    have hg := congrArg (fun v : Fin R × Fin (half + 1) ↦ v.2.val) (congrFun (hgroup i) t)
    exact ((howned i).1 t).trans hg
  have hboundary := mme_modern_CW_full_word_boundary_histograms q cell coarse word hc hsupport
  have hyb (c : Cell half R parent) (hb : yBoundary c) (w : CompleteWord ell) :
      count cell (word 1) c w = mu 1 c w := by
    have h := hboundary.1 c hb w
    rw [histogram_card_eq_count, histogram_card_eq_count] at h
    exact h.trans (((howned 0).2.1 c (fun r ↦ Fin.rev (w r))).trans (hmu.1 c hb w).symm)
  have hy : Compatible cell yBoundary (modeGroup 1) (mu 1) (word 1) := by
    refine ⟨hyb,?_⟩
    intro g w
    have h := useful_aggregate (GlobalCW.cell (address (js 1))) (modeGroup 1)
      (mu 1) (word 1) (howned 1).2.1 g w
    rw [hgroup 1] at h
    exact h
  have h01 : js 0 = js 1 := (howned 1).2.2.1 rfl (js 0)
    (by rw [hae]; exact ha 1) hy
  have hyuse : Useful cell (mu 1) (word 1) := by
    simpa only [cell, h01] using (howned 1).2.1
  have hzb (c : Cell half R parent) (hb : zBoundary c) (w : CompleteWord ell) :
      count cell (word 2) c w = mu 2 c w := by
    rcases hb with hb | hb
    · have h := hboundary.2.1 c hb w
      rw [histogram_card_eq_count, histogram_card_eq_count] at h
      exact h.trans ((hyuse c (fun r ↦ Fin.rev (w r))).trans (hmu.2.1 c hb w).symm)
    · have h := hboundary.2.2 c hb w
      rw [histogram_card_eq_count, histogram_card_eq_count] at h
      exact h.trans (((howned 0).2.1 c (fun r ↦ Fin.rev (w r))).trans (hmu.2.2 c hb w).symm)
  have hz : Compatible cell zBoundary (modeGroup 2) (mu 2) (word 2) := by
    refine ⟨hzb,?_⟩
    intro g w
    have h := useful_aggregate (GlobalCW.cell (address (js 2))) (modeGroup 2)
      (mu 2) (word 2) (howned 2).2.1 g w
    rw [hgroup 2] at h
    exact h
  exact ⟨h01,(howned 2).2.2.2 rfl (js 0) (by rw [hae]; exact ha 2) hz⟩

open Module MME.TensorObj

theorem solution {K : Type u} [Field K] (q ell half R k N p L : ℕ)
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (positions : Fin L ≃ Place n)
    (S : Finset (ZMod p)) (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (address : Fin k → Address half R parent n)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hE : ∀ j, address j ∈ RecursiveXHash.bucketed m e S state)
    (hiso : ∀ j b, b ∈ RecursiveXHash.bucketed m e S state →
      RecursiveXHash.block 0 (address j) = RecursiveXHash.block 0 b → address j = b)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (hmu : BoundaryProfiles mu)
    (parentKeep : Fin 3 → (Place n → CompleteWord ell) → Prop) :
    let T := (CWObj K q).kronPow (L * 2 ^ (ell - 1))
    let b := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (L * 2 ^ (ell - 1))
    let label := fun (w : Fin (L * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
      (p : Place n) (r : Fin (2 ^ (ell - 1))) ↦
        cwSquareCoordGrade q (w (finProdFinEquiv (positions.symm p, r))).down
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦ T.basisAllAllowedSubtensor b
        (fun i x ↦ GlobalCW.Owned address mu j i (label x) ∧ parentKeep i (label x))))
      (T.basisAllAllowedSubtensor b (fun i x ↦ parentKeep i (label x))) := by
  classical
  let T := (CWObj K q).kronPow (L * 2 ^ (ell - 1))
  let b := fun i ↦ kronPowModeWordBasis (CWObj K q) i
    ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (L * 2 ^ (ell - 1))
  let label := fun (w : Fin (L * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
    (p : Place n) (r : Fin (2 ^ (ell - 1))) ↦
      cwSquareCoordGrade q (w (finProdFinEquiv (positions.symm p, r))).down
  have huniq (x : Fin 3 → Fin (L * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
      (js : Fin 3 → Fin k)
      (hc : (Basis.piTensorProduct b).repr T.t x ≠ 0)
      (ho : ∀ i, GlobalCW.Owned address mu (js i) i (label (x i))) :
      js 0 = js 1 ∧ js 0 = js 2 := by
    have hs := mme_modern_CW_power_nonzero_coefficient_fine_support q ell L x hc
    exact owned_support_unique hhalf m e S state address hT hE hiso mu hmu
      js (fun i ↦ label (x i)) ho (fun p r ↦ hs (positions.symm p) r)
  apply mme_basis_projected_family_restrict T b
    (fun i x ↦ parentKeep i (label x))
    (fun j i x ↦ GlobalCW.Owned address mu j i (label x) ∧ parentKeep i (label x))
    (fun _ _ _ h ↦ h.2)
  intro x js hc ho
  have hu := huniq x js hc (fun i ↦ (ho i).1)
  refine ⟨js 0, ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact hu.1.symm
  · exact hu.2.symm
