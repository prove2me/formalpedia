-- Prove2me | solution 1 for mme_released_hashed_recipe_reference_transport
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:10:31.654433+00:00
-- url     : https://prove2.me/submissions/177a41f8-42ef-4fb0-8bcb-a33fd14719ad

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem solution (K ell : ℕ) (a a' : ∀ o : Fin 6, Reference o K) (eps : Fin 6 → ℝ)
    (R : LogJointRecipeG (partSize K a' 1) ell (QPos K a' eps)) :
    ∃ R' : LogJointRecipeG (partSize K a 1) ell (QPos K a eps),
      R'.inputs = R.inputs ∧ R'.logOutputs = R.logOutputs ∧ R'.dims = R.dims := by
  -- Step 1: the two references have the same shape histogram for every owner.
  have hfib : ∀ o c, Fintype.card {b : Fin (blocks K) // (a o).val 0 b = c} =
      Fintype.card {b : Fin (blocks K) // (a' o).val 0 b = c} := by
    intro o c
    have h1 := (a o).property
    have h2 := (a' o).property
    simp only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have e1 := h1 0 c
    have e2 := h2 0 c
    simp only [MME.RecursiveThinSplit.count] at e1 e2
    rw [Fintype.card_subtype, Fintype.card_subtype, e1, e2]
  -- Step 2: per-owner block permutations carrying one reference to the other.
  let σ : ∀ o : Fin 6, Fin (blocks K) ≃ Fin (blocks K) := fun o ↦
    Equiv.ofFiberEquiv (fun c ↦ Fintype.equivOfCardEq (hfib o c))
  have hσ : ∀ o b, (a' o).val 0 (σ o b) = (a o).val 0 b := fun o b ↦
    Equiv.ofFiberEquiv_map _ b
  let τB : Blk K ≃ Blk K := Equiv.sigmaCongrRight σ
  have hcell : ∀ b : Blk K, cellOf K a' (τB b) = cellOf K a b := by
    intro b
    exact hσ b.1 b.2
  let τ : PBlk K a ≃ PBlk K a' :=
    τB.subtypeEquiv (fun b ↦ by rw [hcell b])
  -- Step 3: the induced equivalence of hashed fine positions.
  let π : Fin (partSize K a' 1) ≃ Fin (partSize K a 1) :=
    (finCongr (pLen K a')).symm.trans (finProdFinEquiv.symm.trans
      ((Equiv.prodCongr (((pEnum K a').symm.trans τ.symm).trans (pEnum K a)) (Equiv.refl _)).trans
        (finProdFinEquiv.trans (finCongr (pLen K a)))))
  have hword : ∀ (x : FineWord (partSize K a 1)) (b : PBlk K a),
      pBlockWord K a' (fun r ↦ x (π r)) (τ b) = pBlockWord K a x b := by
    intro x b
    funext r
    simp [pBlockWord, π]
  -- Step 4: the transported source lies in the original source.
  have hinside : ∀ i x, QPos K a' eps i (fun r ↦ x (π r)) → QPos K a eps i x := by
    intro i x ⟨hg, hh⟩
    refine ⟨fun b ↦ ?_, fun o c hc w ↦ ?_⟩
    · have := hg (τ b)
      rw [hword x b] at this
      rw [this]
      show (((cellOf K a' (τB b.val)).val (hashMode b.val.1 i)).val) = _
      rw [hcell b.val]
    · have := hh o c hc w
      have hcard : Fintype.card {b : PBlk K a // b.val.1 = o ∧ (a o).val 0 b.val.2 = c ∧
            pBlockWord K a x b = w} =
          Fintype.card {b : PBlk K a' // b.val.1 = o ∧ (a' o).val 0 b.val.2 = c ∧
            pBlockWord K a' (fun r ↦ x (π r)) b = w} := by
        refine Fintype.card_congr (τ.subtypeEquiv ?_)
        intro b
        rw [hword x b]
        constructor
        · rintro ⟨h1, h2, h3⟩
          subst h1
          exact ⟨rfl, (hσ _ _).trans h2, h3⟩
        · rintro ⟨h1, h2, h3⟩
          have h1' : b.val.1 = o := h1
          subst h1'
          exact ⟨rfl, (hσ _ _).symm.trans h2, h3⟩
      rw [hcard]
      exact this
  -- Step 5: a one-part partition performs the relabelling.
  let pos : ((j : Fin 1) × Fin ((fun _ : Fin 1 ↦ partSize K a' 1) j)) ≃ Fin (partSize K a 1) :=
    { toFun := fun p ↦ π p.2
      invFun := fun z ↦ ⟨0, π.symm z⟩
      left_inv := by
        rintro ⟨j, r⟩
        have hj : j = 0 := Fin.eq_zero j
        subst hj
        simp
      right_inv := by
        intro z
        simp }
  refine ⟨LogJointRecipeG.partition (fun _ ↦ partSize K a' 1) pos (fun _ ↦ QPos K a' eps)
    (fun i x hx ↦ hinside i x (hx 0)) (fun _ ↦ R), ?_, ?_, ?_⟩
  · simp [LogJointRecipeG.inputs]
  · simp [LogJointRecipeG.logOutputs]
  · simp [LogJointRecipeG.dims]
