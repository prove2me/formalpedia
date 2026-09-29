-- Prove2me | solution 1 for mme_recursive_yz_cell_uniform_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T10:58:08.883628+00:00
-- url     : https://prove2.me/submissions/ee3d3bce-404b-484a-8e68-86bdf0f5eb71

import Definitions.Def_mme_recursive_yz_cell_shuffles
import Theorems.Thm_mme_dwz_available_block_shuffle_of_pretransitive_action

open BigOperators MME.RecursiveYZ MME.DWZSquare
open scoped Classical
set_option autoImplicit false

private theorem count_move {P C W : Type*} [Fintype P]
    (cell : P → C) (e : cellPerm cell) (f : P → W) (c : C) (w : W) :
    count cell (fun p ↦ f ((e.val).symm p)) c w = count cell f c w := by
  classical
  apply Finset.card_equiv e.val.symm
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := (e⁻¹).property p
  change cell (e.val.symm p) = cell p at hc
  rw [hc]

private noncomputable def cellAction {P C W D : Type*} [Fintype P]
    (cell : P → C) (grade : W → D) (shape : C → D) (mu : C → W → ℕ) :
    MulAction (cellPerm cell) (CellWord cell grade shape mu) where
  smul e f := ⟨fun p ↦ f.val (e.val.symm p), by
    constructor
    · intro p
      exact (f.property.1 (e.val.symm p)).trans (congrArg shape ((e⁻¹).property p))
    · intro c w
      exact (count_move cell e f.val c w).trans (f.property.2 c w)⟩
  one_smul f := by apply Subtype.ext; rfl
  mul_smul e f w := by apply Subtype.ext; rfl

private theorem pair_card {P C W : Type*} [Fintype P] [DecidableEq C] [DecidableEq W]
    (cell : P → C) (f : P → W) (v : C × W) :
    Fintype.card {p : P // (cell p,f p) = v} = count cell f v.1 v.2 := by
  classical
  rw [Fintype.card_subtype]
  unfold count
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]

theorem solution {P C W D : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (grade : W → D) (shape : C → D) (mu : C → W → ℕ) :
    ∃ system : AvailableBlockShuffle (CellWord cell grade shape mu) (cellPerm cell),
      ∀ e source, (system.move e source).val = fun p ↦ source.val (e.val.symm p) := by
  classical
  letI := cellAction cell grade shape mu
  have ht : MulAction.IsPretransitive (cellPerm cell) (CellWord cell grade shape mu) := by
    constructor
    intro source target
    have hc (v : C × W) :
        Fintype.card {p : P // (cell p,source.val p) = v} =
        Fintype.card {p : P // (cell p,target.val p) = v} := by
      rw [pair_card, pair_card]
      exact (source.property.2 v.1 v.2).trans (target.property.2 v.1 v.2).symm
    let es := fun v : C × W ↦ Fintype.equivOfCardEq (hc v)
    let e : Equiv.Perm P := Equiv.ofFiberEquiv es
    have he (p : P) : (cell (e p),target.val (e p)) = (cell p,source.val p) :=
      Equiv.ofFiberEquiv_map es p
    let g : cellPerm cell := ⟨e,fun p ↦ congrArg Prod.fst (he p)⟩
    refine ⟨g,?_⟩
    apply Subtype.ext
    funext p
    change source.val (e.symm p) = target.val p
    simpa only [Equiv.apply_symm_apply] using (congrArg Prod.snd (he (e.symm p))).symm
  letI := ht
  obtain ⟨system,hs⟩ := mme_dwz_available_block_shuffle_of_pretransitive_action
    (CellWord cell grade shape mu) (cellPerm cell)
  exact ⟨system, fun e source ↦ congrArg Subtype.val (hs e source)⟩
