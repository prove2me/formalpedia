-- Prove2me | solution 1 for mme_prescribed_cell_histogram_card
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:26:40.332637+00:00
-- url     : https://prove2.me/submissions/3653d174-baea-4487-a69b-cb41bb52bd8e

import Definitions.Def_mme_recursive_yz_compatibility
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

private theorem fiber_card {P C W : Type*} [Fintype P]
    (cell : P → C) (f : P → W) (c : C) (w : W) :
    Fintype.card {p : {p : P // cell p = c} // f p.val = w} = count cell f c w := by
  classical
  rw [count, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun p ↦ ⟨p.val.val, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, p.val.property, p.property⟩⟩
    invFun := fun p ↦ ⟨⟨p.val, (Finset.mem_filter.mp p.property).2.1⟩,
      (Finset.mem_filter.mp p.property).2.2⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl }

theorem solution {P C W : Type*} [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (mu : C → W → ℕ)
    (hsum : ∀ c, ∑ w, mu c w = Fintype.card {p : P // cell p = c}) :
    Fintype.card {f : P → W // Useful cell mu f} =
      ∏ c, (Fintype.card {p : P // cell p = c}).factorial / ∏ w, (mu c w).factorial := by
  classical
  let Family := fun c ↦ {g : {p : P // cell p = c} → W //
    ∀ w, Fintype.card {p // g p = w} = mu c w}
  have reconstruct (F : ∀ c, Family c) (c : C) :
      (fun p : {p : P // cell p = c} ↦ (F (cell p.val)).val ⟨p.val,rfl⟩) = (F c).val := by
    funext p
    obtain ⟨p,hp⟩ := p
    subst c
    rfl
  let e : {f : P → W // Useful cell mu f} ≃ (∀ c, Family c) := {
    toFun := fun f c ↦ ⟨fun p ↦ f.val p.val, by
      intro w
      rw [fiber_card]
      exact f.property c w⟩
    invFun := fun F ↦ ⟨fun p ↦ (F (cell p)).val ⟨p,rfl⟩, by
      intro c w
      rw [← fiber_card]
      have hh := congrFun (reconstruct F c)
      simp_rw [hh]
      exact (F c).property w⟩
    left_inv := by intro f; rfl
    right_inv := by
      intro F
      funext c
      apply Subtype.ext
      exact reconstruct F c }
  rw [Fintype.card_congr e, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c hc
  exact mme_fintype_prescribed_fiber_function_card (mu c) (hsum c)
