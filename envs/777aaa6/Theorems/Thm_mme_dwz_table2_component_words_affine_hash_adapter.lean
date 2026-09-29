-- Prove2me | Theorems.Thm_mme_dwz_table2_component_words_affine_hash_adapter
-- name    : mme_dwz_table2_component_words_affine_hash_adapter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:53:09.394166+00:00
-- url     : https://prove2.me/theorems/36fb8809-4ac6-4e15-af0f-2e1780a73f60
-- title:
--   Table-2 component words satisfy the affine-hash support and pair hypotheses
-- statement:
--   Project two distinct words in the fifteen Table-2 component shapes to their $X,Y,Z$ coordinate words, and cast the coordinates into $\mathbb Z/p\mathbb Z$ for $p\geq5$. Each resulting address has pointwise level sum $4$. If the original words share their $X$ projection or share their $Y$ projection, then the cast addresses share that projection and differ in the other one. This supplies exactly the support and distinct-pair hypotheses used by the first asymmetric-hashing incidence bounds.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Table 2 and Section 3.10.

import Definitions.Def_mme_dwz_square_data

set_option autoImplicit false

theorem mme_dwz_table2_component_words_affine_hash_adapter
    {p N : ℕ} (hp : 5 ≤ p)
    (w w' : Fin (N + 1) → Fin 15) (hww' : w ≠ w')
    (hshare :
      (fun t ↦ MME.DWZSquare.shapeX (w t)) =
          (fun t ↦ MME.DWZSquare.shapeX (w' t)) ∨
        (fun t ↦ MME.DWZSquare.shapeY (w t)) =
          (fun t ↦ MME.DWZSquare.shapeY (w' t))) :
    let I : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeX (w t)).val
    let J : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeY (w t)).val
    let K : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeZ (w t)).val
    let I' : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeX (w' t)).val
    let J' : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeY (w' t)).val
    let K' : Fin (N + 1) → ZMod p := fun t ↦
      (MME.DWZSquare.shapeZ (w' t)).val
    (∀ t, I t + J t + K t = (4 : ZMod p)) ∧
      (∀ t, I' t + J' t + K' t = (4 : ZMod p)) ∧
      ((I = I' ∧ J ≠ J') ∨ (J = J' ∧ I ≠ I')) := by
  sorry
