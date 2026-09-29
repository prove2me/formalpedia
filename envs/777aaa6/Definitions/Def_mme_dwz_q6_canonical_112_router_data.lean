-- Prove2me | Definitions.Def_mme_dwz_q6_canonical_112_router_data
-- name    : mme_dwz_q6_canonical_112_router_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T06:24:46.8998+00:00
-- url     : https://prove2.me/theorems/eae96300-b1f0-4270-96bf-2ca634f80666
-- title:
--   Basis labels for the canonical q=6 row-112 coupled router
-- statement:
--   For the canonical 112 block of the square of the Coppersmith--Winograd tensor, this package names the coordinate set of the four-sum coupled constituent, the exact canonical CW-square basis pair representing each coordinate, and its standard coordinate vector in the coupled constituent. The mode-two labels separate the two exceptional boundary pairs from the q by q middle grid. These are the basis labels needed to state the enhanced-112 source router and its shared-Z profile compatibility without hiding the coordinate action behind a quotient isomorphism.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and the enhanced 112 analysis in Section 6.3; the coupled constituent is the four-sum constituent of Coppersmith--Winograd (1990), journal pp. 266 and 270. https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_CW_coupled_value

namespace MME

universe u

set_option autoImplicit false

/-- Coordinate labels of the coupled constituent corresponding to the
canonical `112` block of the CW square. -/
def DWZCanonical112Coord (q : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin q ⊕ Fin q
  | ⟨1, _⟩ => Fin q ⊕ Fin q
  | ⟨2, _⟩ => Fin 2 ⊕ (Fin q × Fin q)

/-- The literal CW-square basis pair carrying a coupled `112` coordinate. -/
def dwzCanonical112Pair (q : ℕ) :
    ∀ s : Fin 3, DWZCanonical112Coord q s →
      Fin (q + 2) × Fin (q + 2)
  | ⟨0, _⟩, Sum.inl i =>
      (⟨0, by omega⟩, ⟨i.val + 1, by omega⟩)
  | ⟨0, _⟩, Sum.inr i =>
      (⟨i.val + 1, by omega⟩, ⟨0, by omega⟩)
  | ⟨1, _⟩, Sum.inl i =>
      (⟨0, by omega⟩, ⟨i.val + 1, by omega⟩)
  | ⟨1, _⟩, Sum.inr i =>
      (⟨i.val + 1, by omega⟩, ⟨0, by omega⟩)
  | ⟨2, _⟩, Sum.inl a =>
      if a = 0 then
        (⟨q + 1, by omega⟩, ⟨0, by omega⟩)
      else
        (⟨0, by omega⟩, ⟨q + 1, by omega⟩)
  | ⟨2, _⟩, Sum.inr ij =>
      (⟨ij.2.val + 1, by omega⟩, ⟨ij.1.val + 1, by omega⟩)

/-- The corresponding standard coordinate vector in the explicit coupled
constituent. -/
noncomputable def dwzCanonical112Vec
    (K : Type u) [Field K] (q : ℕ) :
    ∀ s : Fin 3, DWZCanonical112Coord q s → CoupledSpace K q s
  | ⟨0, _⟩, c => Pi.single c 1
  | ⟨1, _⟩, c => Pi.single c 1
  | ⟨2, _⟩, c => Pi.single c 1

end MME


