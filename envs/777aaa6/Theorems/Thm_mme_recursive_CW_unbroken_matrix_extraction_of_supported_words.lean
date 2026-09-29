-- Prove2me | Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_supported_words
-- name    : mme_recursive_CW_unbroken_matrix_extraction_of_supported_words
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:08:26.366015+00:00
-- url     : https://prove2.me/theorems/6a433a4e-8084-4b47-9218-38931f97c988
-- title:
--   Matrix extraction inside an intact block from jointly supported profile words
-- statement:
--   Consider an intact cell-profile block of $\mathrm{CW}_5^{\otimes L2^{\ell-1}}$ over a field $K$, with finite child positions, prescribed cell grades, and complete-word histograms $\mu_i$. Suppose assignments $w_i$ realize those histograms, have the prescribed grades in every cell, and satisfy
--
--   $$w_0(p,r)+w_1(p,r)+w_2(p,r)=2$$
--
--   at every child position $p$ and elementary position $r$. Let $n_{ij}$ count elementary positions where both mode-$i$ and mode-$j$ entries equal one. Then the literal intact block admits the restriction
--
--   $$\langle5^{n_{02}},5^{n_{01}},5^{n_{12}}\rangle_K\ \preceq\ T_{\mathrm{intact}}.$$
--
--   This applies at every recursive level and to interior as well as boundary cells. Its hypothesis is simultaneous support of the three histogram realizations; separate nonemptiness of the three mode blocks does not supply that hypothesis.
-- source:
--   Singleton elementary boundary profiles and exact profiled CW boundary termination; flattening/splitting identifies the literal intact block.

import Theorems.Thm_mme_recursive_profiled_CW_boundary_end

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.Boundary MME.ProfiledCW

theorem mme_recursive_CW_unbroken_matrix_extraction_of_supported_words
    {K : Type*} [Field K] {P C : Type} [Fintype P] {ell L : ℕ}
    (positions : Fin L ≃ P) (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (w : Fin 3 → P → CompleteWord ell)
    (hgrade : ∀ i p, CWCells.grade (w i p) = shape (cell p) i)
    (hmu : ∀ i, Useful cell (mu i) (w i))
    (hs : ∀ p r, (w 0 p r).val + (w 1 p r).val + (w 2 p r).val = 2) :
    let x := fun i ↦ flatten positions rfl (w i)
    Restrict (MMObj K
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 2 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 0 r).val = 1 ∧ (x 1 r).val = 1)).card)
      (5 ^ (Finset.univ.filter (fun r ↦ (x 1 r).val = 1 ∧ (x 2 r).val = 1)).card))
      (CWCells.unbroken K 5 ell L positions cell shape mu) := by sorry
