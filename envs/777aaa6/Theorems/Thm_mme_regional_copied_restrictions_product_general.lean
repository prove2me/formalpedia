-- Prove2me | Theorems.Thm_mme_regional_copied_restrictions_product_general
-- name    : mme_regional_copied_restrictions_product_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T00:50:43.585096+00:00
-- url     : https://prove2.me/theorems/335682cd-8e66-4ee5-8849-da5b44913cd5
-- title:
--   Product of per-part copy extractions with arbitrary outputs
-- statement:
--   Let $S_1,\dots,S_k$ and $U_1,\dots,U_k$ be 3-tensors, and let a source tensor restrict to the Kronecker product $\bigotimes_j S_j$. Suppose that for every $j$, $\mathrm{outputs}_j$ copies of $U_j$ are a restriction of $\mathrm{inputs}_j$ copies of $S_j$.
--
--   Then $\prod_j \mathrm{outputs}_j$ copies of $\bigotimes_j U_j$ are a restriction of $\prod_j \mathrm{inputs}_j$ copies of the source.
--
--   This generalizes the regional copied-restriction product, whose outputs are matrix-multiplication tensors, to arbitrary output tensors.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_rank_bridge
open BigOperators MME MME.TensorObj
set_option autoImplicit false
universe u

theorem mme_regional_copied_restrictions_product_general {K : Type u} [Field K] {k : ℕ}
    (source : TensorObj K 3) (S U : Fin k → TensorObj K 3) (inputs outputs : Fin k → ℕ)
    (hgroup : TensorObj.Restrict (kronFin k S) source)
    (h : ∀ j, TensorObj.Restrict (bigAdd (fun _ : Fin (outputs j) ↦ U j))
      (bigAdd (fun _ : Fin (inputs j) ↦ S j))) :
    TensorObj.Restrict (bigAdd (fun _ : Fin (∏ j, outputs j) ↦ kronFin k U))
      (bigAdd (fun _ : Fin (∏ j, inputs j) ↦ source)) := by sorry
