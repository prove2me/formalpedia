-- Prove2me | Theorems.Thm_mme_regional_copied_restrictions_product
-- name    : mme_regional_copied_restrictions_product
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T15:12:13.938336+00:00
-- url     : https://prove2.me/theorems/849e159c-2a9c-4888-94a2-5299c351aeac
-- title:
--   Regional extraction multiplies every input and output count
-- statement:
--   If the tensor product of sources $S_j$ restricts from $S$, and $r_j$ copies of $S_j$ yield $c_j$ copies of the matrix tensor $\langle a_j,b_j,d_j\rangle$, then
--
--   $$\bigoplus_{\prod_j c_j}\left\langle\prod_j a_j,\prod_j b_j,\prod_j d_j\right\rangle\ \le\ \bigoplus_{\prod_j r_j}S.$$
--
--   Both the output gain and the cost of independent source copies are retained exactly, including zero counts and an empty region family.
-- source:
--   Constructive tensor-algebra components for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3 and Theorem 6.4. These lemmas implement the finite operations; they do not assert the numerical witness.

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_rank_bridge
open BigOperators MME MME.TensorObj
universe u
set_option autoImplicit false

theorem mme_regional_copied_restrictions_product {K : Type u} [Field K] {k : ℕ}
    (source : TensorObj K 3) (S : Fin k → TensorObj K 3)
    (a b c inputs outputs : Fin k → ℕ)
    (hgroup : Restrict (kronFin k S) source)
    (h : ∀ j, Restrict (bigAdd (fun _ : Fin (outputs j) ↦ MMObj K (a j) (b j) (c j)))
      (bigAdd (fun _ : Fin (inputs j) ↦ S j))) :
    Restrict (bigAdd (fun _ : Fin (∏ j, outputs j) ↦ MMObj K (∏ j, a j) (∏ j, b j) (∏ j, c j)))
      (bigAdd (fun _ : Fin (∏ j, inputs j) ↦ source)) := by sorry
