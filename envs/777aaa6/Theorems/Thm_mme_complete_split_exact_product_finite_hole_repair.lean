-- Prove2me | Theorems.Thm_mme_complete_split_exact_product_finite_hole_repair
-- name    : mme_complete_split_exact_product_finite_hole_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:33:42.14567+00:00
-- url     : https://prove2.me/theorems/c8793468-9887-4370-bde8-558b9b66b0a6
-- title:
--   Exact multi-term complete-profile tensor repair from joint tuple holes
-- statement:
--   Let $S$ be the ordered tensor product of a finite family of tensor powers, each restricted to prescribed exact complete profiles over a field. Use the inherited coordinate bases and literal full-word label maps. Write $B_i$ for the joint label set in mode $i$: a label is a tuple of full-word labels across all factors.
--
--   For natural numbers $d,h$, and arbitrary deleted label sets $Q_{a,i}\subseteq B_i$ in each of $8^h$ copies, suppose
--
--   $$\prod_{i=1}^3|B_i|<d^h,\qquad
--   4d\,|Q_{a,i}|\le |B_i|\quad\text{for every }a,i.$$
--
--   Then the literal tensor $S$ restricts from the direct sum of those individually holed copies. Each copy is the actual coordinate projection onto $B_i\setminus Q_{a,i}$ in every mode. The holes may be correlated across factors; no factorization into per-term holes is required.
--
--   The coordinate bases and label maps retain their ambient power-basis and ordered-word identities. No tensor symmetry or repair conclusion is assumed. Empty factor families, zero powers, and empty exact-type sets are allowed. This finite repair theorem does not assert a source-selection estimate or a matrix multiplication exponent.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definition 4.1 (p.15) and Theorem 4.2 (p.18), https://arxiv.org/abs/2404.16349v2. Underlying three-mode repair: Vassilevska Williams et al., New Bounds for Matrix Multiplication: from Alpha to Omega, arXiv:2307.07970v2, Property 7.1 and Theorem 7.2, https://arxiv.org/abs/2307.07970v2. The 8^h budget is the checked product-cardinality induction variant; its asymptotic accounting is a separate result.

import Theorems.Thm_mme_complete_split_exact_restrictedPower_uniform_basis_interface
import Theorems.Thm_mme_modern_three_mode_finite_hole_repair
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_modern_three_mode_projected_tensor
import Definitions.Def_mme_tensor_quotient
import Mathlib.Data.Fintype.BigOperators

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.DWZSquare MME.ModernRepair PiTensorProduct Module
open scoped BigOperators Classical

universe u v w

set_option autoImplicit false

theorem mme_complete_split_exact_product_finite_hole_repair
    {K : Type u} [Field K] {r : ℕ}
    (T : Fin r → TensorObj K 3) {I : Fin r → Fin 3 → Type u}
    (b : ∀ t i, Basis (I t i) K ((T t).V i)) {ell : ℕ}
    (label : ∀ t i, I t i → CompleteWord ell)
    (n : Fin r → ℕ) (beta : Fin r → Fin 3 → Profile ell) :
    let Coord := fun t i ↦
      {w : PowIndex (I t i) (n t) // ApproxConsistent (label t i) (beta t i) 0 w}
    let Block := fun t i ↦
      {w : PowIndex (CompleteWord ell) (n t) // ApproxConsistent id (beta t i) 0 w}
    let Term := fun t ↦ restrictedPower (T t) (b t) (label t) (beta t) 0 (n t)
    let G := fun t ↦ ((T t).kronPow (n t)).basisAllAllowedGrading
      (fun i ↦ kronPowModeBasis (T t) i (b t i) (n t))
      (fun i ↦ ApproxConsistent (label t i) (beta t i) 0)
    let S := TensorObj.kronFin r Term
    ∃ B : ∀ t i, Basis (Coord t i) K ((Term t).V i),
    ∃ blockLabel : ∀ t i, Coord t i → Block t i,
      (∀ t i w, ((G t).classOf i 0).subtype (B t i w) =
        kronPowModeBasis (T t) i (b t i) (n t) w.1) ∧
      (∀ t i w, (blockLabel t i w).1 =
        PowIndex.ofFun (n t) (fun j ↦ label t i (PowIndex.get (n t) w.1 j))) ∧
      ∀ d h : ℕ,
        (∏ i : Fin 3, Fintype.card (∀ t : Fin r, Block t i)) < d ^ h →
        ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (∀ t : Fin r, Block t i),
          (∀ a i, 4 * d * (holes a i).card ≤
            Fintype.card (∀ t : Fin r, Block t i)) →
          TensorObj.Restrict S
            (TensorObj.bigAdd (fun a ↦ projected S
              (fun i ↦ kronFinModePiBasis r Term i (fun t ↦ B t i))
              (fun i w t ↦ blockLabel t i (w t))
              (fun i ↦ Finset.univ \ holes a i))) := by sorry
