-- Prove2me | Theorems.Thm_mme_recursive_yz_actual_CW_cell_finite_hole_repair
-- name    : mme_recursive_yz_actual_CW_cell_finite_hole_repair
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T11:05:36.25167+00:00
-- url     : https://prove2.me/theorems/98205de3-b6e9-4971-bd4e-935c8333b2c5
-- title:
--   Finite hole repair for literal CW tensors with physical cell profiles
-- statement:
--   Let $U$ be the actual restriction of $\mathrm{CW}_q^{\otimes L2^{\ell-1}}$ to prescribed grades and exact full fine-word histograms in each physical cell and mode. Let $B_i$ be the finite set of its graded exact-profile fine-word blocks. The restricted tensor has a canonical coordinate basis and its actual fine-label map. If $$\prod_{i=0}^2 |B_i| < d^h,$$ then any $8^h$ copies with hole sets satisfying $$4d|H_{j,i}|\le |B_i|$$ in every mode can be combined by tensor restriction to recover the intact $U$.
--
--   The common shuffle action and its invariance on this literal CW restriction are conclusions of the proof; no tensor-symmetry premise is assumed.
-- source:
--   Finite recursive extraction in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.3--6.5; https://arxiv.org/html/2404.16349v2.

import Definitions.Def_mme_recursive_yz_CW_cells
import Theorems.Thm_mme_recursive_yz_cell_uniform_shuffle
import Theorems.Thm_mme_modern_three_mode_finite_hole_repair
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_strassen_preorder
import Mathlib.LinearAlgebra.Basis.Submodule

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.DWZStep1Support
  MME.DWZComponentRestriction MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.DWZSquare MME.ModernRepair Module
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v w

theorem mme_recursive_yz_actual_CW_cell_finite_hole_repair {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    let S := unbroken K q ell L positions cell shape mu
    let G := grading K q ell L positions cell shape mu
    ∃ B : ∀ i, Basis (Coord.{u} q ell L positions cell shape mu i) K (S.V i),
    ∃ blockLabel : ∀ i, Coord.{u} q ell L positions cell shape mu i → Block ell cell shape mu i,
      (∀ i x, (G.classOf i 0).subtype (B i x) = basis K q ell L i x.val) ∧
      (∀ i x, (blockLabel i x).val = CWCells.label q ell L positions x.val) ∧
      ∀ d h : ℕ,
        (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) < d ^ h →
        ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (Block ell cell shape mu i),
          (∀ j i, 4 * d * (holes j i).card ≤ Nat.card (Block ell cell shape mu i)) →
          Restrict S (bigAdd (fun j ↦ projected S B blockLabel (fun i ↦ Finset.univ \ holes j i)))  := by sorry
