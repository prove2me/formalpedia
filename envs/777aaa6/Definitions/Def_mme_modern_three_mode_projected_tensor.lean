-- Prove2me | Definitions.Def_mme_modern_three_mode_projected_tensor
-- name    : mme_modern_three_mode_projected_tensor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-07T04:47:14.524347+00:00
-- url     : https://prove2.me/theorems/54128031-12f1-44c8-b4e5-c3c13fd55b6d
-- title:
--   Ambient three-mode basis-label projection
-- statement:
--   Let $T$ be a three-mode tensor over a field, let $b_i$ be a basis in mode $i$, and give each basis coordinate a label $\ell_i$. For finite retained-label sets $R_i$, let $p_{i,R_i}$ fix a basis vector when its label belongs to $R_i$ and send it to zero otherwise. Define the ambient projection
--
--   $$T[R]=(p_{0,R_0}\otimes p_{1,R_1}\otimes p_{2,R_2})(T).$$
--
--   The original mode spaces are retained, so projected tensors can be added literally in the same ambient tensor space. This is the zero-extended form of simultaneous basis-coordinate restriction. The definition imposes no extraction, symmetry, support, nonemptiness, or value hypothesis.
-- source:
--   Generic ambient-coordinate realization for Vassilevska Williams et al., New Bounds for Matrix Multiplication: from Alpha to Omega, arXiv:2307.07970v2, Theorem7.2 and its eight-box repair proof in Section7 (https://arxiv.org/abs/2307.07970v2). This is the three-mode repair used by Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Theorem4.2 (https://arxiv.org/abs/2404.16349v2). Reuses the existing public basisLabelProjection definition; no repair or symmetry theorem is bundled into the data.

import Definitions.Def_mme_dwz_basis_label_projection

open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u v

set_option autoImplicit false
set_option warningAsError true

namespace MME.ModernRepair

noncomputable def projected
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, DecidableEq (Label i)]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (label : (i : Fin 3) → ι i → Label i)
    (R : (i : Fin 3) → Finset (Label i)) : TensorObj K 3 :=
  { V := T.V
    acg := T.acg
    mod := T.mod
    fin := T.fin
    t := PiTensorProduct.map
      (fun i ↦ basisLabelProjection (b i) (label i) (R i)) T.t }

end MME.ModernRepair


