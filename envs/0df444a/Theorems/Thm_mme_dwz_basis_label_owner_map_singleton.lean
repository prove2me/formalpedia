-- Prove2me | Theorems.Thm_mme_dwz_basis_label_owner_map_singleton
-- name    : mme_dwz_basis_label_owner_map_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:18:36.661683+00:00
-- url     : https://prove2.me/theorems/269fde55-8044-427c-88e6-ca811915ce3f
-- title:
--   An owner-selecting Z projection keeps exactly its labelled tensor block
-- statement:
--   Let a three-mode tensor have a labelled basis in its Z mode. For a block label b and an owner t, first restrict Z to the singleton label b, and then restrict Z to all labels owned by t, while acting identically on X and Y. The composite obeys the exact tensor identity $$P_t\bigl(P_{\{b\}}(T)\bigr)=\begin{cases}P_{\{b\}}(T),&t=\operatorname{owner}(b),\\0,&t\ne\operatorname{owner}(b).\end{cases}$$ This is a literal variable-zeroing equation. It provides the owner-selection map needed by the DWZ Hole Lemma repair without replacing a tensor restriction by a count of surviving labels.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 5 (Hole Lemma), especially Definition 5.4 and the standard-copy repair step; combined with the useful-block labels of Definition 6.3 (PDF pp.47 and 53 / printed pp.46 and 52).

import Definitions.Def_mme_dwz_basis_label_projection

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_basis_label_owner_map_singleton
    {K : Type u} [Field K] (X : TensorObj K 3)
    {ι β : Type*} [Fintype β] [DecidableEq β]
    (b : Basis ι K (X.V 2)) (label : ι → β) {s : ℕ}
    (owner : β → Fin s) (t : Fin s) (block : β) :
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (basisLabelProjection b label
            (Finset.univ.filter (fun b ↦ t = owner b))))
        (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label {block})) X.t) =
      if t = owner block then
        PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label {block})) X.t
      else 0 := by
  sorry
