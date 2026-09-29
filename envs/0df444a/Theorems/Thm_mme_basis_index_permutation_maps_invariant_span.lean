-- Prove2me | Theorems.Thm_mme_basis_index_permutation_maps_invariant_span
-- name    : mme_basis_index_permutation_maps_invariant_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:25:51.769287+00:00
-- url     : https://prove2.me/theorems/e35aef63-9437-467f-908b-224adc554a1d
-- title:
--   A basis permutation preserves the span of an invariant selection
-- statement:
--   Let $b=(b_i)_{i\in I}$ be a basis and let $e$ permute its indices. If a selection predicate $A\subseteq I$ is invariant under $e$, then the induced linear automorphism $b_i\mapsto b_{e(i)}$ preserves exactly the subspace spanned by the selected basis vectors:
--
--   $$
--   e\bigl(\operatorname{span}\{b_i:i\in A\}\bigr)=\operatorname{span}\{b_i:i\in A\}.
--   $$
--
--   Applied to the available-word predicate, this is the linear-subspace step that lets a DWZ standard-form shuffle act on the projected $Z$ mode rather than only on the unrestricted component power.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claims 5.8--5.9, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_basis_index_permutation

open Module

universe u

set_option autoImplicit false

theorem mme_basis_index_permutation_maps_invariant_span
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι : Type u} (b : Basis ι K V) (e : ι ≃ ι)
    (allowed : ι → Prop)
    (hinv : ∀ j, allowed (e j) ↔ allowed j) :
    Submodule.map
        (MME.DWZComponentRestriction.basisIndexPermEquiv b e).toLinearMap
        (Submodule.span K (b '' {j | allowed j})) =
      Submodule.span K (b '' {j | allowed j}) := by
  sorry
