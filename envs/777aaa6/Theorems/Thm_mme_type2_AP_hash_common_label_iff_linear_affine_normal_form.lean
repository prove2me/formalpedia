-- Prove2me | Theorems.Thm_mme_type2_AP_hash_common_label_iff_linear_affine_normal_form
-- name    : mme_type2_AP_hash_common_label_iff_linear_affine_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:09:19.57929+00:00
-- url     : https://prove2.me/theorems/43c5c5f8-bf8f-4f8c-adf0-7b3f983cb368
-- title:
--   Linear-affine normal form for common-label AP hashing
-- statement:
--   Let $(H_0,H_1,H_2)$ be a hash triple in a commutative ring satisfying $H_0+H_1=2H_2$, and let $S$ be a finite label set. The three hashes equal one common allowed label if and only if $$H_0\in\operatorname{image}(S),\qquad H_2=H_0.$$ The progression identity then forces $H_1=H_0$. This converts type-2 retention into the linear-membership plus affine-graph form needed for exact hash-state counting.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356-360; affine Salem--Spencer hash normal form.

import Mathlib

set_option autoImplicit false

theorem mme_type2_AP_hash_common_label_iff_linear_affine_normal_form
    {R Label : Type*} [CommRing R] [DecidableEq R] [DecidableEq Label]
    (S : Finset Label) (label : Label → R) (H : Fin 3 → R)
    (hAP : H 0 + H 1 = 2 * H 2) :
    (∃ s ∈ S, ∀ i : Fin 3, H i = label s) ↔ H 0 ∈ S.image label ∧ H 2 = H 0 := by
  sorry
