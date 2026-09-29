-- Prove2me | Theorems.Thm_mme_dwz_common_state_surviving_word_value_eq_zero_of_competitor
-- name    : mme_dwz_common_state_surviving_word_value_eq_zero_of_competitor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:43:56.145618+00:00
-- url     : https://prove2.me/theorems/719eb7df-28d4-4741-bed3-52411c7ff8ef
-- title:
--   A common-state surviving word kills a distinct compatible owner
-- statement:
--   Fix one owner in the globally correlated common-state construction and a canonical Z-basis word retained by that owner's broken copy. Let x be any value. If nonvanishing of x would make a distinct competitor compatible with the retained useful word at the same common affine state, then x is zero.

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME
open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

universe u v

set_option autoImplicit false

theorem mme_dwz_common_state_surviving_word_value_eq_zero_of_competitor
    {V : Type v} [Zero V]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (owner competitor : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : V)
    (hSurvives : addressWordSurvives m
      (sourceWord reindex edge owner)
      (commonStateBrokenCopy m reindex q edge owner) W)
    (hne : competitor ≠ owner)
    (hCompatible : x ≠ 0 →
      ∀ hUseful : addressWordUseful m
          (sourceWord reindex edge owner) W,
        ownerCompatible m reindex q edge owner
          (addressUsefulBlock m (sourceWord reindex edge owner) W hUseful)
          competitor) :
    x = 0 := by
  sorry
