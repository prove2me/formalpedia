-- Prove2me | Definitions.Def_mme_dwz_step1_mixed_fine_callback_predicates
-- name    : mme_dwz_step1_mixed_fine_callback_predicates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-28T10:18:04.749404+00:00
-- url     : https://prove2.me/theorems/2b1a8325-d3fb-472f-93f6-1b5483b97d02
-- title:
--   DWZ Step-1 mixed-owner fine-callback predicates
-- statement:
--   This module names the dependent propositions at the fine-incidence boundary of the common-state mixed-owner argument: survival of the Step-1-filtered singleton, the retained fine-compatibility conclusion associated to a useful Z word, the Claim-6.2 compatibility interface, and the callback consumed by the common-state collision theorem. It introduces no new source maps.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Claims 6.2 and 6.8; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME PiTensorProduct

universe u


set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZGlobalCorrelated

open MME.DWZSourceAligned

/-- The complete Step-1-filtered mixed Z singleton survives. -/
def Step1FilteredMixedSingletonNonzero
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) : Prop :=
  PiTensorProduct.map
      (step1FilteredMixedSingletonMaps K m reindex q edge
        competitor owner W)
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t ≠ 0

/-- The retained fine-compatibility conclusion determined by a useful Z
word. -/
def Step1MixedRetainedFineCompatible
    (m : ℕ) {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (owner competitor : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (hUseful : addressWordUseful m (sourceWord reindex edge owner) W) : Prop :=
  MME.DWZStep2Source.retainedFineCompatible m
    (sourceWord reindex edge)
    (fun t ↦ MME.DWZStep1Support.fineSplitGrade
      ((addressUsefulBlock m
        (sourceWord reindex edge owner) W hUseful).1 t).1
      ((addressUsefulBlock m
        (sourceWord reindex edge owner) W hUseful).1 t).2)
    competitor

/-- The complete logical interface of the fine-compatibility step. -/
def Step1FilteredMixedFineCompatibilityProperty
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) : Prop :=
  ∀ _hSameZ : ∀ r,
      MME.DWZSquare.shapeZ (sourceWord reindex edge owner r) =
        MME.DWZSquare.shapeZ (sourceWord reindex edge competitor r),
    Step1MixedSelectedSupportProperty
        K m reindex q edge competitor owner W →
    ∀ hUseful : addressWordUseful m (sourceWord reindex edge owner) W,
      Step1FilteredMixedSingletonNonzero
          K m reindex q edge competitor owner W →
        Step1MixedRetainedFineCompatible
          m reindex edge owner competitor W hUseful

/-- The exact callback required by the generic common-state mixed-singleton
zero theorem. -/
def Step1FilteredMixedFineCallbackProperty
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) : Prop :=
  Step1MixedSelectedSupportProperty
      K m reindex q edge competitor owner W →
    Step1FilteredMixedRawNonzero
        K m reindex q edge competitor owner W →
      ∀ hUseful : addressWordUseful m (sourceWord reindex edge owner) W,
        Step1MixedRetainedFineCompatible
          m reindex edge owner competitor W hUseful

end MME.DWZGlobalCorrelated


