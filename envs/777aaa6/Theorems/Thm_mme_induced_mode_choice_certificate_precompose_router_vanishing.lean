-- Prove2me | Theorems.Thm_mme_induced_mode_choice_certificate_precompose_router_vanishing
-- name    : mme_induced_mode_choice_certificate_precompose_router_vanishing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:54:26.060517+00:00
-- url     : https://prove2.me/theorems/2dc83d1b-7ba9-4dbf-b46d-367e37756f43
-- title:
--   Exact source-router pullback preserves mode-choice vanishing
-- statement:
--   Let a family of modewise linear maps route a source tensor exactly to an intermediate tensor. Any induced mode-choice certificate from the intermediate tensor can be pulled back to the source by precomposing every slot map with the router. Moreover, if every third-mode slot annihilates the routed image of a specified class of named source vectors, then the pulled-back certificate annihilates those source vectors themselves.
--
--   This packages the functorial step used after a basis-labelled laser-method source router while retaining the pointwise forbidden-word equations needed for later projector descent.
-- source:
--   Functoriality of tensor restriction and induced finite mode-choice zeroing; elementary multilinear algebra.

import Definitions.Def_mme_induced_mode_choice_certificate

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_induced_mode_choice_certificate_precompose_router_vanishing
    {K : Type u} [Field K]
    {source middle target : TensorObj K 3}
    (router : ∀ i : Fin 3, source.V i →ₗ[K] middle.V i)
    (hrouter : PiTensorProduct.map router source.t = middle.t)
    (cert : InducedModeChoiceCertificate middle target)
    {alpha : Type u} (basisVector : alpha → source.V 2)
    (bad : alpha → Prop)
    (hvanish : ∀ (slot : Fin (cert.slotCount 2)) (a : alpha),
      bad a → cert.modeMap 2 slot (router 2 (basisVector a)) = 0) :
    ∃ pulled : InducedModeChoiceCertificate source target,
      ∀ (slot : Fin (pulled.slotCount 2)) (a : alpha),
        bad a → pulled.modeMap 2 slot (basisVector a) = 0 := by
  sorry
