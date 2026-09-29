-- Prove2me | Theorems.Thm_mme_induced_mode_choice_certificate_descent
-- name    : mme_induced_mode_choice_certificate_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:25:57.621074+00:00
-- url     : https://prove2.me/theorems/af702f4b-a97a-4db6-a938-4a3345924480
-- title:
--   Mode-choice certificates descend through an absorbed tensor projector
-- statement:
--   Let an ambient order-three tensor carry a finite induced mode-choice certificate to a target tensor. Suppose a smaller source maps into the ambient tensor as a modewise projector, and every individual certificate map absorbs that projector. Then the certificate descends to the smaller source. In formulas, if the inclusion maps send the smaller source tensor to the projected ambient tensor and each slot map satisfies $f_{i,j}P_i=f_{i,j}$, then precomposition with the inclusions gives a certificate with the same retained choices and the same target. This is the generic algebraic step needed to descend induced-family extractions through allowed-word projections.
-- source:
--   Elementary functoriality and multilinearity of tensor products; projector descent in the laser method.

import Definitions.Def_mme_induced_mode_choice_certificate

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false

theorem mme_induced_mode_choice_certificate_descent
    {K : Type u} [Field K]
    {source ambient target : TensorObj K 3}
    (cert : InducedModeChoiceCertificate ambient target)
    (inclusion : ∀ i : Fin 3, source.V i →ₗ[K] ambient.V i)
    (project : ∀ i : Fin 3, ambient.V i →ₗ[K] ambient.V i)
    (hinclude : PiTensorProduct.map inclusion source.t =
      PiTensorProduct.map project ambient.t)
    (habsorb : ∀ (i : Fin 3) (slot : Fin (cert.slotCount i)),
      (cert.modeMap i slot).comp (project i) = cert.modeMap i slot) :
    Nonempty (InducedModeChoiceCertificate source target) := by
  sorry
