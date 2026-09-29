-- Prove2me | Theorems.Thm_mme_induced_mode_choice_certificate_basisZAllowed_descent
-- name    : mme_induced_mode_choice_certificate_basisZAllowed_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:21:47.155024+00:00
-- url     : https://prove2.me/theorems/ad464488-d449-4046-8a2f-4cb449a8560d
-- title:
--   Mode-choice certificates descend through an allowed Z-basis projection
-- statement:
--   Let $T$ and $A$ be order-three tensors over a field, and fix a basis of the third mode of $T$ together with a predicate selecting allowed basis vectors. Suppose a finite mode-choice certificate realizes $A$ from $T$, and every individual third-mode map in the certificate annihilates every forbidden basis vector. Then the same target has a finite mode-choice certificate whose source is the Z-projected subtensor of $T$ spanned by the allowed basis vectors.
--
--   This is the exact source-projection descent needed when a laser-method component retains only words with a prescribed histogram. It preserves the certificate's retained choices and off-support equations; it makes no counting or asymptotic assumption.
-- source:
--   Elementary multilinearity and basis projection; source-projection step in laser-method tensor restrictions.

import Mathlib.Tactic
import Definitions.Def_mme_induced_mode_choice_certificate
import Definitions.Def_mme_basis_z_allowed_projection
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor

open MME Module PiTensorProduct BigOperators

universe u

set_option autoImplicit false

theorem mme_induced_mode_choice_certificate_basisZAllowed_descent
    {K : Type u} [Field K]
    {T A : TensorObj K 3} {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed]
    (cert : InducedModeChoiceCertificate T A)
    (hvanish : ∀ (slot : Fin (cert.slotCount 2)) (j : ι),
      ¬ allowed j → cert.modeMap 2 slot (bZ j) = 0) :
    Nonempty (InducedModeChoiceCertificate
      (T.basisZAllowedSubtensor bZ allowed) A) := by
  sorry
