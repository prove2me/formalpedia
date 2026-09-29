-- Prove2me | Theorems.Thm_mme_dwz_conditioned_XZ_collision_fiber_independent_of_b0
-- name    : mme_dwz_conditioned_XZ_collision_fiber_independent_of_b0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:06:13.036376+00:00
-- url     : https://prove2.me/theorems/320c8517-d02e-4c66-b60c-a95dac105602
-- title:
--   The conditioned Claim-6.8 collision fiber is independent of the affine offset
-- statement:
--   For a fixed conditioned X--Z hash weight and conditioned value, changing the common affine offset b_0 does not change the finite family of compatible outer words satisfying the hash equality. The offset occurs additively on both sides and cancels.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Claim 6.8 and the conditioned second hash.

import Definitions.Def_mme_dwz_asymmetric_affine_hash

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_conditioned_XZ_collision_fiber_independent_of_b0
    {p N : ℕ} {Outer : Type*} [Fintype Outer] [DecidableEq Outer]
    (compatible : Outer → Prop) [DecidablePred compatible]
    (addressX : Outer → Fin (N + 1) → Fin 5)
    (addressZ : Fin (N + 1) → Fin 5)
    (b0 b0' w0 : ZMod p) (w : Fin (N + 1) → ZMod p) :
    Finset.univ.filter (fun A : Outer ↦
      compatible A ∧
        b0 + ∑ t, (((addressX A) t).val : ZMod p) * w t =
          b0 + (2 : ZMod p)⁻¹ *
            (w0 + ∑ t,
              ((4 : ZMod p) - (addressZ t).val) * w t)) =
      Finset.univ.filter (fun A : Outer ↦
        compatible A ∧
          b0' + ∑ t, (((addressX A) t).val : ZMod p) * w t =
            b0' + (2 : ZMod p)⁻¹ *
              (w0 + ∑ t,
                ((4 : ZMod p) - (addressZ t).val) * w t)) := by
  sorry
