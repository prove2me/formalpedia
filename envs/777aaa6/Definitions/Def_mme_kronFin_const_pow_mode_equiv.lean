-- Prove2me | Definitions.Def_mme_kronFin_const_pow_mode_equiv
-- name    : mme_kronFin_const_pow_mode_equiv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T07:32:58.154463+00:00
-- url     : https://prove2.me/theorems/d316e2b9-15df-4352-a1cd-42c1fbe87b98
-- title:
--   Canonical mode equivalence from constant Kronecker families to powers
-- statement:
--   For every tensor T and integer n ≥ 0, the ordered head-recursive Kronecker product of the constant family (T,…,T) and the recursively defined power T^{⊗n} have canonically equivalent mode spaces. The equivalence follows the same recursive tensor-product tree on both sides. It is the coordinate interface needed to identify consecutive Table-2 fibers with the component powers used in the DWZ standard tensor.
-- source:
--   Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6 and Table 2; recursive tensor-power regrouping infrastructure for the Prove2Me 2.3747 mission.

import Definitions.Def_mme_CW_2376_address_block

open MME TensorProduct

universe u

set_option autoImplicit false

namespace MME.TensorObj

/-- The modewise recursive identification of an ordered constant Kronecker
family with the corresponding tensor power. -/
noncomputable def kronFinConstPowModeEquiv
    {K : Type u} [Field K] {d : ℕ} (T : TensorObj K d) (i : Fin d) :
    ∀ n : ℕ,
      (TensorObj.kronFin n (fun _ ↦ T)).V i ≃ₗ[K]
        (T.kronPow n).V i
  | 0 => LinearEquiv.refl K K
  | n + 1 => TensorProduct.congr (LinearEquiv.refl K (T.V i))
      (kronFinConstPowModeEquiv T i n)

end MME.TensorObj


