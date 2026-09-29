-- Prove2me | Theorems.Thm_mme_HasSixSymmetricTauValueAtLeast_of_powered_cyclic_source_restrict
-- name    : mme_HasSixSymmetricTauValueAtLeast_of_powered_cyclic_source_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:09:02.705226+00:00
-- url     : https://prove2.me/theorems/73683fbd-1b90-46ef-ae75-0262cc4aa868
-- title:
--   Powered cyclic sources realize six-symmetrized target values
-- statement:
--   Let a source tensor have ordinary tau-value at least W cubed for every strict sub-endpoint W. If its positive N-th Kronecker power restricts both to the cyclic symmetrization of a target tensor and to the first-two-mode swap of that cyclic symmetrization, then the target has six-symmetrized tau-value at least the N-th power of every nonnegative strict sub-endpoint. This isolates the exact linear realization needed to turn cyclic component witnesses into the six-symmetric values used in DWZ Equation (25).
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.3 and the component-value assembly used in Equation (25); https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_finite_kronFin_HasTauValueAtLeast_product_below
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators

set_option autoImplicit false

universe u

theorem mme_HasSixSymmetricTauValueAtLeast_of_powered_cyclic_source_restrict
    {K : Type u} [Field K]
    (source targetObj : TensorObj K 3) (tau endpoint target : ℝ)
    (N : ℕ)
    (hN : 0 < N)
    (hendpoint : 0 < endpoint) (htarget : 0 ≤ target)
    (hstrict : target < endpoint)
    (hsource : ∀ W : ℝ, 0 ≤ W → W < endpoint →
      HasTauValueAtLeast source tau (W ^ (3 : ℕ)))
    (hleft : TensorObj.Restrict (source.kronPow N)
      (cyclicSymmetrization targetObj))
    (hright : TensorObj.Restrict (source.kronPow N)
      (TensorObj.permObj swapFirstTwoPerm
        (cyclicSymmetrization targetObj))) :
    HasSixSymmetricTauValueAtLeast targetObj tau (target ^ N) := by
  sorry
