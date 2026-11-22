-- Prove2me | solution 1 for LinearMap.GeneralLinearGroup.coe_ofLinearEquiv_bruhat2024
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:43:13.542934+00:00
-- url     : https://prove2.me/submissions/ec6bb777-fb8e-43df-8952-625e4d9a8ca2

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra

set_option autoImplicit false

namespace LinearMap.GeneralLinearGroup
theorem _root_.solution {R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] (f : M ≃ₗ[R] M) :
    (LinearMap.GeneralLinearGroup.ofLinearEquiv f).val = f := by
  rfl
end LinearMap.GeneralLinearGroup
