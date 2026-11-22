-- Prove2me | solution 1 for Submodule.quotient_equiv_eq_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:47:23.00884+00:00
-- url     : https://prove2.me/submissions/68a52762-1aed-40a1-8dee-33919e5c6ee5

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra

set_option autoImplicit false
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
namespace Submodule
theorem _root_.solution (p : Submodule R M)
    (p' : { p' : Submodule R M // p ≤ p' }) :
    p' = ⊥ ↔ p'.val = p := by
  show p' = ⟨p, le_rfl⟩ ↔ p'.val = p
  apply Subtype.ext_iff
end Submodule
