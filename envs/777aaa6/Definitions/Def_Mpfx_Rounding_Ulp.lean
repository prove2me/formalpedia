-- Prove2me | Definitions.Def_Mpfx_Rounding_Ulp
-- name    : Mpfx_Rounding_Ulp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:44:55.785029+00:00
-- url     : https://prove2.me/theorems/c67105dc-9299-41a9-a19a-b88310e26209
-- title:
--   Ulp
-- statement:
--   Definitions and structural lemmas for Ulp, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
namespace Mpfx
noncomputable def ulp (F : FiniteFormat) (x : ℝ) : ℝ :=
  if x = 0 ∧ F.exp = ⊥ then 0 else (2 : ℝ) ^ F.canonicalExp x
noncomputable def rndDown (F : FiniteFormat) (x : ℝ) : Dyadic :=
  Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x)
noncomputable def midp (F : FiniteFormat) (x : ℝ) : ℝ :=
  (rndDown F x : ℝ) + ulp F x / 2
noncomputable def rndUp (F : FiniteFormat) (x : ℝ) : Dyadic :=
  Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x)
end Mpfx


