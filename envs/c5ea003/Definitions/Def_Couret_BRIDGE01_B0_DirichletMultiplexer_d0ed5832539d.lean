-- Prove2me | Definitions.Def_Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
-- name    : Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:36.494027+00:00
-- url     : https://prove2.me/theorems/b71683c6-853c-40ca-880c-2906acf0d64a
-- title:
--   Finite Dirichlet Fourier coefficients on U(30)
-- statement:
--   In CouretOaiBridge01, u30FourierCoeff is defined for a commutative ring R, a weight w : U30 → R, and a Dirichlet character χ of modulus 30 with values in R. Its value is the finite sum over units b of w(b) multiplied by χ evaluated at the inverse of the underlying residue b in ZMod 30. The bundle defines this coefficient without any assumption that w is a probability weight or that R is a field; it contains no Fourier inversion theorem.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/BRIDGE01_B0_DirichletMultiplexer.lean; source file SHA-256 f1579856311c26da1ffe23c1bae588a7a5100e3ddc136e2da67d3ac712ccad55

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Definitions.Def_Couret_BRIDGE01_A1_U30KernelInverse_5560f1024274
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic

open scoped BigOperators

namespace CouretOaiBridge01

noncomputable section

/--
Finite Fourier coefficient of a weight on U(30), expressed through Dirichlet characters.
The theorem below is purely finite and algebraic.
-/
def u30FourierCoeff
    {R : Type*} [CommRing R]
    (w : U30 → R) (χ : DirichletCharacter R 30) : R :=
  ∑ b : U30, w b * χ ((b : ZMod 30)⁻¹)



end

end CouretOaiBridge01


