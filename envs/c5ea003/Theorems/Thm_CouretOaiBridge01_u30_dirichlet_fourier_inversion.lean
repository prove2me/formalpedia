-- Prove2me | Theorems.Thm_CouretOaiBridge01_u30_dirichlet_fourier_inversion
-- name    : CouretOaiBridge01.u30_dirichlet_fourier_inversion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:46:43.031846+00:00
-- url     : https://prove2.me/theorems/85c2c720-6ab3-41aa-a83a-2f8435e8c27d
-- title:
--   Finite Dirichlet inversion on units modulo thirty
-- statement:
--   Let U be the units of Z/30, and R a commutative integral domain with enough roots of unity for the exponent of U. For w:U→R define $\widehat w(\chi)=\sum_{b\in U}w(b)\chi(b^{-1})$. For every a in U, $$\varphi(30)w(a)=\sum_{\chi\bmod30}\widehat w(\chi)\chi(a).$$ The totient is cast into R; no division by it is asserted.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/BRIDGE01_B0_DirichletMultiplexer.lean#L20-L65, lines 20–65; source file SHA-256 f1579856311c26da1ffe23c1bae588a7a5100e3ddc136e2da67d3ac712ccad55; theorem CouretOaiBridge01.u30_dirichlet_fourier_inversion

import Definitions.Def_Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
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

theorem u30_dirichlet_fourier_inversion
    {R : Type*} [CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent U30)]
    (w : U30 → R) (a : U30) :
    ((30 : ℕ).totient : R) * w a =
      ∑ χ : DirichletCharacter R 30, u30FourierCoeff w χ * χ (a : ZMod 30) := by sorry


end

end CouretOaiBridge01
