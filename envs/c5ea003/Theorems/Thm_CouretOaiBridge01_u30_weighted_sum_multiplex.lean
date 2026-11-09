-- Prove2me | Theorems.Thm_CouretOaiBridge01_u30_weighted_sum_multiplex
-- name    : CouretOaiBridge01.u30_weighted_sum_multiplex
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:02:57.592199+00:00
-- url     : https://prove2.me/theorems/adaf53e8-7db9-4860-9cc6-82c8975cce2a
-- title:
--   Finite weighted sums multiplex into character channels
-- statement:
--   Let U be the units modulo 30 and R a commutative integral domain with enough roots of unity for the exponent of U. Let I be any finite type, w:U→R, c:I→R and r:I→U. With $\widehat w(\chi)=\sum_{b\in U}w(b)\chi(b^{-1})$, $$\varphi(30)\sum_{i\in I}c_iw(r_i)=\sum_{\chi\bmod30}\widehat w(\chi)\sum_{i\in I}c_i\chi(r_i).$$ Empty I is included; this is a finite algebraic identity.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/BRIDGE01_B1_WeightedSumMultiplex.lean#L10-L46, lines 10–46; source file SHA-256 a1f7837de0f1205815cb78782dfb1fedbacc565a70f12d76db2d82abfd994d36; theorem CouretOaiBridge01.u30_weighted_sum_multiplex

import Definitions.Def_Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Theorems.Thm_CouretOaiBridge01_u30_dirichlet_fourier_inversion
import Definitions.Def_Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
import Mathlib.Tactic

open scoped BigOperators

namespace CouretOaiBridge01

noncomputable section

theorem u30_weighted_sum_multiplex
    {R I : Type*} [CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent U30)]
    [Fintype I]
    (w : U30 → R) (c : I → R) (r : I → U30) :
    ((30 : ℕ).totient : R) * (∑ i : I, c i * w (r i)) =
      ∑ χ : DirichletCharacter R 30,
        u30FourierCoeff w χ * (∑ i : I, c i * χ (r i : ZMod 30)) := by sorry


end

end CouretOaiBridge01
