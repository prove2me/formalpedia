-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_modulus_coprime_monomial
-- name    : Couret.InterIA.Fibres.modulus_coprime_monomial
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:59:41.05146+00:00
-- url     : https://prove2.me/theorems/2aab4fd3-4c4e-4c13-8365-869214f41a99
-- title:
--   A negacyclic modulus is coprime to a nonzero monomial
-- statement:
--   For natural $m>0$, $i\ge0$, and nonzero real $a$, $$\gcd(X^m+1,aX^i)=1$$ in $\mathbb R[X]$, in the sense of polynomial coprimality. The monomial may be constant.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/NegacyclicBinomial.lean, lines 96–112; source file SHA-256 588e3d124d25fde2fdb187a567942b85fcf8e96074f04925453df69fbe86d890; theorem Couret.InterIA.Fibres.modulus_coprime_monomial

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

theorem modulus_coprime_monomial (m : ℕ) (hm : 0 < m) (i : ℕ)
    (a : ℝ) (ha : a ≠ 0) : IsCoprime (X^m+1 : ℝ[X]) (monomial i a) := by sorry








end Couret.InterIA.Fibres
