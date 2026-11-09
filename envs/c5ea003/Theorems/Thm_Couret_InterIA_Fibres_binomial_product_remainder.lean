-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_binomial_product_remainder
-- name    : Couret.InterIA.Fibres.binomial_product_remainder
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:59:25.659224+00:00
-- url     : https://prove2.me/theorems/350bdf4c-5f37-4b34-9444-c8d495ca2239
-- title:
--   The explicit negacyclic binomial product is the remainder
-- statement:
--   Let $m,r,s\in\mathbb N$, $r,s<m$, and $a,b\in\mathbb R$. Define $P=1+aX^r+bX^s+abX^{r+s}$ if $r+s<m$, and $P=1+aX^r+bX^s-abX^{r+s-m}$ otherwise. Then
--
--   $$((1+aX^r)(1+bX^s))\bmod(X^m+1)=P.$$
--
--   The formula allows zero exponents and zero coefficients.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/NegacyclicBinomial.lean, lines 58–86; source file SHA-256 588e3d124d25fde2fdb187a567942b85fcf8e96074f04925453df69fbe86d890; theorem Couret.InterIA.Fibres.binomial_product_remainder

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_reducedProduct_degree_lt
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

theorem binomial_product_remainder (m r s : ℕ) (hr : r < m) (hs : s < m)
    (a b : ℝ) :
    ((1 + monomial r a) * (1 + monomial s b)) %ₘ (X^m + 1) =
      reducedProduct m r s a b := by sorry












end Couret.InterIA.Fibres
