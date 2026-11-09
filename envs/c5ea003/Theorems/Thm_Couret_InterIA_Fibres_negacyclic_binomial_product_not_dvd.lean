-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_negacyclic_binomial_product_not_dvd
-- name    : Couret.InterIA.Fibres.negacyclic_binomial_product_not_dvd
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:05.270139+00:00
-- url     : https://prove2.me/theorems/c0b75036-74b4-4736-bc8d-7a5f4ff96211
-- title:
--   A negacyclic polynomial cannot divide this binomial product
-- statement:
--   Let $m\in\mathbb N$, $i,j,k,l<m$, with $i\ne j$ and $k\ne l$, and let $a,b,c,d\in\mathbb R$ be nonzero. Then
--
--   $$X^m+1\nmid(aX^i+bX^j)(cX^k+dX^l).$$
--
--   This excludes binomial factorizations producing a vanishing negacyclic product.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/NegacyclicBinomial.lean, lines 145–159; source file SHA-256 588e3d124d25fde2fdb187a567942b85fcf8e96074f04925453df69fbe86d890; theorem Couret.InterIA.Fibres.negacyclic_binomial_product_not_dvd

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_ordered_negacyclic_binomial_product_not_dvd
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

theorem negacyclic_binomial_product_not_dvd (m i j k l : ℕ)
    (hi : i < m) (hj : j < m) (hk : k < m) (hl : l < m)
    (hij : i ≠ j) (hkl : k ≠ l)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ¬ (X^m+1 : ℝ[X]) ∣
      (monomial i a+monomial j b)*(monomial k c+monomial l d) := by sorry


end Couret.InterIA.Fibres
