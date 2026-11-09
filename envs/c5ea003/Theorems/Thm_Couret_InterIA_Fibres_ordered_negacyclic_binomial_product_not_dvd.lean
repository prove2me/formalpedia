-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_ordered_negacyclic_binomial_product_not_dvd
-- name    : Couret.InterIA.Fibres.ordered_negacyclic_binomial_product_not_dvd
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:29.80128+00:00
-- url     : https://prove2.me/theorems/b7bd3297-083a-4aa4-8389-29355e106ba6
-- title:
--   A product of ordered real binomials is not divisible by the negacyclic modulus
-- statement:
--   Let $m,i,j,k,l\in\mathbb N$ satisfy $i<j<m$ and $k<l<m$, and let $a,b,c,d\in\mathbb R$ with $a,b,c\ne0$. Then
--
--   $$X^m+1\nmid(aX^i+bX^j)(cX^k+dX^l).$$
--
--   The coefficient $d$ may be zero; no nonzero assumption on it is present.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/NegacyclicBinomial.lean, lines 123–143; source file SHA-256 588e3d124d25fde2fdb187a567942b85fcf8e96074f04925453df69fbe86d890; theorem Couret.InterIA.Fibres.ordered_negacyclic_binomial_product_not_dvd

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_binomial_product_remainder
import Theorems.Thm_Couret_InterIA_Fibres_modulus_coprime_monomial
import Theorems.Thm_Couret_InterIA_Fibres_reducedProduct_ne_zero
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

theorem ordered_negacyclic_binomial_product_not_dvd (m i j k l : ℕ)
    (hij : i < j) (hkl : k < l) (hj : j < m) (hl : l < m)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ¬ (X^m+1 : ℝ[X]) ∣
      (monomial i a+monomial j b)*(monomial k c+monomial l d) := by sorry




end Couret.InterIA.Fibres
