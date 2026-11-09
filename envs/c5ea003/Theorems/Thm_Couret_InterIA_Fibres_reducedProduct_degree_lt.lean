-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_reducedProduct_degree_lt
-- name    : Couret.InterIA.Fibres.reducedProduct_degree_lt
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:50.397562+00:00
-- url     : https://prove2.me/theorems/a86daa46-7109-4add-8b05-4f3c3e6d3709
-- title:
--   The explicit negacyclic remainder has degree below the modulus
-- statement:
--   Let $m,r,s\in\mathbb N$, $r,s<m$, and $a,b\in\mathbb R$. Define $P=1+aX^r+bX^s+abX^{r+s}$ if $r+s<m$, and $P=1+aX^r+bX^s-abX^{r+s-m}$ otherwise. Then
--
--   $$\deg P<m,$$
--
--   with the zero polynomial assigned degree $-\infty$. The exponent hypotheses imply $m>0$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/NegacyclicBinomial.lean, lines 17–29; source file SHA-256 588e3d124d25fde2fdb187a567942b85fcf8e96074f04925453df69fbe86d890; theorem Couret.InterIA.Fibres.reducedProduct_degree_lt

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

theorem reducedProduct_degree_lt (m r s : ℕ) (hr : r < m) (hs : s < m)
    (a b : ℝ) : (reducedProduct m r s a b).degree < (m : WithBot ℕ) := by sorry
















end Couret.InterIA.Fibres
