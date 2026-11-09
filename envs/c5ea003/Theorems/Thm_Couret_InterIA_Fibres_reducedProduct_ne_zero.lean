-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_reducedProduct_ne_zero
-- name    : Couret.InterIA.Fibres.reducedProduct_ne_zero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:59:43.969365+00:00
-- url     : https://prove2.me/theorems/ab0c92c5-a23e-4891-8711-cc2f00da20c7
-- title:
--   A reduced negacyclic product is nonzero
-- statement:
--   Let $m,r,s\in\mathbb N$ satisfy $0<r<m$ and $0<s<m$, and $a,b\in\mathbb R$ with $a\ne0$. The defined negacyclic reduced product satisfies $$R_{m,r,s}(a,b)\ne0.$$ No nonzero assumption is made on $b$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/NegacyclicBinomial.lean, lines 31–56; source file SHA-256 588e3d124d25fde2fdb187a567942b85fcf8e96074f04925453df69fbe86d890; theorem Couret.InterIA.Fibres.reducedProduct_ne_zero

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

theorem reducedProduct_ne_zero (m r s : ℕ) (hr0 : 0 < r) (_hr : r < m)
    (hs0 : 0 < s) (_hs : s < m) (a b : ℝ) (ha : a ≠ 0) :
    reducedProduct m r s a b ≠ 0 := by sorry














end Couret.InterIA.Fibres
