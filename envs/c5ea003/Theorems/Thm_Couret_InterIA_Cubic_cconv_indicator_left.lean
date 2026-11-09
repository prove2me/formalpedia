-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_cconv_indicator_left
-- name    : Couret.InterIA.Cubic.cconv_indicator_left
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:58:13.394945+00:00
-- url     : https://prove2.me/theorems/d9108e23-5922-4ef3-926d-efd8c8698737
-- title:
--   Convolution with an indicator is a support sum
-- statement:
--   Let $G$ be a finite abelian group. Let $S\subseteq G$, $g:G\to\mathbb C$, and $z\in G$. For $f*g(z)=\sum_{x+y=z}f(x)g(y)$ and indicator $1_S$,
--
--   $$(1_S*g)(z)=\sum_{x\in S}g(z-x).$$
--
--   This connects convolution notation with direct support evaluation.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicSupport.lean, lines 26–47; source file SHA-256 86b6a418d9e2de393ac4913cf0aea258d411abf4d8e8d64d56470cdd2f3eb82d; theorem Couret.InterIA.Cubic.cconv_indicator_left

import Definitions.Def_Couret_CubicSupport_513df21f9351
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity

theorem cconv_indicator_left {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (g : G → ℂ) (z : G) :
    cconv (complexIndicator S) g z = ∑ x ∈ S, g (z-x) := by sorry














end Couret.InterIA.Cubic
