-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_square_cube_support_injective
-- name    : Couret.InterIA.Cubic.square_cube_support_injective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:35.340112+00:00
-- url     : https://prove2.me/theorems/a695adb1-1538-4704-a25c-44761ad42ba3
-- title:
--   Square and cube counts determine a cyclic support
-- statement:
--   Let $n>0$ and $S,T\subseteq\mathbb Z/n\mathbb Z$ be finite supports. Let $Q_S(z)$ and $C_S(z)$ count ordered pairs and ordered triples from $S$ summing to $z$. If $Q_S=Q_T$ and $C_S=C_T$ pointwise, then
--
--   $$S=T.$$
--
--   The combined second and third convolution powers uniquely determine the support, without cardinality restrictions.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicSupport.lean, lines 67–83; source file SHA-256 86b6a418d9e2de393ac4913cf0aea258d411abf4d8e8d64d56470cdd2f3eb82d; theorem Couret.InterIA.Cubic.square_cube_support_injective

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
import Theorems.Thm_Couret_InterIA_Cubic_cconv_indicator_left
import Theorems.Thm_Couret_InterIA_Cubic_square_cube_injective
import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity

theorem square_cube_support_injective (n : ℕ) (hn : 0<n)
    (S T : Finset (ZMod n))
    (hs : ∀ z, orderedSquare S z=orderedSquare T z)
    (hc : ∀ z, orderedCube S z=orderedCube T z) : S=T := by sorry








end Couret.InterIA.Cubic
