-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_probe_union
-- name    : Couret.InterIA.Cubic.probe_union
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:23.022396+00:00
-- url     : https://prove2.me/theorems/ea589145-f83b-494c-ba31-4fd5e9875947
-- title:
--   Probes add on disjoint unions
-- statement:
--   Let $G$ be an abelian group, $r:G\to\mathbb R$, and finite disjoint supports $S,T$. Put $P_r(S)(z)=\sum_{x\in S}r(z-x)$. Then, as functions of $z$, $$P_r(S\cup T)=P_r(S)+P_r(T).$$ Empty supports are allowed; this is additivity of convolution by a finite indicator.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicSupport.lean, lines 89–93; source file SHA-256 86b6a418d9e2de393ac4913cf0aea258d411abf4d8e8d64d56470cdd2f3eb82d; theorem Couret.InterIA.Cubic.probe_union

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

theorem probe_union {G : Type*} [AddCommGroup G] [DecidableEq G]
    (r : G → ℝ) (S T : Finset G) (hd : Disjoint S T) :
    probe r (S ∪ T)=probe r S+probe r T := by sorry




end Couret.InterIA.Cubic
