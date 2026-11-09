-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Orbits_invariant_coeff_nsmul
-- name    : Couret.InterIA.Catalogue.Orbits.invariant_coeff_nsmul
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:50.181938+00:00
-- url     : https://prove2.me/theorems/11682f1f-5443-43ac-b931-0cb4e024bb99
-- title:
--   Coefficients are constant along translation orbits
-- statement:
--   Let $G$ be an abelian group and $W\in\mathbb Z[G]$. If $W=X^\delta W$ for $\delta\in G$, then for every $x\in G$ and natural $k$, $$[X^{x+k\delta}]W=[X^x]W.$$
--
--   The zero multiple is included.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientOrbits.lean, lines 20–26; source file SHA-256 90a9fb6b3c18f1724e125dbed131f8a89171589bc356f33f17aa73d3bf1014b8; theorem Couret.InterIA.Catalogue.Orbits.invariant_coeff_nsmul

import Definitions.Def_Couret_QuotientOrbits_0c82b3d4a090
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_QuotientPeriods_cf8d74422994

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem invariant_coeff_nsmul (W : AddMonoidAlgebra ℤ G) (δ : G)
    (he : W=AddMonoidAlgebra.single δ 1*W) (x : G) (k : ℕ) :
    W.coeff (x+k • δ)=W.coeff x := by sorry






end Couret.InterIA.Catalogue.Orbits
