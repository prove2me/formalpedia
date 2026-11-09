-- Prove2me | Definitions.Def_Couret_QuotientBridge_26f10959e8eb
-- name    : Couret_QuotientBridge_26f10959e8eb
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:34.547023+00:00
-- url     : https://prove2.me/theorems/c2597989-74e6-4e49-b041-020bbd04b1e0
-- title:
--   Projected residuals and integral group-ring moments
-- statement:
--   Defines the projected residual of a common support and two marked points as its pushed-forward indicator plus the two projected point masses. Defines mass as the sum of integer coefficients and first moment as their group-valued weighted sum. Includes compatibility of pushing a point mass with projecting its group label.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientBridge.lean; source file SHA-256 e3039f9ffa13d11690462eb5cb4b77969858bb42cad9a16ac2921936d5203630

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
open Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo Couret.InterIA.Projection

noncomputable def residual (m : ℕ) (C : Finset (ZMod (2*m))) (a b : ZMod (2*m)) :
    AddMonoidAlgebra ℤ (ZMod m) := push m (indicator C) + atom (projection m a) + atom (projection m b)

theorem push_atom (m : ℕ) (a : ZMod (2*m)) :
    push m (atom a) = atom (projection m a) := by
  exact push_single m a 1







section Moment
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The first moment of an integral group-ring element, valued in the group. -/
noncomputable def moment : AddMonoidAlgebra ℤ G →+ G :=
  (Finsupp.liftAddHom (zmultiplesHom G)).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom





end Moment







noncomputable def mass {G : Type*} [AddCommGroup G] : AddMonoidAlgebra ℤ G →+ ℤ :=
  (Finsupp.liftAddHom (fun _ : G => AddMonoidHom.id ℤ)).comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom









end Couret.InterIA.QuotientBridge


