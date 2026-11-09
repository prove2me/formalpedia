-- Prove2me | Theorems.Thm_Couret_InterIA_TwoPoint_equal_doubles_gap
-- name    : Couret.InterIA.TwoPoint.equal_doubles_gap
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:30:49.361117+00:00
-- url     : https://prove2.me/theorems/bead67c5-87af-4f5b-bb4e-1cc5462501b5
-- title:
--   equal doubles gap
-- statement:
--   Let G be any additive commutative group with decidable equality. For all a,b,c,d∈G with a≠b, c≠d and 2a=2b, if for every z∈G the natural numbers [2a=z]+[2b=z]+2[a+b=z] and [2c=z]+[2d=z]+2[c+d=z] are equal, then d−c=b−a or c−d=b−a. Here [P] equals 1 if P holds and 0 otherwise.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TwoPointCollision.lean, lines 100–119; source file SHA-256 2b544e811d91074c1143be0a41817cbd978462a670ca9d6c7b39cd133d16f371; theorem Couret.InterIA.TwoPoint.equal_doubles_gap

import Definitions.Def_Couret_TwoPointCollision_eefa36a5b454
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.TwoPoint
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem equal_doubles_gap (a b c d : G) (hab : a ≠ b) (hcd : c ≠ d)
    (hd : a+a=b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) :
    d-c=b-a ∨ c-d=b-a := by sorry










end Couret.InterIA.TwoPoint
