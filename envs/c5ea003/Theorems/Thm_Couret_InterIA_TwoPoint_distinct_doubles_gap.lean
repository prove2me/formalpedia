-- Prove2me | Theorems.Thm_Couret_InterIA_TwoPoint_distinct_doubles_gap
-- name    : Couret.InterIA.TwoPoint.distinct_doubles_gap
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:30:48.131733+00:00
-- url     : https://prove2.me/theorems/00e870cf-ddce-43ca-b8be-c3cc47b9ced4
-- title:
--   Gap from two-point coefficients
-- statement:
--   For every additive commutative group $G$ with decidable equality and $a,b,c,d\in G$, assume $a\ne b$, $2a\ne2b$, and for every $z\in G$, $[2a=z]+[2b=z]+2[a+b=z]=[2c=z]+[2d=z]+2[c+d=z]$, where brackets equal $1$ when their condition holds and $0$ otherwise. Then $d-c=b-a$ or $c-d=b-a$. Distinctness of $c,d$ is not separately assumed.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TwoPointCollision.lean, lines 55–80; source file SHA-256 2b544e811d91074c1143be0a41817cbd978462a670ca9d6c7b39cd133d16f371; theorem Couret.InterIA.TwoPoint.distinct_doubles_gap

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

theorem distinct_doubles_gap (a b c d : G) (hab : a ≠ b)
    (hd : a+a ≠ b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) :
    d-c=b-a ∨ c-d=b-a := by sorry
















end Couret.InterIA.TwoPoint
