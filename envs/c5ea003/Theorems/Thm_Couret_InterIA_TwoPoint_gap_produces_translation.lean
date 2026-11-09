-- Prove2me | Theorems.Thm_Couret_InterIA_TwoPoint_gap_produces_translation
-- name    : Couret.InterIA.TwoPoint.gap_produces_translation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:30:57.866681+00:00
-- url     : https://prove2.me/theorems/91c80353-1068-43cb-a5fb-77f482516a0c
-- title:
--   gap produces translation
-- statement:
--   For every abelian group $G$ with decidable equality, for all $a,b,c,d∈G$, if $d-c=b-a$ or $c-d=b-a$, then $\{a,b\}+t=\{c,d\}$ for some $t∈G$. No distinctness is required; singleton cases are included.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TwoPointCollision.lean, lines 128–145; source file SHA-256 2b544e811d91074c1143be0a41817cbd978462a670ca9d6c7b39cd133d16f371; theorem Couret.InterIA.TwoPoint.gap_produces_translation

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

theorem gap_produces_translation (a b c d : G)
    (hgap : d-c=b-a ∨ c-d=b-a) :
    ∃ t : G, ({a,b} : Finset G).image (fun x => x+t)=({c,d} : Finset G) := by sorry






end Couret.InterIA.TwoPoint
