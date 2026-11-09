-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Affine_four_lift_step_order
-- name    : Couret.InterIA.Catalogue.Affine.four_lift_step_order
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:18.035654+00:00
-- url     : https://prove2.me/theorems/c79f1eb2-647f-4226-83d4-2098eacfcf33
-- title:
--   Order of a four-lift step
-- statement:
--   For every positive natural $m$ and $r\in\mathbb Z/(2m)\mathbb Z$, if $4r=m$, then the additive order of $r$ is exactly $8$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/CyclicStepNormalisation.lean, lines 55–64; source file SHA-256 56cce8151cfebd4ef854f2c3a199f2449366340bb19ea338b9c03a0bd52c731a; theorem Couret.InterIA.Catalogue.Affine.four_lift_step_order

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts

theorem four_lift_step_order (m : ℕ) (hm : 0 < m) (r : ZMod (2*m))
    (hr : 4 • r=m) : addOrderOf r=8 := by sorry


end Couret.InterIA.Catalogue.Affine
