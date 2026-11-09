-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Lifts_projected_order_four_lift
-- name    : Couret.InterIA.Catalogue.Lifts.projected_order_four_lift
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:32:30.44994+00:00
-- url     : https://prove2.me/theorems/41b72ee2-db93-4e5f-818c-8cd7bdfb4ed0
-- title:
--   Lifting projected order four
-- statement:
--   For every positive natural $m$ and $r\in\mathbb Z/(2m)\mathbb Z$, if the reduction of $r$ modulo $m$ has additive order exactly $4$, then $4r=m$ in $\mathbb Z/(2m)\mathbb Z$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitLiftGeometry.lean, lines 21–40; source file SHA-256 9a24bf9b337b4d4892c4df1227e258531057bd84d540c5a60e997582e6ecc31c; theorem Couret.InterIA.Catalogue.Lifts.projected_order_four_lift

import Definitions.Def_Couret_OrbitAssembly_415e94ef1ad8
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
import Definitions.Def_Couret_OrbitAssembly_415e94ef1ad8

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Catalogue.Orbits Couret.InterIA.Parity

theorem projected_order_four_lift (m : ℕ) (hm : 0 < m) (r : ZMod (2*m))
    (ho : addOrderOf (projection m r)=4) : 4 • r=m := by sorry






end Couret.InterIA.Catalogue.Lifts
