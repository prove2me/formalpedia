-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Lifts_two_orbit_lift
-- name    : Couret.InterIA.Catalogue.Lifts.two_orbit_lift
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:36.388576+00:00
-- url     : https://prove2.me/theorems/2f1f3102-8243-4a7a-80b9-8fa108584ee4
-- title:
--   Lifting a two-orbit configuration
-- statement:
--   For every positive natural $m$, finite subsets $S,T\subseteq R=\mathbb Z/(2m)\mathbb Z$, and $a,b,c,d\in R$, assume $S\setminus T=\{a,a+m\}$, $T\setminus S=\{b,b+m\}$, $S\cap T=\{c,d\}$, the reduction of $b-a$ modulo $m$ has additive order $2$, and $\pi(d)=\pi(c)+\pi(b-a)$, where $\pi:R\to\mathbb Z/m\mathbb Z$ is reduction. Then there exist $a',c',r\in R$ with $2r=m$, $S=\{c',c'+r,a',a'+2r\}$ and $T=\{c',c'+r,a'+r,a'+3r\}$. No additional distinctness or cardinality hypotheses are present.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitLiftModels.lean, lines 19–48; source file SHA-256 b53c12478eeb85239ca6f74493f759dcf51a0caac7f55b7bf29361734ff3e646; theorem Couret.InterIA.Catalogue.Lifts.two_orbit_lift

import Definitions.Def_Couret_OrbitLiftModels_210387863d55
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
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_projected_order_two_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_projected_step_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_reconstruct_pair_fibre
import Definitions.Def_Couret_OrbitAssembly_415e94ef1ad8

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Catalogue.Orbits Couret.InterIA.Parity

theorem two_orbit_lift (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (a b c d : ZMod (2*m))
    (hU : S \ T=fibre (m : ZMod (2*m)) a)
    (hV : T \ S=fibre (m : ZMod (2*m)) b) (hC : S ∩ T={c,d})
    (ho : addOrderOf (projection m (b-a))=2)
    (he : projection m d=projection m c+projection m (b-a)) : TwoLift m S T := by sorry




end Couret.InterIA.Catalogue.Lifts
