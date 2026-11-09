-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Lifts_four_orbit_lift
-- name    : Couret.InterIA.Catalogue.Lifts.four_orbit_lift
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:28.862197+00:00
-- url     : https://prove2.me/theorems/d9da8e76-f401-4b59-b536-87d4332214e3
-- title:
--   four orbit lift
-- statement:
--   For every positive natural m, finite S,T⊆ℤ/(2m)ℤ and a,b,c,d∈ℤ/(2m)ℤ, let π be reduction modulo m. Assume S∖T={a,a+m}, T∖S={b,b+m}, S∩T={c,d}, the additive order of π(b−a) is 4, π(c)=π(a)+2π(b−a), and π(d)=π(a)+3π(b−a). Then there exist a′,r,c′,d′∈ℤ/(2m)ℤ such that 4r=m, c′∈{a′+2r,a′+6r}, d′∈{a′+3r,a′+7r}, S={c′,d′,a′,a′+4r}, and T={c′,d′,a′+r,a′+5r}. No distinctness of the originally named c,d is explicitly assumed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitLiftModels.lean, lines 50–78; source file SHA-256 b53c12478eeb85239ca6f74493f759dcf51a0caac7f55b7bf29361734ff3e646; theorem Couret.InterIA.Catalogue.Lifts.four_orbit_lift

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
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_projected_order_four_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_projected_step_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_reconstruct_pair_fibre
import Definitions.Def_Couret_OrbitAssembly_415e94ef1ad8

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Catalogue.Orbits Couret.InterIA.Parity

theorem four_orbit_lift (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (a b c d : ZMod (2*m))
    (hU : S \ T=fibre (m : ZMod (2*m)) a)
    (hV : T \ S=fibre (m : ZMod (2*m)) b) (hC : S ∩ T={c,d})
    (ho : addOrderOf (projection m (b-a))=4)
    (hc : projection m c=projection m a+2 • projection m (b-a))
    (hd : projection m d=projection m a+3 • projection m (b-a)) : FourLift m S T := by sorry


end Couret.InterIA.Catalogue.Lifts
