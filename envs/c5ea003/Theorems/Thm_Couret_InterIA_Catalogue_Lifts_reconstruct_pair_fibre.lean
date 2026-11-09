-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Lifts_reconstruct_pair_fibre
-- name    : Couret.InterIA.Catalogue.Lifts.reconstruct_pair_fibre
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:39.403056+00:00
-- url     : https://prove2.me/theorems/648d2de8-0496-4e42-9487-676dd75cb442
-- title:
--   Reconstructing a support from a fibre
-- statement:
--   For every natural $m$, finite subsets $S,T$ of $R=\operatorname{ZMod}(2m)$, and $a,c,d\in R$, if $S\setminus T=\{a,a+m\}$ and $S\cap T=\{c,d\}$, then $S=\{c,d,a,a+m\}$. Distinctness is not required, and $m=0$, where $R=\mathbb Z$ and the first displayed set is a singleton, is included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitLiftGeometry.lean, lines 48–53; source file SHA-256 9a24bf9b337b4d4892c4df1227e258531057bd84d540c5a60e997582e6ecc31c; theorem Couret.InterIA.Catalogue.Lifts.reconstruct_pair_fibre

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

theorem reconstruct_pair_fibre (m : ℕ) (S T : Finset (ZMod (2*m)))
    (a c d : ZMod (2*m)) (hU : S \ T=fibre (m : ZMod (2*m)) a)
    (hC : S ∩ T={c,d}) : S={c,d,a,a+m} := by sorry


end Couret.InterIA.Catalogue.Lifts
