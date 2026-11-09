-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_four_collision_shift_iff
-- name    : Couret.InterIA.Catalogue.Exact.four_collision_shift_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:13.06129+00:00
-- url     : https://prove2.me/theorems/fef3519e-dab3-4e9a-8437-326b48987def
-- title:
--   four collision shift iff
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. Here ℤ/0ℤ means ℤ, so modulus zero is included. For every natural n, finite S,T⊆ℤ/nℤ and t∈ℤ/nℤ with 2t=0, the conjunction |S|=4, |T+t|=4, Q(S,z)=Q(T+t,z) for every z, and S not affinely equivalent to T+t holds if and only if the conjunction |S|=|T|=4, Q(S,z)=Q(T,z) for every z, and S not affinely equivalent to T holds. Here T+t={z+t:z∈T}.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/ReferenceCatalogueConverse.lean, lines 67–72; source file SHA-256 b8960db280a86d8c11a71df15e18d41866b1c6a5e978040912f6676f87ebfbd0; theorem Couret.InterIA.Catalogue.Exact.four_collision_shift_iff

import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_unilateral_translation_equivalent_iff
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport

theorem four_collision_shift_iff {n : ℕ} (S T : Finset (ZMod n)) (t : ZMod n)
    (ht : t+t=0) : FourCollision S (T.image (fun z => z+t)) ↔ FourCollision S T := by sorry








end Couret.InterIA.Catalogue.Exact
