-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_normalised_patterns_reference_form
-- name    : Couret.InterIA.Catalogue.Quarter.Ambient.normalised_patterns_reference_form
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:24:54.122508+00:00
-- url     : https://prove2.me/theorems/af873fad-66d1-494b-a3ef-9c66deca0791
-- title:
--   normalised patterns reference form
-- statement:
--   Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For all natural n,q with n=4q and q>0, finite S,T⊆ℤ/nℤ, unit u∈ℤ/nℤ and v,x∈ℤ/nℤ, assume x∉{0,q,2q,3q}, {u z+v:z∈S}={0,q,x,x+2q}, {u z+v:z∈T}={0,q,x+q,x+3q}, and S,T are not affinely equivalent. Then there exist positive natural d,b with n=4db and b congruent to 2 modulo 4, a unit U∈ℤ/nℤ and V∈ℤ/nℤ such that, putting E={0,b,1,1+2b} and F={0,b,1+b,1+3b} as finite subsets of ℤ/(4b)ℤ and D(w)=d·val(w) modulo n, either {U z+V:z∈S}=D(E) and {U z+V:z∈T}=D(F), or the same two equalities hold with E and F exchanged. Here val is the least nonnegative representative.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AmbientCollisionAssembly.lean, lines 18–42; source file SHA-256 5644ce4fd9e8bafd6f25e78efbcd512000a4dad8e6841d2bcb4e0131600ca136; theorem Couret.InterIA.Catalogue.Quarter.Ambient.normalised_patterns_reference_form

import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541
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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_common_affine_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_affine_image_comp
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_pattern_ambient_reference_pair
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive Couret.InterIA.Catalogue.Parameters
open Couret.InterIA.Catalogue.AffineTransport Couret.InterIA.Parity

theorem normalised_patterns_reference_form (n q : ℕ) (hn : n=4*q) (hq : 0 < q)
    (S T : Finset (ZMod n)) (u : (ZMod n)ˣ) (v x : ZMod n)
    (hx : x ∉ ({0,(q : ZMod n),2 • (q : ZMod n),3 • (q : ZMod n)} : Finset (ZMod n)))
    (hS : S.image (fun z => (u : ZMod n)*z+v)={0,(q : ZMod n),x,x+2 • (q : ZMod n)})
    (hT : T.image (fun z => (u : ZMod n)*z+v)={0,(q : ZMod n),x+q,x+3 • (q : ZMod n)})
    (hna : ¬ AffineEquivalent S T) : AmbientReferenceForm n S T := by sorry








end Couret.InterIA.Catalogue.Quarter.Ambient
