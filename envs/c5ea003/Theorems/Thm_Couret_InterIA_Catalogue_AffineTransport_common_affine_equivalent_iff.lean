-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_common_affine_equivalent_iff
-- name    : Couret.InterIA.Catalogue.AffineTransport.common_affine_equivalent_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:28.248775+00:00
-- url     : https://prove2.me/theorems/98d2760a-9170-46d9-a95d-0314258477e1
-- title:
--   common affine equivalent iff
-- statement:
--   Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. Here ℤ/0ℤ means ℤ, so modulus zero is included. For every natural n, finite S,T⊆ℤ/nℤ, unit u of ℤ/nℤ and v∈ℤ/nℤ, the sets {u z+v:z∈S} and {u z+v:z∈T} are affinely equivalent if and only if S and T are affinely equivalent. Empty sets are included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineEquivalenceTransport.lean, lines 40–54; source file SHA-256 317b8b661cceb15b156cd289602ed84565c6a27bf8af9028f7e0389c60f5aab8; theorem Couret.InterIA.Catalogue.AffineTransport.common_affine_equivalent_iff

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_affine_equivalent_symm
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_affine_equivalent_trans
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.AffineTransport
open Finset Couret.InterIA.NormalForm

theorem common_affine_equivalent_iff {n : ℕ} (S T : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v : ZMod n) :
    AffineEquivalent (S.image (fun z => (u : ZMod n)*z+v))
      (T.image (fun z => (u : ZMod n)*z+v)) ↔ AffineEquivalent S T := by sorry






end Couret.InterIA.Catalogue.AffineTransport
