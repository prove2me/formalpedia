-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Parameters_affine_image_card
-- name    : Couret.InterIA.Catalogue.Parameters.affine_image_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:47:51.007978+00:00
-- url     : https://prove2.me/theorems/4b34df0f-af39-45d8-9d97-250975025b44
-- title:
--   affine image card
-- statement:
--   Here ℤ/0ℤ means ℤ, so modulus zero is included. For every natural n, finite S⊆ℤ/nℤ, unit u of ℤ/nℤ and v∈ℤ/nℤ, the image {u z+v:z∈S} has cardinality |S|. The empty set is included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineParameterControls.lean, lines 38–43; source file SHA-256 b23f6d173f81bdcce0efd0f521f478b044082f8c922fd091f81c4bf2ca25e413; theorem Couret.InterIA.Catalogue.Parameters.affine_image_card

import Definitions.Def_Couret_AffineParameterControls_321393084939
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
import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Parameters
open Finset Couret.InterIA.Catalogue.Affine Couret.InterIA.Parity

variable {G : Type*} [DecidableEq G]

theorem affine_image_card (n : ℕ) (S : Finset (ZMod n)) (u : (ZMod n)ˣ) (v : ZMod n) :
    (S.image (fun z => (u : ZMod n)*z+v)).card=S.card := by sorry










end Couret.InterIA.Catalogue.Parameters
