-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Parameters_two_pattern_parameter_separation
-- name    : Couret.InterIA.Catalogue.Parameters.two_pattern_parameter_separation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:33:06.214615+00:00
-- url     : https://prove2.me/theorems/3cf8c7df-65ab-4487-bd97-abfcc1968ae5
-- title:
--   two pattern parameter separation
-- statement:
--   For all natural n,q with n=4q and x∈ℤ/nℤ, if the finite set {0,q,x,x+2q} has cardinality 4, then x∉{0,q,2q,3q}. When q=n=0 the ring is ℤ and the cardinality hypothesis cannot hold.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineParameterControls.lean, lines 45–61; source file SHA-256 b23f6d173f81bdcce0efd0f521f478b044082f8c922fd091f81c4bf2ca25e413; theorem Couret.InterIA.Catalogue.Parameters.two_pattern_parameter_separation

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
import Theorems.Thm_Couret_InterIA_Catalogue_Parameters_four_card_separations
import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Parameters
open Finset Couret.InterIA.Catalogue.Affine Couret.InterIA.Parity

variable {G : Type*} [DecidableEq G]

theorem two_pattern_parameter_separation (n q : ℕ) (hn : n=4*q) (x : ZMod n)
    (hc : ({0,(q : ZMod n),x,x+2 • (q : ZMod n)} : Finset (ZMod n)).card=4) :
    x ∉ ({0,(q : ZMod n),2 • (q : ZMod n),3 • (q : ZMod n)} : Finset (ZMod n)) := by sorry








end Couret.InterIA.Catalogue.Parameters
