-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_scaled_parameter_admissible
-- name    : Couret.InterIA.Catalogue.Exact.scaled_parameter_admissible
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:15.865921+00:00
-- url     : https://prove2.me/theorems/e2fa14bb-a936-4ac1-8a8c-a71306d9f1af
-- title:
--   scaled parameter admissible
-- statement:
--   For all natural d,b with d>0 and b≥2, the residue d in ℤ/(4db)ℤ belongs to none of {0,db,2db,3db}.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/ReferenceCatalogueConverse.lean, lines 74–92; source file SHA-256 b8960db280a86d8c11a71df15e18d41866b1c6a5e978040912f6676f87ebfbd0; theorem Couret.InterIA.Catalogue.Exact.scaled_parameter_admissible

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
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport

theorem scaled_parameter_admissible (d b : ℕ) (hd : 0 < d) (hb : 2 ≤ b) :
    (d : ZMod (4*(d*b))) ∉ badParameters (d*b) := by sorry






end Couret.InterIA.Catalogue.Exact
