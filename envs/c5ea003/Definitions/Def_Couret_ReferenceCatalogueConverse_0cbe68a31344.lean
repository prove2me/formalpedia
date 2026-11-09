-- Prove2me | Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
-- name    : Couret_ReferenceCatalogueConverse_0cbe68a31344
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:16:54.911612+00:00
-- url     : https://prove2.me/theorems/2dcbd9a1-39a5-4a5d-a68e-ce6a1ec0e2f5
-- title:
--   Non-affine four-point square collisions
-- statement:
--   For supports $S,T\subseteq\mathbb Z/n$, define $$\operatorname{FourCollision}(S,T)\iff |S|=|T|=4,\quad Q_S=Q_T,\quad S\text{ and }T\text{ are not affinely equivalent}.$$ This packages exactly the collision and nontriviality conditions used by the catalogue converse.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/ReferenceCatalogueConverse.lean; source file SHA-256 b8960db280a86d8c11a71df15e18d41866b1c6a5e978040912f6676f87ebfbd0

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

def FourCollision {n : ℕ} (S T : Finset (ZMod n)) : Prop :=
  S.card=4 ∧ T.card=4 ∧ (∀ z, orderedSquare S z=orderedSquare T z) ∧ ¬ AffineEquivalent S T

















end Couret.InterIA.Catalogue.Exact


