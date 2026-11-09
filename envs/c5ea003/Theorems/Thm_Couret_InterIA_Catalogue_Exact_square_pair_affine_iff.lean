-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_square_pair_affine_iff
-- name    : Couret.InterIA.Catalogue.Exact.square_pair_affine_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:50.08841+00:00
-- url     : https://prove2.me/theorems/e0272ce7-f3d4-4f79-bee5-b1d9686896a0
-- title:
--   square pair affine iff
-- statement:
--   For every natural number $n$, finite subsets $S,T$ of $ℤ/nℤ$, unit $u$, and residue $v$, write $Q_E(z)$ for the number of ordered pairs $(x,y)∈E×E$ with $x+y=z$. the equality $Q_{uS+v}(z)=Q_{uT+v}(z)$ for every $z$ is equivalent to $Q_S(z)=Q_T(z)$ for every $z$. This includes $n=0$ and empty sets.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/ReferenceCatalogueConverse.lean, lines 34–50; source file SHA-256 b8960db280a86d8c11a71df15e18d41866b1c6a5e978040912f6676f87ebfbd0; theorem Couret.InterIA.Catalogue.Exact.square_pair_affine_iff

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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_ordered_square_affine_at
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport

theorem square_pair_affine_iff {n : ℕ} (S T : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v : ZMod n) :
    (∀ z, orderedSquare (S.image (fun x => (u : ZMod n)*x+v)) z=
      orderedSquare (T.image (fun x => (u : ZMod n)*x+v)) z) ↔
      ∀ z, orderedSquare S z=orderedSquare T z := by sorry














end Couret.InterIA.Catalogue.Exact
