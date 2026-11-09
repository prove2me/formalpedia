-- Prove2me | Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541
-- name    : Couret_AmbientCollisionAssembly_e789a884d541
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:15:20.12883+00:00
-- url     : https://prove2.me/theorems/0c1ff6d0-312c-4e0f-9ce4-371fb3860304
-- title:
--   Ambient affine reference form
-- statement:
--   For two supports in $\mathbb Z/n\mathbb Z$, defines an ambient reference form by positive integers $d,b$ with $n=4db$ and $b\equiv2\pmod4$, a unit multiplier and a common translation. Their images must be the two dilated reference patterns, in either order. This packages affine equivalence while preserving the ambient modulus.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AmbientCollisionAssembly.lean; source file SHA-256 5644ce4fd9e8bafd6f25e78efbcd512000a4dad8e6841d2bcb4e0131600ca136

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
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive Couret.InterIA.Catalogue.Parameters
open Couret.InterIA.Catalogue.AffineTransport Couret.InterIA.Parity

/-- A common ambient affinity to a dilated parameter-one pair; both orientations are retained. -/
def AmbientReferenceForm (n : ℕ) (S T : Finset (ZMod n)) : Prop :=
  ∃ d b : ℕ, 0 < d ∧ 0 < b ∧ n=4*(d*b) ∧ b%4=2 ∧
    ∃ U : (ZMod n)ˣ, ∃ V : ZMod n,
      (S.image (fun z => (U : ZMod n)*z+V)=(patternA b 1).image (dilate n d) ∧
       T.image (fun z => (U : ZMod n)*z+V)=(patternB b 1).image (dilate n d)) ∨
      (S.image (fun z => (U : ZMod n)*z+V)=(patternB b 1).image (dilate n d) ∧
       T.image (fun z => (U : ZMod n)*z+V)=(patternA b 1).image (dilate n d))









end Couret.InterIA.Catalogue.Quarter.Ambient


