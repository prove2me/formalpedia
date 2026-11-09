-- Prove2me | Definitions.Def_Couret_OrbitLiftModels_210387863d55
-- name    : Couret_OrbitLiftModels_210387863d55
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:10:04.895203+00:00
-- url     : https://prove2.me/theorems/497832dd-268e-48e3-8449-ea12274df3dd
-- title:
--   Two-lift and four-lift support models
-- statement:
--   For $S,T\subseteq\mathbb Z/(2m)\mathbb Z$, the two-lift predicate asks for $2r=m$ and
--
--   $$S=\{c,c+r,a,a+2r\},\qquad T=\{c,c+r,a+r,a+3r\}.$$
--
--   The four-lift predicate uses $4r=m$, common entries $c\in\{a+2r,a+6r\}$ and $d\in\{a+3r,a+7r\}$, and exclusive pairs $\{a,a+4r\}$ versus $\{a+r,a+5r\}$. These models state the catalogue geometry directly at support level.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitLiftModels.lean; source file SHA-256 b53c12478eeb85239ca6f74493f759dcf51a0caac7f55b7bf29361734ff3e646

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

/-- Necessary support model for the two-cycle branch; affine normalisation is separate. -/
def TwoLift (m : ℕ) (S T : Finset (ZMod (2*m))) : Prop :=
  ∃ a c r : ZMod (2*m), r+r=m ∧
    S={c,c+r,a,a+2 • r} ∧ T={c,c+r,a+r,a+3 • r}

/-- All antipodal choices of the common points in the four-cycle branch. -/
def FourLift (m : ℕ) (S T : Finset (ZMod (2*m))) : Prop :=
  ∃ a r c d : ZMod (2*m), 4 • r=m ∧
    (c=a+2 • r ∨ c=a+6 • r) ∧ (d=a+3 • r ∨ d=a+7 • r) ∧
    S={c,d,a,a+4 • r} ∧ T={c,d,a+r,a+5 • r}





end Couret.InterIA.Catalogue.Lifts


