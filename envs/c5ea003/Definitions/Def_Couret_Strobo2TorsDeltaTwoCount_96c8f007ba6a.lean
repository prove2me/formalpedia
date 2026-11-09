-- Prove2me | Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
-- name    : Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:16.18709+00:00
-- url     : https://prove2.me/theorems/c4190919-2eac-488f-868e-de4eca56ed6b
-- title:
--   Parameters for distance-two ordinary collisions
-- statement:
--   A dependent triple of group elements serves as a raw parameter type. A finite parameter subset imposes the distance-two conditions; realization maps it to an ordered pair of supports. The ordered-pair family records the corresponding ordinary square collisions. This is the enumeration interface used to count distance-two edges.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaTwoCount.lean; source file SHA-256 cb89a555428b446017e32cc8ccac7e557459a109f1144b64f2304523abb8127d

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact count of the ordinary delta-two edges, with zero allowed.

Parameters (a,u,b) have u a nonzero element of G[2] and b outside
{a,a+u}. They represent the ordered pair
({a,a+u,b}, {a,a+u,b+u}). Each ordered pair has precisely two
parameters, according to the choice a or a+u in its common pair.
The graph handshake supplies the second factor of two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]













variable [Fintype G]

abbrev DeltaTwoParameter (G : Type*) := Σ _ : G × G, G

def deltaTwoParameters : Finset (DeltaTwoParameter G) :=
  ((Finset.univ : Finset G) ×ˢ ((twoTorsion : Finset G).erase 0)).sigma
    (fun au => Finset.univ \ {au.1, au.1 + au.2})

def deltaTwoRealization (p : DeltaTwoParameter G) : Finset G × Finset G :=
  ({p.1.1, p.1.1 + p.1.2, p.2},
    {p.1.1, p.1.1 + p.1.2, p.2 + p.1.2})





attribute [local instance] Classical.propDecidable

/-- Oriented ordinary triple pairs with two common points. By the certified
delta classification, these are exactly the equal-square delta-two pairs. -/
noncomputable def deltaTwoOrderedPairs : Finset (Finset G × Finset G) :=
  ((tripleSupports : Finset (Finset G)) ×ˢ tripleSupports).filter
    (fun p => OrdinaryPartner p.1 p.2 ∧ (p.1 ∩ p.2).card = 2)




















end Couret.STROBO2TORS


