-- Prove2me | Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
-- name    : Couret_Strobo2TorsZeroFreeAll_270e04a89080
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:11.273211+00:00
-- url     : https://prove2.me/theorems/38b3b0ee-fdce-4605-9d7c-3b2792ebebc0
-- title:
--   All nonempty zero-free triple square fibres
-- statement:
--   For a finite abelian group, filters full triple square fibres and ordinary fibres for those retaining a member after removing supports containing zero, then takes their zero-free images. Also groups triple supports by how many of their three points lie in the two-torsion subgroup. These definitions distinguish empty reductions from actual zero-free fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFreeAll.lean; source file SHA-256 57e0e6b2919f605519cfad328e82e56477cae03c002010fa3c4fd6a8c218120b

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

/-- The full labelled-square fibres that have at least one support avoiding zero. -/
def nonemptyFullFibres : Finset (Finset (Finset G)) :=
  (allSquareFibres : Finset (Finset (Finset G))).filter
    (fun F => (withoutZero F).Nonempty)

/-- Ordinary labelled-square fibres that survive removal of zero. -/
def ordinaryNonemptyFibres : Finset (Finset (Finset G)) :=
  (ordinaryFibres : Finset (Finset (Finset G))).filter
    (fun F => (withoutZero F).Nonempty)

def zeroFreeFullFibres : Finset (Finset (Finset G)) :=
  (nonemptyFullFibres : Finset (Finset (Finset G))).image withoutZero

def zeroFreeOrdinaryFibres : Finset (Finset (Finset G)) :=
  (ordinaryNonemptyFibres : Finset (Finset (Finset G))).image withoutZero





























/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/









/-- Actual supports of cardinal three with exactly j members in G[2]. -/
def tripleSupportsProfile (j : ℕ) : Finset (Finset G) :=
  (tripleSupports : Finset (Finset G)).filter
    (fun S => (S ∩ (twoTorsion : Finset G)).card = j)





/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS


