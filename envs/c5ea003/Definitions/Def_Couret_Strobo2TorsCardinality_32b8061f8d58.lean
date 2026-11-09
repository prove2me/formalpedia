-- Prove2me | Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
-- name    : Couret_Strobo2TorsCardinality_32b8061f8d58
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:47.412473+00:00
-- url     : https://prove2.me/theorems/2020a940-ae15-4498-82d7-83a3234cdd87
-- title:
--   Triple square fibres and torsion translation orbits
-- statement:
--   For a finite abelian group, this defines the two-torsion set $H=\{u:2u=0\}$, the orbit $\mathcal O(S)=\{S+u:u\in H\}$, and the square fibre consisting of all three-element supports with the same ordered pair-sum counts as $S$. Their zero-free versions retain only supports not containing zero.
--
--   It also defines the three-torsion set, its nonzero part, and exceptional offsets $(G[3]\setminus\{0\})\cup((G[3]\setminus\{0\})+d)$. These are the finite objects used in orbit, fibre and offset counts.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem translateSupport_card (S : Finset G) (u : G) :
    (translateSupport S u).card = S.card := by
  exact Finset.card_image_of_injective S (fun _ _ h => add_right_cancel h)





















section Finite

variable [Fintype G]

def twoTorsion : Finset G := Finset.univ.filter (fun u => u + u = 0)

def torsionOrbit (S : Finset G) : Finset (Finset G) :=
  (twoTorsion : Finset G).image (fun u => translateSupport S u)

def squareFibre (S : Finset G) : Finset (Finset G) :=
  Finset.univ.powerset.filter (fun T => T.card = 3 ∧
    ∀ z : G, orderedSquare S z = orderedSquare T z)

def zeroFreeOrbit (S : Finset G) : Finset (Finset G) :=
  (torsionOrbit S).filter (fun T => 0 ∉ T)

def zeroFreeSquareFibre (S : Finset G) : Finset (Finset G) :=
  (squareFibre S).filter (fun T => 0 ∉ T)

theorem mem_twoTorsion (u : G) : u ∈ (twoTorsion : Finset G) ↔ u + u = 0 := by
  simp [twoTorsion]

theorem mem_torsionOrbit (S T : Finset G) :
    T ∈ torsionOrbit S ↔ OrdinaryPartner S T := by
  constructor
  · intro h
    obtain ⟨u, hu, ht⟩ := Finset.mem_image.mp h
    exact ⟨u, (mem_twoTorsion u).mp hu, ht.symm⟩
  · rintro ⟨u, hu, ht⟩
    exact Finset.mem_image.mpr ⟨u, (mem_twoTorsion u).mpr hu, ht.symm⟩

theorem mem_squareFibre (S T : Finset G) :
    T ∈ squareFibre S ↔ T.card = 3 ∧ ∀ z : G, orderedSquare S z = orderedSquare T z := by
  simp [squareFibre]


































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/

def offsetThreeTorsion : Finset G :=
  Finset.univ.filter (fun w => (w + w) + w = 0)

def nonzeroThreeTorsion : Finset G :=
  (offsetThreeTorsion : Finset G).erase 0

def exceptionalOffsets (d : G) : Finset G :=
  (nonzeroThreeTorsion : Finset G) ∪
    (nonzeroThreeTorsion : Finset G).image (fun w => w + d)

















end Finite
end Couret.STROBO2TORS


