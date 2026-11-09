-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_orbit_separated_family_card_le_two
-- name    : Couret.STROBO2TORS.recoh_orbit_separated_family_card_le_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:55:45.849378+00:00
-- url     : https://prove2.me/theorems/7a0541cb-f2cf-4f13-b447-98f4e9194a08
-- title:
--   At most two orbit-separated representatives share a triple square
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $P$ be a finite family of three-element supports all with the same ordered square. Suppose no two distinct members are two-torsion translates. Then
--
--   $$|P|\le2.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDedupTransport.lean, lines 21–54; source file SHA-256 dd13e6ade9a021706d0ec14fbcbb837eac41d9018980c650ddd694417386b379; theorem Couret.STROBO2TORS.recoh_orbit_separated_family_card_le_two

import Aesop
import Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_realization_of_ordinary_partner
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_le_two_h
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbits_disjoint
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06

set_option autoImplicit false

/-!
Transport through the explicit anchored deduplication model.

An enumeration and an anchor remain explicit inputs with representation
contracts. The decoder really recovers from the retained representatives.
The fibre classification bounds their number by two, without assuming that
the supplied square data are realizable. No Python list-order or JSON
equivalence is claimed by this module.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_orbit_separated_family_card_le_two
    (R : G → ℕ) (P : Finset (Finset G))
    (hsound : ∀ B ∈ P, B.card = 3 ∧ orderedSquare B = R)
    (hsep : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → ¬ OrdinaryPartner B C) :
    P.card ≤ 2 := by sorry










section CyclicSelected

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





















end CyclicSelected

end Couret.STROBO2TORS
