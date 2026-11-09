-- Prove2me | Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0
-- name    : Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:56.291872+00:00
-- url     : https://prove2.me/theorems/c1471db1-21ae-4cfa-82e8-37b4448012a5
-- title:
--   Ordinary collision graphs and symmetric-difference layers
-- statement:
--   Defines a simple graph on finite supports whose edges join distinct three-element ordinary partners, meaning partners differing by a two-torsion translation. Defines its layer at natural $k$ by additionally requiring the symmetric difference to have cardinality $k$. Symmetry, absence of loops, and decidability instances are supplied.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaOrdinaryCount.lean; source file SHA-256 5f469c556c1bf01d2004ee02931f1320ffd1877ea4f76323ea4b587ca2c42c59

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Ordinary collision edges on all triple supports, with zero permitted.
The action of the two-torsion subgroup is free on a three-element support.
Consequently every triple has exactly h - 1 distinct ordinary neighbours.
The certified intersection subdivision partitions these edges into delta
two and delta six; this module does not identify ordinary fibres with all
ordinary partner edges, since exceptional fibres contain such edges too.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Ordinary partner edges on all finite subsets, with non-triples isolated. -/
def ordinaryGraph : SimpleGraph (Finset G) where
  Adj S T := S.card = 3 ∧ T.card = 3 ∧ S ≠ T ∧ OrdinaryPartner S T
  symm := by
    rintro S T ⟨hS, hT, hST, u, hu, hTu⟩
    refine ⟨hT, hS, hST.symm, u, hu, ?_⟩
    rw [hTu, translateSupport_twice S u hu]
  loopless := by
    constructor
    intro S h
    exact h.2.2.1 rfl

noncomputable instance ordinaryGraph_decidableRel :
    DecidableRel (ordinaryGraph (G := G)).Adj := Classical.decRel _







/-- Ordinary edges with prescribed symmetric-difference cardinality. -/
def ordinaryDeltaGraph (k : ℕ) : SimpleGraph (Finset G) where
  Adj S T := (ordinaryGraph (G := G)).Adj S T ∧ (S ∆ T).card = k
  symm := by
    intro S T h
    refine ⟨(ordinaryGraph (G := G)).symm h.1, ?_⟩
    rw [symmDiff_comm]
    exact h.2
  loopless := by
    constructor
    intro S h
    exact h.1.2.2.1 rfl

noncomputable instance ordinaryDeltaGraph_decidableRel (k : ℕ) :
    DecidableRel (ordinaryDeltaGraph (G := G) k).Adj := Classical.decRel _














end Couret.STROBO2TORS


