-- Prove2me | Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374
-- name    : Couret_Strobo2TorsNontranslationUnordered_7692bff20374
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:25.501399+00:00
-- url     : https://prove2.me/theorems/be7cb673-3168-4d1e-9c6e-304abba46469
-- title:
--   The simple graph of nontranslation collisions
-- statement:
--   Defines a simple graph on finite supports: a support of size three is adjacent exactly to its nontranslated square-profile neighbours. Its symmetry and looplessness are proved from the neighbour relation, and a classical decidability instance enables finite graph enumeration.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationUnordered.lean; source file SHA-256 9658a84461c5a4d77889dd76eb3dddcec15835d7b88366ad8625c7d4f9683325

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsNontranslationSymmetry_29c4a2e9c2a5
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- A finite graph on all finite subsets, with isolated non-triples. -/
def nontranslationGraph : SimpleGraph (Finset G) where
  Adj S T := S.card = 3 ∧ T ∈ nontranslatedNeighbours S
  symm := by
    intro S T h
    exact ⟨((mem_nontranslatedNeighbours S T h.1).mp h.2).1,
      nontranslatedNeighbours_symm S T h.1 h.2⟩
  loopless := by
    constructor
    intro S h
    exact nontranslatedNeighbours_irrefl S h.1 h.2

/-- Decidable adjacency supplies finite neighbor- and edge-set instances
to mathlib's graph-counting API on the finite vertex type. -/
noncomputable instance nontranslationGraph_decidableRel :
    DecidableRel (nontranslationGraph (G := G)).Adj := Classical.decRel _







end Couret.STROBO2TORS


