-- Prove2me | Definitions.Def_Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
-- name    : Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:51.650058+00:00
-- url     : https://prove2.me/theorems/b44c267f-0b0d-4788-a7f6-bc8a41fc7491
-- title:
--   Nontranslation collision graphs at a prescribed symmetric difference
-- statement:
--   For finite supports in a finite abelian group, retain the nontranslated square-fibre neighbours $T$ of $S$ for which $|S\triangle T|=k$. The resulting simple graph has adjacency when $S$ is a triple and $T$ is such a neighbour.
--
--   The construction includes symmetry, absence of loops and a decidable adjacency interface. This supports exact degree and edge counts separately for each symmetric-difference size.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaExceptionalCount.lean; source file SHA-256 f29a05e63c72c6391cb5af4eda72214b169f1bd248608234ab836d615b0d4ef0

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374

set_option autoImplicit false

/-!
Unordered nontranslation collisions, split by symmetric-difference size.
The ambient group is finite abelian, supports have cardinality three, and
zero is permitted. An exceptional source has one delta-four neighbour and
`|G[2]| - 1` delta-six neighbours. Graph degree sums count unordered pairs
twice, so the final statements require no division in natural numbers.
-/

open scoped BigOperators symmDiff

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Nontranslated square partners having the prescribed symmetric difference. -/
def nontranslationDeltaNeighbours (S : Finset G) (k : ℕ) : Finset (Finset G) :=
  (nontranslatedNeighbours S).filter (fun T => (S ∆ T).card = k)



/-- The nontranslation collision graph at a fixed symmetric-difference size.
Finite subsets that are not triples are isolated vertices. -/
def nontranslationDeltaGraph (k : ℕ) : SimpleGraph (Finset G) where
  Adj S T := S.card = 3 ∧ T ∈ nontranslationDeltaNeighbours S k
  symm := by
    intro S T h
    obtain ⟨hN, hdelta⟩ := Finset.mem_filter.mp h.2
    refine ⟨((mem_nontranslatedNeighbours S T h.1).mp hN).1, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨nontranslatedNeighbours_symm S T h.1 hN, ?_⟩
    rw [symmDiff_comm]
    exact hdelta
  loopless := by
    constructor
    intro S h
    exact nontranslatedNeighbours_irrefl S h.1 (Finset.mem_filter.mp h.2).1

noncomputable instance nontranslationDeltaGraph_decidableRel (k : ℕ) :
    DecidableRel (nontranslationDeltaGraph (G := G) k).Adj := Classical.decRel _


































end Couret.STROBO2TORS


