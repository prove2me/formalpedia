-- Prove2me | Definitions.Def_Couret_Strobo2TorsNontranslationSymmetry_29c4a2e9c2a5
-- name    : Couret_Strobo2TorsNontranslationSymmetry_29c4a2e9c2a5
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:03.849137+00:00
-- url     : https://prove2.me/theorems/3d2d8aa4-bd08-4de4-b389-9c00d7fadf40
-- title:
--   Symmetry of nontranslation square neighbours
-- statement:
--   The nontranslation-neighbour family consists of square-equivalent triples outside the two-torsion orbit of the source. This bundle supplies the symmetry and irreflexivity interface for that relation on three-element supports.
--
--   Those properties permit packaging the nontranslation collision relation as a simple graph for unordered edge counting.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationSymmetry.lean; source file SHA-256 2381e904cb9a097a828d8cb86ec74db6c4ad62f0b1e80fff2bb62a6731d0797d

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The nontranslation collision relation is symmetric: all ambient
translations are excluded, not just those in the two-torsion subgroup. -/
theorem nontranslatedNeighbours_symm
    (S T : Finset G) (hS : S.card = 3)
    (hT : T ∈ nontranslatedNeighbours S) :
    S ∈ nontranslatedNeighbours T := by
  obtain ⟨hTcard, hSq, hNo⟩ :=
    (mem_nontranslatedNeighbours S T hS).mp hT
  apply (mem_nontranslatedNeighbours T S hTcard).mpr
  refine ⟨hS, (fun z => (hSq z).symm), ?_⟩
  rintro ⟨v, hv⟩
  apply hNo
  refine ⟨-v, ?_⟩
  have hBack : translateSupport S (-v) = T := by
    rw [hv, translateSupport_add]
    simp [translateSupport]
  exact hBack.symm

/-- No support is its own nontranslated collision partner. -/
theorem nontranslatedNeighbours_irrefl (S : Finset G)
    (hS : S.card = 3) : S ∉ nontranslatedNeighbours S := by
  intro h
  have hNo := ((mem_nontranslatedNeighbours S S hS).mp h).2.2
  apply hNo
  refine ⟨0, ?_⟩
  simp [translateSupport]

end Couret.STROBO2TORS


