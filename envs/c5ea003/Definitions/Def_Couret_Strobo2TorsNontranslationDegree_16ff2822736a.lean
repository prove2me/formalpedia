-- Prove2me | Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
-- name    : Couret_Strobo2TorsNontranslationDegree_16ff2822736a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:47.075539+00:00
-- url     : https://prove2.me/theorems/3e46536d-bfac-4f79-9e93-7521b92973c6
-- title:
--   Nontranslation collision neighbours
-- statement:
--   For a finite abelian group and support $S$, define its neighbour family to consist of three-element supports with equal ordered square that are not any translate of $S$. Thus the translation exclusion is $$\neg\exists u\in G,\ T=S+u.$$ Its cardinality is the nontranslation degree used in the directed degree sum.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationDegree.lean; source file SHA-256 bb81c661856c1b823aeeb307e2603c5cb0aee20a082885d1c0ea1a2cc7b78ead

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- For one source triple S, retain precisely its partners in the labelled
ordered-square fibre which are not in its two-torsion translation orbit. -/
def nontranslatedNeighbours (S : Finset G) : Finset (Finset G) :=
  squareFibre S \ torsionOrbit S

/-- The complement of the ordinary orbit really excludes every ambient
translation, not just translations from G[2]. -/
theorem mem_nontranslatedNeighbours (S T : Finset G) (hS : S.card = 3) :
    T ∈ nontranslatedNeighbours S ↔
      T.card = 3 ∧
      (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
      ¬ ∃ v : G, T = translateSupport S v := by
  constructor
  · intro hT
    obtain ⟨hFib, hNotOrb⟩ := Finset.mem_sdiff.mp hT
    obtain ⟨hTcard, hSq⟩ := (mem_squareFibre S T).mp hFib
    refine ⟨hTcard, hSq, ?_⟩
    intro hTranslate
    have hOrd : OrdinaryPartner S T :=
      (orderedSquare_translation_iff_ordinary S T hS hTcard).mp
        ⟨hSq, hTranslate⟩
    exact hNotOrb ((mem_torsionOrbit S T).mpr hOrd)
  · rintro ⟨hTcard, hSq, hNotTranslate⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_squareFibre S T).mpr ⟨hTcard, hSq⟩, ?_⟩
    intro hOrd
    obtain ⟨u, _, hTranslate⟩ := (mem_torsionOrbit S T).mp hOrd
    exact hNotTranslate ⟨u, hTranslate⟩













end Couret.STROBO2TORS


