-- Prove2me | Theorems.Thm_Erdos180_subdivisionLine_centers_injective
-- name    : Erdos180.subdivisionLine_centers_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:08:08.795545+00:00
-- url     : https://prove2.me/theorems/4356c40a-5520-4639-88f1-6ce514dc6580
-- title:
--   Distinct centres land on distinct lines
-- statement:
--   If a copy of $S_k$ in $I_q$ sends the centres to lines $C(1), \dots, C(k)$, that
--   assignment is injective.
--
--   Copies are injective on vertices; this is the form in which the source's counting uses it, when
--   it argues that the unique common neighbours of the $3k$ base-centre pairs are distinct, since a
--   repetition would relate two bases or two centres (Lemma 3.1(2)).
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2566-L2579

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Combinatorics.SimpleGraph.Copy

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionLine_centers_injective
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (C : Fin k → SymplecticLine K)
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center)) :
    Function.Injective C := by sorry
