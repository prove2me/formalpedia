-- Prove2me | Theorems.Thm_Hirsch_irredundant_rows_card_le_any_equivalent_presentation
-- name    : Hirsch.irredundant_rows_card_le_any_equivalent_presentation
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T03:46:19.439369+00:00
-- url     : https://prove2.me/theorems/8538150b-8afe-47ad-94b0-d72189b80264
-- title:
--   Irredundant H-presentations are cardinal-minimal under strict feasibility
-- statement:
--   Let an n-row finite H-presentation be strictly feasible and irredundant, where irredundant means deleting any row strictly enlarges the feasible set. Then every equivalent finite H-presentation has at least n rows. The comparison presentation may use completely different normals and may contain redundant rows, duplicate rows, or zero-normal tautologies. Boundedness is not required.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/1ff86eb9c69679c6355c6fa968b6601482b046a1 ; standalone Lean/Axiom gate Actions run 34559027640

import Mathlib
import Definitions.Def_Hirsch_circuit_model
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch
theorem irredundant_rows_card_le_any_equivalent_presentation
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hirr : RowPresentationIrredundant a b)
    (hstrict : StrictlyFeasibleRows a b)
    (hP : Hpoly c β = Hpoly a b) : n ≤ m := by sorry
end Hirsch
