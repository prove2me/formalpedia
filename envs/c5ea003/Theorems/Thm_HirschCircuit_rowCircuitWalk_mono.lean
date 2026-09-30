-- Prove2me | Theorems.Thm_HirschCircuit_rowCircuitWalk_mono
-- name    : HirschCircuit.rowCircuitWalk_mono
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-08T18:47:47.942249+00:00
-- url     : https://prove2.me/theorems/25951473-a407-43c4-a7be-443e35593402
-- title:
--   Padded row-circuit walks are monotone in the budget
-- statement:
--   A padded maximal row-circuit walk of length at most $L$ can be represented with any larger budget $M\ge L$ by retaining the original walk through time $L$ and then remaining at its final endpoint. This establishes monotonicity of the padded circuit-walk predicate in its step budget.
-- source:
--   Formalization helper for the Polynomial Hirsch circuit reduction; follows directly from the padded-walk definition in Hirsch_circuit_model.

import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
open Hirsch

namespace HirschCircuit

theorem rowCircuitWalk_mono {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {L M : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (h : RowCircuitWalk a b L u v) (hLM : L ≤ M) :
    RowCircuitWalk a b M u v := by sorry

end HirschCircuit
