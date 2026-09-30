-- Prove2me | Theorems.Thm_HirschCircuit_exists_irredundant_strict_model
-- name    : HirschCircuit.exists_irredundant_strict_model
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-08T16:16:43.910522+00:00
-- url     : https://prove2.me/theorems/8734b2cd-5242-49d5-af5a-d0d57bc0953f
-- title:
--   Irredundant strict presentation from separated feasible endpoints
-- statement:
--   Let an $n$-row H-polyhedron contain feasible points $u$ and $v$. Assume that every nonzero describing row is not tight at both endpoints. Then some subfamily of $m\le n$ original rows defines exactly the same feasible set, is irredundant, and admits a point strictly satisfying every retained inequality.
--
--   The retained family is chosen with minimum cardinality. Row-deletion witnesses give irredundancy, and the midpoint of $u$ and $v$ is strictly feasible for every retained nonzero row. This normalization is useful before translating an H-polytope into slack coordinates for circuit-walk arguments.
-- source:
--   Elementary normalization lemma used in the circuit-routing reduction for the Polynomial Hirsch mission; the downstream slack-coordinate motivation is Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Section 1.1 and Theorem 3.1.

import Definitions.Def_Hirsch_circuit_model
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

theorem HirschCircuit.exists_irredundant_strict_model
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hv : v ∈ Hpoly a b)
    (hsep : ∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hpoly a b ∧
      RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) ∧
      StrictlyFeasibleRows (fun j => a (e j)) (fun j => b (e j)) := by sorry
