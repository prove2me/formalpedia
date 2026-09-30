-- Prove2me | Theorems.Thm_HirschCircuit_elementary_conformal_decomposition_ambient_bound
-- name    : HirschCircuit.elementary_conformal_decomposition_ambient_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-08T19:57:33.444053+00:00
-- url     : https://prove2.me/theorems/05726681-715c-408a-b44c-d73dac856b20
-- title:
--   Conformal elementary decomposition with an ambient-coordinate bound
-- statement:
--   Every vector $z$ in a real linear subspace $K\subseteq\mathbb R^n$ can be written as a sum of at most $n$ nonzero support-minimal vectors of $K$. Each summand has the same closed-orthant signs as $z$ and is coordinatewise no larger in absolute value. The zero vector is represented by the empty sum. This ambient-coordinate bound does not assert a maximal circuit-walk bound or the sharper dimension bound.
-- source:
--   Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Definition 2.1 and Lemma 2.2. Matrix-free ambient-coordinate relaxation, proved by support-cardinality induction; no novelty claim.

import Definitions.Def_Hirsch_circuit_slack_model
set_option autoImplicit false

theorem HirschCircuit.elementary_conformal_decomposition_ambient_bound {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (z : Fin n → ℝ) (hz : z ∈ K) :
    ∃ gs : List (Fin n → ℝ), gs.length ≤ n ∧
      (∀ g ∈ gs, HirschCircuit.IsElementaryIn K g ∧
        ∀ i, 0 ≤ g i * z i ∧ |g i| ≤ |z i|) ∧ gs.sum = z := by sorry
