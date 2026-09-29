-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
-- name    : mme_HasTauValueAtLeast_bigAdd_uniform_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:11:13.374214+00:00
-- url     : https://prove2.me/theorems/71504438-3cad-46b9-b74f-3831202fdc61
-- title:
--   Strict uniform tau-values add over a finite tensor direct sum
-- statement:
--   Let $T_1,…,T_k$ be tensors. Suppose every summand $T_i$ has asymptotic tau-value at least every nonnegative scalar strictly below a common bound $B$. Then their direct sum has tau-value at least every nonnegative $V$ satisfying
--
--   $$V<kB.$$
--
--   The strict formulation avoids any endpoint-continuity assumption. It is the finite direct-sum superadditivity principle needed when an outer laser extraction produces many address blocks with one common lower value.
-- source:
--   The standard direct-sum superadditivity of the Coppersmith--Winograd asymptotic tau-value, in a strict witness-level formulation; compare D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 6.

import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_HasTauValueAtLeast_bigAdd_uniform_strict
    {K : Type u} [Field K] {k : ℕ}
    (F : Fin k → TensorObj K 3)
    (tau B : ℝ) (hB : 0 ≤ B)
    (hcomponent : ∀ i : Fin k, ∀ W : ℝ,
      0 ≤ W → W < B → HasTauValueAtLeast (F i) tau W)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < (k : ℝ) * B) :
    HasTauValueAtLeast (TensorObj.bigAdd F) tau V := by
  sorry
