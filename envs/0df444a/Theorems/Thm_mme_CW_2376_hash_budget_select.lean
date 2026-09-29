-- Prove2me | Theorems.Thm_mme_CW_2376_hash_budget_select
-- name    : mme_CW_2376_hash_budget_select
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:31:46.959963+00:00
-- url     : https://prove2.me/theorems/c501c761-afdc-4d40-85c5-41c5e5b9af0a
-- title:
--   An aggregate CW hash budget selects a vertex-closed state with target surplus
-- statement:
--   Let $L$ be a desired real reserve. Suppose the total hash-state budget satisfies: the number of augmented states times $L$, plus the universal target-to-ambient collision bound, is no larger than the exact aggregate target-survival count. Then some affine hash state retains a full marginal-supported hypergraph $E$ for which $|C(T(E),E)|+L$ is at most $|T(E)|$.
--
--   The retained hypergraph is also vertex-closed because the label set is three-term-progression-free in the lower half of the odd modulus. This theorem is the deterministic selection step between the finite incidence estimates and target-relative collision deletion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), affine hashing, Salem--Spencer restriction, and collision deletion on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_CW_2376_hash_incidence_sums
import Theorems.Thm_mme_CW_2376_augmented_hash_state_universe_card
import Theorems.Thm_mme_CW_2376_marginal_hash_retained_vertex_closed
import Theorems.Thm_mme_finite_collision_budget_averaging_real

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_CW_2376_hash_budget_select
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (L : ℝ)
    (hbudget :
      (p : ℝ) ^ (cw2376ProfileLength m + 2) * L +
          ((cw2376AllTargetAmbientCollisions m).card : ℝ) *
            (p : ℝ) ^ cw2376ProfileLength m ≤
        ((cw2376AllExactTargetEdges m).card : ℝ) *
          (S.card : ℝ) * (p : ℝ) ^ cw2376ProfileLength m) :
    ∃ q : (Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p,
      let E := cw2376RetainedEdgesAtAugmentedState m p S q
      CW2376MarginalVertexClosed E ∧
        ((cw2376TargetAmbientCollisions E).card : ℝ) + L ≤
          ((cw2376ExactTargetEdges E).card : ℝ) := by
  sorry
