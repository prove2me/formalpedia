-- Prove2me | Theorems.Thm_ProofSpace_count_phase_transition
-- name    : ProofSpace.count_phase_transition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:07.437844+00:00
-- url     : https://prove2.me/theorems/82d261bd-ca5c-4b41-aa2c-62e9ad84b136
-- title:
--   Count formulation of the phase-transition theorem.
-- statement:
--   Count formulation of the phase-transition theorem.
--
--   ```lean
--   theorem ProofSpace.count_phase_transition(provable unprovable : ℕ → ℕ) (N : ℕ)
--       (hpositive : ∀ n ≤ N, 0 < provable n + unprovable n)
--       (hdec : ∀ n < N,
--         imbalance (provable (n + 1)) (unprovable (n + 1)) <
--           imbalance (provable n) (unprovable n))
--       (hend : provable N ≤ unprovable N) :
--       ∃! n, n ≤ N ∧
--         orderParameter (provable n) (unprovable n) ≤ (1 / 2 : ℚ) ∧
--         (∀ m < n, (1 / 2 : ℚ) < orderParameter (provable m) (unprovable m)) ∧
--         ∀ m, n < m → m ≤ N →
--           orderParameter (provable m) (unprovable m) < (1 / 2 : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProofSpaceTransition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProofSpaceTransition.lean#L125

-- Thm stub generated from Logic/ProofSpaceTransition.lean
import Mathlib
import Definitions.Def_Logic_ProofSpaceTransition

/-!
# A discrete Gödel threshold in finite proof space

This file gives a precise finite model of the proposed phase-transition picture.
At cutoff `n`, `provable n` and `unprovable n` count the two classes of statements
seen so far.  Their difference is the signed order parameter.  The main theorem
shows that, whenever this difference starts positive and ends nonpositive, there
is a unique first cutoff at which the provable majority disappears.  Under a
strict-decrease hypothesis, the sign change is permanent and its location is
unique.

This is deliberately a theorem about an abstract enumeration: incompleteness
alone does not imply any particular asymptotic density or power law without a
choice of syntax, length function, and probability measure.
-/

open ProofSpace

theorem ProofSpace.count_phase_transition(provable unprovable : ℕ → ℕ) (N : ℕ)
    (hpositive : ∀ n ≤ N, 0 < provable n + unprovable n)
    (hdec : ∀ n < N,
      imbalance (provable (n + 1)) (unprovable (n + 1)) <
        imbalance (provable n) (unprovable n))
    (hend : provable N ≤ unprovable N) :
    ∃! n, n ≤ N ∧
      orderParameter (provable n) (unprovable n) ≤ (1 / 2 : ℚ) ∧
      (∀ m < n, (1 / 2 : ℚ) < orderParameter (provable m) (unprovable m)) ∧
      ∀ m, n < m → m ≤ N →
        orderParameter (provable m) (unprovable m) < (1 / 2 : ℚ) := by sorry
