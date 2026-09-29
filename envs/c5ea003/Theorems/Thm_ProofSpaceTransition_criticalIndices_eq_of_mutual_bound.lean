-- Prove2me | Theorems.Thm_ProofSpaceTransition_criticalIndices_eq_of_mutual_bound
-- name    : ProofSpaceTransition.criticalIndices_eq_of_mutual_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:09:01.342293+00:00
-- url     : https://prove2.me/theorems/c52641de-32c2-487e-a51a-4caad1f11096
-- title:
--   With zero recoding distortion, the two critical indices coincide.
-- statement:
--   With zero recoding distortion, the two critical indices coincide.
--
--   ```lean
--   theorem ProofSpaceTransition.criticalIndices_eq_of_mutual_bound    (p q : ℕ → ℝ) (ε : ℝ) (cp cq : ℕ)
--       (hp : ∀ n, p n < ε ↔ cp < n)
--       (hq : ∀ n, q n < ε ↔ cq < n)
--       (hpq : ∀ n, p n ≤ q n)
--       (hqp : ∀ n, q n ≤ p n) :
--       cp = cq := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/StableProofSpaceTransitions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/StableProofSpaceTransitions.lean#L79

-- Thm stub generated from Shared/StableProofSpaceTransitions.lean
import Mathlib

/-!
# Stability of Critical Indices Under Bounded Recodings

This file develops an abstract sharp-transition theorem for real-valued order
parameters.  An antitone profile converging to zero has a unique last index at
or above every positive level that is attained initially.  Two such profiles
whose shifted values bound one another have critical indices differing by at
most the shift.  Thus a finite-distortion recoding cannot move a sharp
transition by more than its distortion bound.
-/


open Filter Topology

theorem ProofSpaceTransition.criticalIndices_eq_of_mutual_bound    (p q : ℕ → ℝ) (ε : ℝ) (cp cq : ℕ)
    (hp : ∀ n, p n < ε ↔ cp < n)
    (hq : ∀ n, q n < ε ↔ cq < n)
    (hpq : ∀ n, p n ≤ q n)
    (hqp : ∀ n, q n ≤ p n) :
    cp = cq := by sorry
