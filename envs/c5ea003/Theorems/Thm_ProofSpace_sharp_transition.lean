-- Prove2me | Theorems.Thm_ProofSpace_sharp_transition
-- name    : ProofSpace.sharp_transition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:02.044792+00:00
-- url     : https://prove2.me/theorems/af12c5eb-03bb-4aef-a889-0acbadcec297
-- title:
--   Strict decrease makes the threshold a permanent sharp transition: every
-- statement:
--   Strict decrease makes the threshold a permanent sharp transition: every
--   later cutoff through `N` has negative imbalance.
--
--   ```lean
--   theorem ProofSpace.sharp_transition(f : ℕ → ℤ) (N : ℕ)
--       (hdec : ∀ n < N, f (n + 1) < f n)
--       (hN : f N ≤ 0) :
--       ∃! n, n ≤ N ∧ IsFirstThreshold f n ∧
--         ∀ m, n < m → m ≤ N → f m < 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProofSpaceTransition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProofSpaceTransition.lean#L70

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

theorem ProofSpace.sharp_transition(f : ℕ → ℤ) (N : ℕ)
    (hdec : ∀ n < N, f (n + 1) < f n)
    (hN : f N ≤ 0) :
    ∃! n, n ≤ N ∧ IsFirstThreshold f n ∧
      ∀ m, n < m → m ≤ N → f m < 0 := by sorry
