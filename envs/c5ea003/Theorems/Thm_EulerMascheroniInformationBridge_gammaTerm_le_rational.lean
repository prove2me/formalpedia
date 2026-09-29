-- Prove2me | Theorems.Thm_EulerMascheroniInformationBridge_gammaTerm_le_rational
-- name    : EulerMascheroniInformationBridge.gammaTerm_le_rational
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:33:37.619987+00:00
-- url     : https://prove2.me/theorems/02e5580e-a3cd-4456-9186-c9228498b622
-- title:
--   A rational `O(kâ»Â²)` majorant for the `k`-th EulerâMascheroni summand.
-- statement:
--   A rational `O(kâ»Â²)` majorant for the `k`-th EulerâMascheroni summand.
--
--   ```lean
--   theorem EulerMascheroniInformationBridge.gammaTerm_le_rational(k : ℕ) :
--       gammaTerm k ≤ 1 / ((k + 1 : ℝ) * (2 * k + 3)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/EulerMascheroniInformationBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/EulerMascheroniInformationBridge.lean#L133

-- Thm stub generated from Shared/EulerMascheroniInformationBridge.lean
import Mathlib
import Definitions.Def_Shared_EulerMascheroniInformationBridge

/-!
# Euler–Mascheroni constant as accumulated information divergence

This file connects analytic number theory with information theory.  For positive
rates `λ` and `μ`, the Kullback–Leibler divergence from an exponential law of rate
`λ` to one of rate `μ` has the closed form

`log (λ / μ) + μ / λ - 1`.

At the consecutive integer rates `λ = k+1`, `μ = k+2`, this is exactly the
`k`-th nonnegative summand in the classical series for the Euler–Mascheroni
constant.  Consequently, `γ` is the accumulated KL divergence along the chain
of exponential distributions with rates `1, 2, 3, ...`.
-/

open Real Filter Finset Topology

open EulerMascheroniInformationBridge

theorem EulerMascheroniInformationBridge.gammaTerm_le_rational(k : ℕ) :
    gammaTerm k ≤ 1 / ((k + 1 : ℝ) * (2 * k + 3)) := by sorry
