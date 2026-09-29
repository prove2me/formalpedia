-- Prove2me | Theorems.Thm_EulerMascheroniInformationBridge_gammaTerm_partial_sum
-- name    : EulerMascheroniInformationBridge.gammaTerm_partial_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:44:00.355188+00:00
-- url     : https://prove2.me/theorems/556477a0-f138-4c49-af97-deb09e59b98c
-- title:
--   GammaTerm partial sum
-- statement:
--   Formal statement of `EulerMascheroniInformationBridge.gammaTerm_partial_sum` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem EulerMascheroniInformationBridge.gammaTerm_partial_sum(n : ℕ) :
--       ∑ k ∈ range n, gammaTerm k = Real.eulerMascheroniSeq n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EulerMascheroniInformationBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EulerMascheroniInformationBridge.lean#L51

-- Thm stub generated from Novelty/EulerMascheroniInformationBridge.lean
import Mathlib
import Definitions.Def_Novelty_EulerMascheroniInformationBridge

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

theorem EulerMascheroniInformationBridge.gammaTerm_partial_sum(n : ℕ) :
    ∑ k ∈ range n, gammaTerm k = Real.eulerMascheroniSeq n := by sorry
