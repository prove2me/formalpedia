-- Prove2me | Theorems.Thm_Bridges_AttentionKneeEntropyBound_uniform_l2_bound
-- name    : Bridges.AttentionKneeEntropyBound.uniform_l2_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:21:06.318744+00:00
-- url     : https://prove2.me/theorems/6b8d4c98-6f0b-4c11-86d9-96f80c8a71d8
-- title:
--   And the `ℓ²` bound really does apply to the uniform profile, giving
-- statement:
--   And the `ℓ²` bound really does apply to the uniform profile, giving
--   `g² n ≤ k*`, weaker than the truth `g n ≤ k*` by the factor `g`.
--
--   ```lean
--   theorem Bridges.AttentionKneeEntropyBound.uniform_l2_bound{n : ℕ} {g : ℝ} (hn : 0 < n) (hg : 0 ≤ g)
--       (hex : ∃ k, g ≤ mass (stepProfile n (1 / n)) k) :
--       g ^ 2 * n ≤ (knee (stepProfile n (1 / n)) g : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AttentionKneeEntropyBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AttentionKneeEntropyBound.lean#L164

-- Thm stub generated from Bridges/AttentionKneeEntropyBound.lean
import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeGeometry
/-
  # Cycle 2: the retention knee is bounded *below* by Rényi-2 (collision) entropy

  `Bridges.AttentionKneeGeometry` established the order-theoretic side of the
  retention knee (grids, majorization, geometric upper budgets).  That side is
  one-directional: it can only certify that `k` keys *suffice*.  This module
  supplies the converse — an **information-theoretic lower bound** on the knee,
  obtained from Cauchy–Schwarz (Chebyshev's sum inequality) rather than from any
  ordering assumption:

      `g ≤ mass w k  ⟹  g² ≤ k · E_k`   (`sq_gate_le_card_mul_energy`)

  where `E_k = ∑_{i<k} (w i)²` is the *attention energy* of those keys — the
  collision probability, i.e. `2^{-H₂}` for a probability profile.  Hence

      `k*(g) ≥ g² / E`   (`knee_ge_gate_sq_div_energy`).

  What is proved here:

  * `energy_ge_of_knee_le`: read backwards, a *measured* knee is a hard upper
    bound on the Rényi-2 entropy of the attention row.  Applied to the NET-63
    round-16 reading (`net63_energy_lower_bound`): any nonnegative profile whose
    knee at gate `0.98` is at most `24` must have energy `≥ 0.9604/24 > 0.04`,
    i.e. collision entropy `H₂ ≤ log₂(24/0.9604) < 4.65` bits.  This is a
    falsifiable prediction about the measured rows, not a restatement of the
    sweep.
  * `knee_ge_of_max_weight`: the cruder `ℓ^∞` bound `k*(g) ≥ g / M`.
  * `uniform_knee_lower_bound` / `uniform_energy`: on the uniform profile over
    `n` keys the `ℓ²` bound `g²n` is tight up to exactly one factor of the gate
    (the truth is `g n`), so the constant in the bound cannot be improved by
    more than `1/g`.
  * `knee_sandwich` and `budget_energy_consistency`: combining with the
    geometric-tail budget of cycle 1, any reported triple (knee, energy, tail
    constants) must satisfy `g²/E ≤ N` — a consistency test on the experiment.
-/


open Bridges.AttentionKneeEntropyBound

open Finset Bridges.AttentionKneeGeometry



/-! ## 1. Cauchy–Schwarz: mass cannot outrun energy -/




/-! ## 2. The NET-63 prediction -/


/-! ## 3. The `ℓ^∞` bound, and tightness of the `ℓ²` bound -/

theorem Bridges.AttentionKneeEntropyBound.uniform_l2_bound{n : ℕ} {g : ℝ} (hn : 0 < n) (hg : 0 ≤ g)
    (hex : ∃ k, g ≤ mass (stepProfile n (1 / n)) k) :
    g ^ 2 * n ≤ (knee (stepProfile n (1 / n)) g : ℝ) := by sorry
