-- Prove2me | Definitions.Def_Bridges_AttentionKneeEntropyBound
-- name    : Bridges_AttentionKneeEntropyBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:52.257237+00:00
-- url     : https://prove2.me/theorems/ae473e75-d89f-479a-b553-cd46e8d11038
-- title:
--   Aether Catalog definitions — Bridges_AttentionKneeEntropyBound
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AttentionKneeEntropyBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AttentionKneeEntropyBound.lean by skeleton subtraction
import Mathlib
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


namespace Bridges.AttentionKneeEntropyBound

open Finset Bridges.AttentionKneeGeometry

/-- The **attention energy** (collision probability) of the first `k` keys. -/
def energy (w : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, (w i) ^ 2


/-! ## 1. Cauchy–Schwarz: mass cannot outrun energy -/




/-! ## 2. The NET-63 prediction -/


/-! ## 3. The `ℓ^∞` bound, and tightness of the `ℓ²` bound -/







/-! ## 4. Sandwiching the knee, and a consistency test for the experiment -/



/-!
## Lab Notes (cycle 2)

* Numerical instance of the entropy floor: gate `g = 0.98`, measured knee
  `K = 24` gives `E ≥ 0.98²/24 = 0.0400166…`, hence `H₂ ≤ log₂(1/0.04) ≈ 4.64`
  bits.  Formalised (in the strict form `E > 0.04`) as
  `net63_energy_lower_bound`.
* Tightness check on the uniform profile over `n` keys: energy `1/n`
  (`uniform_energy`), true knee `≥ g n` (`uniform_knee_lower_bound`), `ℓ²`
  floor `g² n` (`uniform_l2_bound`).  Ratio of truth to bound: exactly `1/g`,
  i.e. `1.0204` at `g = 0.98` — the floor is essentially sharp at high gates.
* Consistency of the deployment table: with `N = 30` the test
  `g²/E ≤ N` requires `E ≥ 0.032`; the round-16 numbers satisfy it with room to
  spare.
-/

end Bridges.AttentionKneeEntropyBound


