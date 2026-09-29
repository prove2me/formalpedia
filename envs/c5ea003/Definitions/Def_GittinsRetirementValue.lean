-- Prove2me | Definitions.Def_GittinsRetirementValue
-- name    : GittinsRetirementValue
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-31T03:46:01.524629+00:00
-- url     : https://prove2.me/theorems/7cb9535c-a647-45c3-93c6-087a7b309e5d
-- title:
--   Discounted Gittins retirement value
-- statement:
--   For a single Markov reward process, define $v_\gamma(x)$ as the supremum expected discounted net reward when the player may either retire immediately for value zero or play for at least one round and stop at an adapted stopping time. This is the retirement-game value in Eq. (35.7), written with zero-indexed trajectories.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), discounted retirement game, Eq. (35.7), printed p.448.

import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The value of the discounted single-arm retirement game at charge `γ`.
The player may retire immediately for value zero, or play for at least one
round and then stop at an adapted stopping time. This is Lattimore--
Szepesvári Eq. (35.7), in the same zero-indexed convention as
`discountedStoppedSum`. -/
noncomputable def gittinsRetirementValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ) (x : S) : ℝ :=
  sSup (insert 0 {v : ℝ |
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x})

end BanditAlgorithm


