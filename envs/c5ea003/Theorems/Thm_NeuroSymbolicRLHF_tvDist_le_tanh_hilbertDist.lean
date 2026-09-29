-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_tvDist_le_tanh_hilbertDist
-- name    : NeuroSymbolicRLHF.tvDist_le_tanh_hilbertDist
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:49:32.559617+00:00
-- url     : https://prove2.me/theorems/4966ad43-bd0d-4ed8-93fc-bf6710f071f8
-- title:
--   Sharp Hilbert → total variation comparison.
-- statement:
--   **Sharp Hilbert → total variation comparison.**  For positive probability
--   vectors, `‖p - q‖_TV ≤ (e^{d/2} - 1)/(e^{d/2} + 1) = tanh (d/4)`, where
--   `d = d_H(p, q)`.  Unlike `tvDist_le_expm1_hilbertDist`, this bound is always
--   smaller than `1`.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.tvDist_le_tanh_hilbertDist{p q : ι → ℝ} (hp : IsPosProb p) (hq : IsPosProb q) :
--       tvDist p q
--         ≤ (Real.exp (hilbertDist p q / 2) - 1) / (Real.exp (hilbertDist p q / 2) + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/RLHFBirkhoffTV.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/RLHFBirkhoffTV.lean#L73

-- Thm stub generated from Speculative/AutoResearch/RLHFBirkhoffTV.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
/-
# The sharp Hilbert → total-variation bound for aligned policies

Fifth file of the neurosymbolic RLHF thread.  `RLHFHilbertIsometry.lean` proves
the crude comparison `‖p - q‖_TV ≤ e^{d_H(p,q)} - 1`, which is useless once
`d_H > log 2` because it exceeds the trivial bound `1`.  Here we prove the
*sharp* Birkhoff-type comparison

  `‖p - q‖_TV ≤ (e^{d/2} - 1) / (e^{d/2} + 1) = tanh (d_H(p,q) / 4)`,

which is always `< 1`, and combine it with the tilt isometry to obtain the
final reward-model-misspecification bound

  `‖π_β(r₁) - π_β(r₂)‖_TV ≤ tanh (oscil (r₁ - r₂) / (4β))`.

The proof is a genuine optimisation: writing `u = e^{sup log(p/q)}`,
`v = e^{inf log(p/q)}` and splitting the space at `{p ≥ q}`, the total variation
obeys the two linear constraints `a ≤ u x` and `1 - a ≥ v (1 - x)`; eliminating
`x` gives `TV ≤ (u-1)(1-v)/((u-1)+(1-v))`, and the extremal analysis reduces to
the single square `(v w - 1)² ≥ 0` where `w² = u / v`.  That square is the exact
reason the constant is `tanh(d/4)`.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem NeuroSymbolicRLHF.tvDist_le_tanh_hilbertDist{p q : ι → ℝ} (hp : IsPosProb p) (hq : IsPosProb q) :
    tvDist p q
      ≤ (Real.exp (hilbertDist p q / 2) - 1) / (Real.exp (hilbertDist p q / 2) + 1) := by sorry
