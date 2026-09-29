-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_freeEnergy_ge_max_add
-- name    : NeuroSymbolicRLHF.freeEnergy_ge_max_add
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:46:10.229982+00:00
-- url     : https://prove2.me/theorems/2d28794d-0bb6-4ef4-90e8-7abd984f4273
-- title:
--   Zero-temperature lower bound: the free energy is within `β log (min ref)` of
-- statement:
--   Zero-temperature lower bound: the free energy is within `β log (min ref)` of
--   the maximal reward.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.freeEnergy_ge_max_add{β : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} (href : IsPosProb ref) :
--       (univ.sup' univ_nonempty r) + β * Real.log (univ.inf' univ_nonempty ref)
--         ≤ freeEnergy β ref r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/NeuroSymbolicRLHFPareto.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/NeuroSymbolicRLHFPareto.lean#L73

-- Thm stub generated from Speculative/AutoResearch/RLHFFreeEnergyDuality.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
/-
# Free-energy duality, annealing limits, and the exact PTX regression law

Second file of the neurosymbolic RLHF thread.  It builds on the catalog
definitions of `Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean`
(`tiltZ`, `gibbs`, `freeEnergy`, `rlhfObj`, `ptxTerm`) and on the oscillation
seminorm `oscil` introduced in `MachineLearning/RLHFHilbertIsometry.lean`.

Three independent layers, all about the *value function*
`F(β, r) = β log Z = max_p [𝔼_p r - β KL(p ‖ ref)]` of the InstructGPT
objective:

* **Level A — Legendre / Danskin duality (`hasDerivAt_freeEnergy`).**
  The directional derivative of the free energy with respect to the reward is
  the expectation of the direction under the *optimal* (tilted) policy:
  `d/dt|₀ F(β, r + t s) = 𝔼_{π_β(r)}[s]`.
  So the aligned policy is literally the gradient of the alignment value —
  an envelope theorem for RLHF.

* **Level B — annealing (thermodynamic limits).**
  Zero temperature: `max r + β log (min ref) ≤ F(β,r) ≤ max r`, hence
  `F(β,r) → max r` as `β → 0⁺` (reward maximisation, policy collapse).
  Infinite temperature: `0 ≤ F(β,r) - 𝔼_ref[r] ≤ (3/4)‖r‖_∞²/β` for
  `β ≥ ‖r‖_∞`, hence `F(β,r) → 𝔼_ref[r]` as `β → ∞` (the SFT model).
  Both limits come with explicit rates.

* **Level C — the exact PTX regression law (`ptx_at_gibbs`).**
  Evaluating the pre-training mix-in at the aligned policy gives the *identity*
  `𝔼_pre[log π_β(r)] = 𝔼_pre[log ref] + (𝔼_pre[r] - F(β,r))/β`.
  Hence RLHF regresses on the pre-training distribution exactly when the
  pre-training data scores below the free-energy level, and the regression is
  never worse than `γ · oscil r / β` — the same `1/β` scale that governs the
  Hilbert-metric drift of the policy itself.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators Filter Topology

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Level A: the free energy is the potential of the aligned policy -/



/-! ## Level B: annealing limits with explicit rates -/

theorem NeuroSymbolicRLHF.freeEnergy_ge_max_add{β : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} (href : IsPosProb ref) :
    (univ.sup' univ_nonempty r) + β * Real.log (univ.inf' univ_nonempty ref)
      ≤ freeEnergy β ref r := by sorry
