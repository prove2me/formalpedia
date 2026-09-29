-- Prove2me | solution 1 for NeuroSymbolicRLHF.tendsto_freeEnergy_atTop
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:49.321739+00:00
-- url     : https://prove2.me/submissions/7a05c00b-997d-4b2c-8809-9bbfedd944c7

-- Sol generated from Speculative/AutoResearch/RLHFFreeEnergyDuality.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_expected_ref_le_freeEnergy
import Theorems.Thm_NeuroSymbolicRLHF_freeEnergy_sub_expected_le
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







/-! ## Level C: the exact PTX regression law -/





open NeuroSymbolicRLHF in
theorem solution{M : ℝ} {ref r : ι → ℝ} (href : IsPosProb ref)
    (hM : ∀ i, |r i| ≤ M) (hMpos : 0 < M) :
    Tendsto (fun β : ℝ => freeEnergy β ref r) atTop (𝓝 (∑ i, ref i * r i)) := by
  set A := ∑ i, ref i * r i
  have hupper : Tendsto (fun β : ℝ => A + (3 / 4) * M ^ 2 / β) atTop (𝓝 A) := by
    have : Tendsto (fun β : ℝ => (3 / 4) * M ^ 2 / β) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using tendsto_const_nhds.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact expected_ref_le_freeEnergy hβ href
  · filter_upwards [eventually_ge_atTop M] with β hβ
    have := freeEnergy_sub_expected_le href hM hMpos hβ
    linarith
