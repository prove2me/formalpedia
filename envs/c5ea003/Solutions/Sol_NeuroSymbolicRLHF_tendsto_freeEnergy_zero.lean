-- Prove2me | solution 1 for NeuroSymbolicRLHF.tendsto_freeEnergy_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:49.800676+00:00
-- url     : https://prove2.me/submissions/852d09f4-e183-49b4-a573-5be090102219

-- Sol generated from Speculative/AutoResearch/RLHFFreeEnergyDuality.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_freeEnergy_ge_max_add
import Theorems.Thm_NeuroSymbolicRLHF_freeEnergy_le_max
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
theorem solution{ref r : ι → ℝ} (href : IsPosProb ref) :
    Tendsto (fun β : ℝ => freeEnergy β ref r) (𝓝[>] (0 : ℝ))
      (𝓝 (univ.sup' univ_nonempty r)) := by
  set Mx := univ.sup' univ_nonempty r
  set L := Real.log (univ.inf' univ_nonempty ref)
  have hg : Tendsto (fun β : ℝ => Mx + β * L) (𝓝[>] (0 : ℝ)) (𝓝 Mx) := by
    have : Tendsto (fun β : ℝ => Mx + β * L) (𝓝 (0 : ℝ)) (𝓝 (Mx + 0 * L)) := by
      exact tendsto_const_nhds.add (Filter.Tendsto.mul_const L tendsto_id)
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact freeEnergy_ge_max_add hβ href
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact freeEnergy_le_max hβ href
