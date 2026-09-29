-- Prove2me | solution 1 for NeuroSymbolicRLHF.ptx_at_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:31:50.137934+00:00
-- url     : https://prove2.me/submissions/80077dd9-6981-4f8a-8464-e023890c8238

-- Sol generated from Speculative/AutoResearch/RLHFFreeEnergyDuality.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_tiltZ_pos
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
theorem solution{β : ℝ} (hβ : 0 < β) {ref r pre : ι → ℝ} (href : IsPosProb ref)
    (hpre : IsProb pre) :
    ∑ i, pre i * Real.log (gibbs β ref r i)
      = (∑ i, pre i * Real.log (ref i)) + ((∑ i, pre i * r i) - freeEnergy β ref r) / β := by
  have hZ : 0 < tiltZ β ref r := tiltZ_pos href
  have hlog : ∀ i, Real.log (gibbs β ref r i)
      = Real.log (ref i) + r i / β - Real.log (tiltZ β ref r) := by
    intro i
    simp only [gibbs]
    rw [Real.log_div (mul_pos (href.pos i) (Real.exp_pos _)).ne' hZ.ne',
      Real.log_mul (href.pos i).ne' (Real.exp_pos _).ne', Real.log_exp]
  have hF : Real.log (tiltZ β ref r) = freeEnergy β ref r / β := by
    simp only [freeEnergy]
    field_simp
  calc ∑ i, pre i * Real.log (gibbs β ref r i)
      = ∑ i, (pre i * Real.log (ref i) + pre i * (r i / β)
          - pre i * Real.log (tiltZ β ref r)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hlog i]; ring
    _ = (∑ i, pre i * Real.log (ref i)) + (∑ i, pre i * r i) / β
          - Real.log (tiltZ β ref r) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hpre.sum_one,
          one_mul]
        have : ∑ i, pre i * (r i / β) = (∑ i, pre i * r i) / β := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this]
    _ = (∑ i, pre i * Real.log (ref i)) + ((∑ i, pre i * r i) - freeEnergy β ref r) / β := by
        rw [hF]; ring
