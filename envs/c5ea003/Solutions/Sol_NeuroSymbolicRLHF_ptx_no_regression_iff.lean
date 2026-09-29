-- Prove2me | solution 1 for NeuroSymbolicRLHF.ptx_no_regression_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:33:42.068965+00:00
-- url     : https://prove2.me/submissions/f9c6181a-c31a-47bc-8a48-a0ee9755cb20

-- Sol generated from Speculative/AutoResearch/RLHFFreeEnergyDuality.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_ptx_at_gibbs
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
theorem solution{β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) {ref r pre : ι → ℝ}
    (href : IsPosProb ref) (hpre : IsProb pre) :
    ptxTerm γ pre ref ≤ ptxTerm γ pre (gibbs β ref r)
      ↔ freeEnergy β ref r ≤ ∑ i, pre i * r i := by
  have hid := ptx_at_gibbs (r := r) hβ href hpre
  have hstep : ptxTerm γ pre (gibbs β ref r) - ptxTerm γ pre ref
      = γ * (((∑ i, pre i * r i) - freeEnergy β ref r) / β) := by
    simp only [ptxTerm]
    rw [hid]
    ring
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hneg : ((∑ i, pre i * r i) - freeEnergy β ref r) / β < 0 :=
      div_neg_of_neg_of_pos (by linarith) hβ
    have hmul := mul_neg_of_pos_of_neg hγ hneg
    rw [← hstep] at hmul
    linarith
  · intro h
    have h1 : 0 ≤ ((∑ i, pre i * r i) - freeEnergy β ref r) / β :=
      div_nonneg (by linarith) hβ.le
    have hmul := mul_nonneg hγ.le h1
    rw [← hstep] at hmul
    linarith
