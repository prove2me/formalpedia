-- Prove2me | solution 1 for NeuroSymbolicRLHF.hasDerivAt_tiltZ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:24:09.186545+00:00
-- url     : https://prove2.me/submissions/dea80795-75d9-4b69-b4e7-a187d6be4197

-- Sol generated from Speculative/AutoResearch/RLHFFreeEnergyDuality.lean
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







/-! ## Level C: the exact PTX regression law -/





open NeuroSymbolicRLHF in
omit [Nonempty ι] in
theorem solution(β : ℝ) (ref r s : ι → ℝ) :
    HasDerivAt (fun t : ℝ => tiltZ β ref (fun i => r i + t * s i))
      (∑ i, ref i * Real.exp (r i / β) * (s i / β)) 0 := by
  have hterm : ∀ i ∈ (univ : Finset ι),
      HasDerivAt (fun t : ℝ => ref i * Real.exp ((r i + t * s i) / β))
        (ref i * Real.exp (r i / β) * (s i / β)) 0 := by
    intro i _
    have h1 : HasDerivAt (fun t : ℝ => (r i + t * s i) / β) (s i / β) 0 := by
      have h0 : HasDerivAt (fun t : ℝ => r i + t * s i) (s i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (s i)).const_add (r i)
      simpa using h0.div_const β
    have h2 := (h1.exp).const_mul (ref i)
    simpa [← mul_assoc] using h2
  have hsum := HasDerivAt.sum hterm
  have hfun : (∑ i : ι, fun t : ℝ => ref i * Real.exp ((r i + t * s i) / β))
      = fun t : ℝ => tiltZ β ref (fun i => r i + t * s i) := by
    funext t
    simp [tiltZ, Finset.sum_apply]
  rwa [hfun] at hsum
