-- Prove2me | solution 1 for NeuroSymbolicRLHF.freeEnergy_add_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:12:33.189816+00:00
-- url     : https://prove2.me/submissions/fdd6dad7-29c0-4869-b30f-a7918732ac88

-- Sol generated from Speculative/AutoResearch/RLHFHilbertIsometry.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_tiltZ_pos
/-
# RLHF as an isometry of the Hilbert projective metric

This file continues the neurosymbolic RLHF / PPO-ptx research thread of
`Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean`, whose definitions
(`tiltZ`, `gibbs`, `freeEnergy`, `rlhfObj`, `klDivFin`) are reused verbatim.

The InstructGPT objective

  `Objective(p) = 𝔼_p[RM] - β · KL(p ‖ p_SFT) + γ · 𝔼_{pre}[log p]`

has, for `γ = 0`, the exponentially tilted maximiser `gibbs β ref r`.  The
catalog already knows that tilting is a *transitive group action* of the reward
space on the open simplex (a torsor structure).  Here we upgrade that algebraic
statement to a **metric** one, bridging information theory with the projective
geometry of Birkhoff and Hilbert:

* **Level 0.** Elementary theory of the oscillation seminorm
  `oscil f = max f - min f` (translation invariance, positive homogeneity,
  comparison with the sup-norm).
* **Level 1 (main theorem, `hilbertDist_gibbs`).**  The tilt map is an *exact
  isometry*, with scale factor `1/β`:
  `d_H (π_β(r₁), π_β(r₂)) = oscil (r₁ - r₂) / β`.
  In particular the RLHF torsor action of `(ℝ^ι/ℝ·1, oscil)` on the open
  simplex equipped with the Hilbert projective metric is by isometries, and
  `d_H (π_β(r), ref) = oscil r / β`.
* **Level 2 (`tvDist_le_expm1_hilbertDist`).**  A Hilbert-metric bound controls
  total variation, giving the quantitative reward-model-misspecification bound
  `‖π_β(r₁) - π_β(r₂)‖_TV ≤ exp(oscil (r₁ - r₂)/β) - 1`:
  KL-regularisation with large `β` makes the aligned policy insensitive to
  reward-model error.
* **Level 3 (`rlhf_reward_hacking_regret`).**  Optimising a *proxy* reward `r̂`
  loses at most `2‖r - r̂‖_∞` of the true KL-regularised value — an explicit
  reward-hacking (Goodhart) bound.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Level 0: the oscillation seminorm -/









/-! ## Level 1: the Hilbert projective metric and the tilt isometry -/








/-! ## Level 2: from the Hilbert metric to total variation -/






/-! ## Level 3: Goodhart / reward-hacking regret -/






open NeuroSymbolicRLHF in
theorem solution{β : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} (href : IsPosProb ref) (c : ℝ) :
    freeEnergy β ref (fun i => r i + c) = freeEnergy β ref r + c := by
  have hZ : tiltZ β ref (fun i => r i + c) = Real.exp (c / β) * tiltZ β ref r := by
    simp only [tiltZ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_div, Real.exp_add]
    ring
  have hZpos : 0 < tiltZ β ref r := tiltZ_pos href
  simp only [freeEnergy, hZ]
  rw [Real.log_mul (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  field_simp
  ring
