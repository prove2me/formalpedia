-- Prove2me | solution 1 for NeuroSymbolicRLHF.hilbertDist_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:26:53.184447+00:00
-- url     : https://prove2.me/submissions/215ffbcd-d236-4c73-886b-ae10121d51a8

-- Sol generated from Speculative/AutoResearch/RLHFHilbertIsometry.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_oscil_add_const
import Theorems.Thm_NeuroSymbolicRLHF_oscil_const_mul
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




/-- Pointwise log-ratio of two tilted policies: the reward difference divided by
`β`, plus a constant (the log ratio of partition functions). -/
theorem log_gibbs_ratio {β : ℝ} {ref r₁ r₂ : ι → ℝ} (href : IsPosProb ref) (i : ι) :
    Real.log (gibbs β ref r₁ i / gibbs β ref r₂ i)
      = (r₁ i - r₂ i) / β + Real.log (tiltZ β ref r₂ / tiltZ β ref r₁) := by
  have hZ1 : 0 < tiltZ β ref r₁ := tiltZ_pos href
  have hZ2 : 0 < tiltZ β ref r₂ := tiltZ_pos href
  have hri : 0 < ref i := href.pos i
  have hkey : gibbs β ref r₁ i / gibbs β ref r₂ i
      = Real.exp ((r₁ i - r₂ i) / β) * (tiltZ β ref r₂ / tiltZ β ref r₁) := by
    have he1 : Real.exp (r₁ i / β) ≠ 0 := (Real.exp_pos _).ne'
    have he2 : Real.exp (r₂ i / β) ≠ 0 := (Real.exp_pos _).ne'
    simp only [gibbs, sub_div, Real.exp_sub]
    field_simp
  rw [hkey, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]




/-! ## Level 2: from the Hilbert metric to total variation -/






/-! ## Level 3: Goodhart / reward-hacking regret -/






open NeuroSymbolicRLHF in
theorem solution{β : ℝ} (hβ : 0 < β) {ref r₁ r₂ : ι → ℝ} (href : IsPosProb ref) :
    hilbertDist (gibbs β ref r₁) (gibbs β ref r₂) = oscil (fun i => r₁ i - r₂ i) / β := by
  have hfun : (fun i => Real.log (gibbs β ref r₁ i / gibbs β ref r₂ i))
      = fun i => (1 / β) * (r₁ i - r₂ i) + Real.log (tiltZ β ref r₂ / tiltZ β ref r₁) := by
    funext i
    rw [log_gibbs_ratio href i]
    ring_nf
  simp only [hilbertDist, hfun]
  rw [oscil_add_const, oscil_const_mul (by positivity)]
  ring
