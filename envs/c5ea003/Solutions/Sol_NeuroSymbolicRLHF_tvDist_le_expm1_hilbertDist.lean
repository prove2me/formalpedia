-- Prove2me | solution 1 for NeuroSymbolicRLHF.tvDist_le_expm1_hilbertDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:50.255162+00:00
-- url     : https://prove2.me/submissions/cd468378-0f53-48fb-947e-5fa884a9215c

-- Sol generated from Speculative/AutoResearch/RLHFHilbertIsometry.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_hilbertDist_nonneg
import Theorems.Thm_NeuroSymbolicRLHF_le_exp_hilbertDist_mul
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
theorem solution{p q : ι → ℝ} (hp : IsPosProb p) (hq : IsPosProb q) :
    tvDist p q ≤ Real.exp (hilbertDist p q) - 1 := by
  set d := hilbertDist p q with hd
  have hd0 : 0 ≤ d := hilbertDist_nonneg p q
  have hexp1 : 1 ≤ Real.exp d := Real.one_le_exp hd0
  have hpt : ∀ i, |p i - q i| ≤ 2 * ((Real.exp d - 1) * q i) - (p i - q i) := by
    intro i
    have hle : p i ≤ Real.exp d * q i := le_exp_hilbertDist_mul hp hq i
    rcases le_or_gt (p i) (q i) with h | h
    · rw [abs_of_nonpos (by linarith)]
      have : 0 ≤ (Real.exp d - 1) * q i := by
        have := (hq.pos i).le
        nlinarith
      linarith
    · rw [abs_of_nonneg (by linarith)]
      nlinarith
  have hsum : ∑ i, |p i - q i| ≤ ∑ i, (2 * ((Real.exp d - 1) * q i) - (p i - q i)) :=
    Finset.sum_le_sum fun i _ => hpt i
  have hrhs : ∑ i, (2 * ((Real.exp d - 1) * q i) - (p i - q i))
      = 2 * (Real.exp d - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hp.sum_one, hq.sum_one]
    ring
  rw [hrhs] at hsum
  simp only [tvDist]
  linarith
