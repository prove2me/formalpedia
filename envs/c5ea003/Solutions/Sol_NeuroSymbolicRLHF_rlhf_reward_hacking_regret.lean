-- Prove2me | solution 1 for NeuroSymbolicRLHF.rlhf_reward_hacking_regret
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:48.709426+00:00
-- url     : https://prove2.me/submissions/9c3cc65f-585a-4312-ac0e-7dc5234b4af5

-- Sol generated from Speculative/AutoResearch/RLHFHilbertIsometry.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_freeEnergy_add_const
import Theorems.Thm_NeuroSymbolicRLHF_freeEnergy_mono
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_isPosProb
import Theorems.Thm_NeuroSymbolicRLHF_rlhfObj_gibbs
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



/-- **Free energy is 1-Lipschitz in the reward (sup-norm).** -/
theorem freeEnergy_sub_le {β : ℝ} (hβ : 0 < β) {ref r₁ r₂ : ι → ℝ} {M : ℝ}
    (href : IsPosProb ref) (hM : ∀ i, |r₁ i - r₂ i| ≤ M) :
    freeEnergy β ref r₁ - freeEnergy β ref r₂ ≤ M := by
  have h1 : ∀ i, r₁ i ≤ r₂ i + M := by
    intro i
    have := (abs_le.mp (hM i)).2
    linarith
  have := freeEnergy_mono hβ href h1
  rw [freeEnergy_add_const hβ href] at this
  linarith



open NeuroSymbolicRLHF in
theorem solution{β : ℝ} (hβ : 0 < β) {ref r rhat : ι → ℝ} {M : ℝ}
    (href : IsPosProb ref) (hM : ∀ i, |r i - rhat i| ≤ M) :
    freeEnergy β ref r - rlhfObj β ref r (gibbs β ref rhat) ≤ 2 * M := by
  set q := gibbs β ref rhat with hq
  have hqprob : IsPosProb q := gibbs_isPosProb href
  -- value of the proxy-optimal policy under the proxy reward
  have hopt : rlhfObj β ref rhat q = freeEnergy β ref rhat := rlhfObj_gibbs hβ href
  -- swapping the reward inside the objective costs at most `M`
  have hswap : rlhfObj β ref rhat q - rlhfObj β ref r q ≤ M := by
    simp only [rlhfObj]
    have : ∑ i, q i * rhat i - ∑ i, q i * r i ≤ M := by
      rw [← Finset.sum_sub_distrib]
      have hle : ∀ i ∈ univ, q i * rhat i - q i * r i ≤ q i * M := by
        intro i _
        have := (abs_le.mp (hM i)).1
        nlinarith [(hqprob.pos i).le]
      calc ∑ i, (q i * rhat i - q i * r i) ≤ ∑ i, q i * M := Finset.sum_le_sum hle
        _ = M := by rw [← Finset.sum_mul, hqprob.sum_one, one_mul]
    linarith
  -- the two free energies are within `M`
  have hfe : freeEnergy β ref r - freeEnergy β ref rhat ≤ M :=
    freeEnergy_sub_le hβ href hM
  linarith [hopt, hswap, hfe]
