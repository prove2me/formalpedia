-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_le_exp_hilbertDist_mul
-- name    : NeuroSymbolicRLHF.le_exp_hilbertDist_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:48:25.359767+00:00
-- url     : https://prove2.me/theorems/d32b04db-107d-46cb-84ec-c6e21eaba28d
-- title:
--   A density-ratio bound: two positive probability vectors at Hilbert distance
-- statement:
--   A density-ratio bound: two positive probability vectors at Hilbert distance
--   `d` satisfy `p ≤ e^d q` pointwise.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.le_exp_hilbertDist_mul{p q : ι → ℝ} (hp : IsPosProb p) (hq : IsPosProb q) (i : ι) :
--       p i ≤ Real.exp (hilbertDist p q) * q i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/RLHFHilbertIsometry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/RLHFHilbertIsometry.lean#L226

-- Thm stub generated from Speculative/AutoResearch/RLHFHilbertIsometry.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
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

theorem NeuroSymbolicRLHF.le_exp_hilbertDist_mul{p q : ι → ℝ} (hp : IsPosProb p) (hq : IsPosProb q) (i : ι) :
    p i ≤ Real.exp (hilbertDist p q) * q i := by sorry
