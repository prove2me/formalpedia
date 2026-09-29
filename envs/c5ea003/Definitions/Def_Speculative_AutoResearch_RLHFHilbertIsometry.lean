-- Prove2me | Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
-- name    : Speculative_AutoResearch_RLHFHilbertIsometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:58.385089+00:00
-- url     : https://prove2.me/theorems/22daa841-e1a9-4e10-8398-28df576855f8
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_RLHFHilbertIsometry
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.RLHFHilbertIsometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/RLHFHilbertIsometry.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
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

namespace NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Level 0: the oscillation seminorm -/

/-- The oscillation (range) seminorm `max f - min f` of a function on a finite
nonempty type.  It vanishes exactly on the constants, and is the natural norm
on the quotient `ℝ^ι / ℝ·1` of rewards modulo additive constants. -/
def oscil (f : ι → ℝ) : ℝ :=
  (univ.sup' univ_nonempty f) - (univ.inf' univ_nonempty f)








/-! ## Level 1: the Hilbert projective metric and the tilt isometry -/

/-- The Hilbert projective (Birkhoff) distance between two positive vectors:
the oscillation of the log-likelihood ratio. -/
def hilbertDist (p q : ι → ℝ) : ℝ := oscil (fun i => Real.log (p i / q i))







/-! ## Level 2: from the Hilbert metric to total variation -/

/-- Total variation distance between two finite probability vectors. -/
def tvDist (p q : ι → ℝ) : ℝ := (∑ i, |p i - q i|) / 2





/-! ## Level 3: Goodhart / reward-hacking regret -/





end NeuroSymbolicRLHF


