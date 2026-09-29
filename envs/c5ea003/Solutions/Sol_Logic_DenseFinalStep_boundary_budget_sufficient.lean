-- Prove2me | solution 1 for Logic.DenseFinalStep.boundary_budget_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:55:07.267893+00:00
-- url     : https://prove2.me/submissions/93efe175-d907-4810-97f6-69802fbe5306

-- Sol generated from Logic/DenseFinalStepBoundaryConditioning.lean
import Mathlib
import Definitions.Def_Logic_DenseFinalStepBoundaryConditioning
/-
# NET-25 / Catalog·Logic — Dense final-step (EOS) inputs: expressivity-invariance and gain

Formal counterpart of the *boundary half* of the NET-25 law
**DENSE-FINAL-STEP-IS-THE-CURE**.

The decisive experimental control of round-net-25 compared two recurrent answer
paths whose cell and head weights are **byte-identical for a fixed seed**, and
which differ in exactly one architectural variable: the dimension `d` of the
learned end-of-sequence (EOS) vector that is fed at the *final carry step*.

| arm                | EOS dim `d` | params  | n=8 full        |
|--------------------|-------------|---------|-----------------|
| `pad384`  s0..s3   | 384         | 335,242 | 1.0000 × 4      |
| `pad384-zeroEOS`   | 20          | 334,878 | 0.7441 / 0.0259 |
| `pos28`   s0/s1    | 28          | 129,830 | 0.0049 / 0.0049 |
| `raw20-192` s0..s6 | 20          | 125,214 | 0.0806 … 0.0020 |

Since the EOS token is a *single learned vector* `e ∈ ℝ^d`, its whole effect on
the cell is the vector `W e ∈ ℝ^h`, where `W` is the (already present) input
matrix restricted to the EOS columns.  This file proves the two facts that
together turn the empirical law into a mechanism statement.

* **Expressivity invariance** (`boundaryBias_surjective`,
  `boundaryBias_range_eq`, `eos_dimension_no_expressivity_gain`):
  for every `d ≥ 1` the reachable set of boundary contributions is *all* of
  `ℝ^h`.  Widening the EOS from 20 to 384 dimensions adds **no** representable
  function.  Hence the measured flip `0.0259 → 1.0000` is provably *not* a
  capacity/expressivity effect — exactly as the identical-weights control
  suggested, and this refutes any capacity-based reading (H1) at the level of
  the boundary pathway.
* **Gain / conditioning** (`boundaryDrift_eq`, `inner_boundaryDrift`,
  `boundary_gain_ge`, `boundary_gain_ge_card`, `boundary_gain_strict_mono_dim`):
  the *dynamics* are not invariant.  Under gradient flow on the factorised
  parameterisation `v = W e`, the induced velocity of the effective boundary
  bias `v` is `v̇ = -(‖e‖² • g + W Wᵀ g)`, i.e. the update is preconditioned by
  the PSD matrix `‖e‖² I + W Wᵀ`.  With per-coordinate initialisation scale `c`
  the gain is at least `d · c² · ‖g‖²`: **linear in the EOS dimension**.

Conclusion, formally: EOS width is invisible to the function class and visible
to the optimiser.  That is precisely the "boundary-step backprop conditioning"
mechanism hypothesis of the paper, here proved at the level of the induced
gradient flow (the remaining, unproven, step is that this gain is what keeps the
digit readout in-distribution at depth).

Companion file: `Logic.DenseFinalStepCarryChain` (transition half).
-/


open Logic.DenseFinalStep

open Finset Matrix

variable {h d : ℕ}

/-! ## The effective boundary bias -/





/-! ## Gradient flow on the factorised boundary bias

With `L` a loss depending on the boundary bias `v = W e` only, write
`g = ∇_v L ∈ ℝ^h`.  The chain rule gives `∇_W L = g eᵀ` and `∇_e L = Wᵀ g`, so
gradient flow is `Ẇ = -g eᵀ`, `ė = -Wᵀ g`, and the induced velocity of `v` is
`v̇ = Ẇ e + W ė`.  We take that expression as the definition and compute it. -/










/-! ## The two halves together -/


/-! ## Gradient flow: exponential contraction at a rate linear in the EOS width

We now close the loop: the `d`-linear gain of `boundary_gain_ge_card` is fed into a
Grönwall argument, giving an explicit contraction rate for the effective boundary
bias and hence an explicit *training-budget* prediction — the sufficient budget
shrinks like `1 / d`.  This is the falsifiable sharpening of the paper's open
item "threshold 28–384 untested". -/






/-! ## Lab notes (round-net-25, measured)

`pad384` vs `pad384-zeroEOS`: identical GRUCell/head weights per seed
(construction order matches), differing only in the EOS parameter count
(384-d vs 20-d), giving `n = 8` full accuracy `1.0000` vs `0.7441 / 0.0259`.
`cap384-raw` (471,582 params, 20-d EOS) fails at `0.0078 / 0.0063`, so raw
parameter count is not the lever; `pos28` (28-d EOS) fails at `0.0049`, so the
threshold lies strictly between 28 and 384 and position information is not the
lever.  The theorems above show why width can matter at all *only* through the
optimisation geometry: the realisable set is width-independent
(`eos_dimension_no_expressivity_gain`) while the boundary gain grows like `d`
(`boundary_gain_ge_card`).  With `c` fixed, `d = 20 → 384` multiplies the
guaranteed gain by `19.2`.
-/


open Logic.DenseFinalStep in
theorem solution{L₀ ε κ t : ℝ} (hL₀ : 0 < L₀) (hε : 0 < ε) (hκ : 0 < κ)
    (ht : Real.log (L₀ / ε) / (2 * κ) ≤ t) :
    L₀ * Real.exp (-(2 * κ * t)) ≤ ε := by
  have h2κ : 0 < 2 * κ := by linarith
  have hlog : Real.log (L₀ / ε) ≤ 2 * κ * t := by
    rw [div_le_iff₀ h2κ] at ht
    linarith [ht]
  have hpos : 0 < L₀ / ε := div_pos hL₀ hε
  have hexp : Real.exp (-(2 * κ * t)) ≤ Real.exp (-Real.log (L₀ / ε)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hval : Real.exp (-Real.log (L₀ / ε)) = ε / L₀ := by
    rw [Real.exp_neg, Real.exp_log hpos]
    field_simp
  calc L₀ * Real.exp (-(2 * κ * t)) ≤ L₀ * Real.exp (-Real.log (L₀ / ε)) := by nlinarith
    _ = L₀ * (ε / L₀) := by rw [hval]
    _ = ε := by field_simp
