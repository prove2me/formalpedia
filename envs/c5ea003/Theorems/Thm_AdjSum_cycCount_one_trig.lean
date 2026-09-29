-- Prove2me | Theorems.Thm_AdjSum_cycCount_one_trig
-- name    : AdjSum.cycCount_one_trig
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:14:14.775438+00:00
-- url     : https://prove2.me/theorems/00ab9951-9c62-44b6-bef9-0dffdc7f515d
-- title:
--   Trigonometric closed form for the two-state cyclic counts (the Lucas numbers).
-- statement:
--   **Trigonometric closed form for the two-state cyclic counts** (the Lucas numbers).
--
--   ```lean
--   theorem AdjSum.cycCount_one_trig(d : ℕ) :
--       (cycCount 1 d : ℝ)
--         = (-1 / (2 * Real.cos (3 * Real.pi / 5))) ^ (d + 1)
--             + (-1 / (2 * Real.cos (Real.pi / 5))) ^ (d + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/Spectral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/Spectral.lean#L94

-- Thm stub generated from Applications/AdjacentSumPolytopes/Spectral.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

/-!
# A trigonometric form of the two-state spectrum

Numerical experiments (recorded in `ComputationalEvidence.md`) suggest that the
eigenvalues of the adjacent-sum transfer matrix `adjMat s` are exactly

`(-1)^s / (2 cos((2j−1)π/(2s+3)))`,  `j = 1, …, s + 1`.

This file proves the first instance, `s = 1`, completely: the two eigenvalues of
`adjMat 1 = !![1,1;1,0]` are `−1/(2 cos(3π/5)) = φ` and `−1/(2 cos(π/5)) = ψ`, the golden
ratio and its conjugate, and consequently the two-state open and cyclic counts have
*trigonometric* closed forms

`#open(d) = (A^{d+3} − B^{d+3})/√5`,  `#cyclic(d) = A^{d+1} + B^{d+1}`,
`A = −1/(2 cos(3π/5))`, `B = −1/(2 cos(π/5))`.

The dominant pole `A = φ` is the exponential growth rate of both parity classes, an
explicit instance of the abstract growth rate produced in
`Applications.AdjacentSumPolytopes.DominantGrowth`.

-- !-- Lab Notes -- !--
* **Hypothesis.** The transfer matrix is a `0/1` staircase matrix, whose spectrum should
  be a secant family, i.e. reciprocals of cosines at odd multiples of `π/(2s+3)`.
* **Experiment.** Characteristic polynomials computed exactly for `s = 1, …, 7` and
  evaluated at the candidate values `±1/(2 cos((2j−1)π/(2s+3)))`: the residuals are of
  size `10⁻¹⁶`–`10⁻¹⁰` (pure floating-point noise) precisely when the global sign is
  `(-1)^s`, and of size `10⁻¹`–`10⁵` for the other sign.  So the sign alternates with the
  parity of `s`, which is the parity dichotomy of the model showing up spectrally.
* **Analysis.** For `s = 1` the claim is exactly the statement that the golden ratio is
  `−1/(2 cos 3π/5)`, which is provable from `Real.cos_pi_div_five`; the general case
  requires a Chebyshev-type factorisation of `det(xI − adjMat s)` and is recorded as the
  headline conjecture in `FUTURE_DIRECTIONS.md`.
* **Critique.** Nothing here is definitional: the identity `−1/(2 cos 3π/5) = φ` needs
  the exact value of `cos(π/5)`, and the closed forms need Binet's formula together with
  the two Fibonacci identities proved in `Growth.lean`.
-/

open AdjSum

open Real

theorem AdjSum.cycCount_one_trig(d : ℕ) :
    (cycCount 1 d : ℝ)
      = (-1 / (2 * Real.cos (3 * Real.pi / 5))) ^ (d + 1)
          + (-1 / (2 * Real.cos (Real.pi / 5))) ^ (d + 1) := by sorry
