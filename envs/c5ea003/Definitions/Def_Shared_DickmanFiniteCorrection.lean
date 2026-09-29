-- Prove2me | Definitions.Def_Shared_DickmanFiniteCorrection
-- name    : Shared_DickmanFiniteCorrection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:36.328984+00:00
-- url     : https://prove2.me/theorems/98b3d272-e841-4dd3-b4cd-48cd1f93d301
-- title:
--   Aether Catalog definitions — Shared_DickmanFiniteCorrection
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.DickmanFiniteCorrection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/DickmanFiniteCorrection.lean by skeleton subtraction
import Mathlib

/-!
# The Dickman leading term, its finite-size correction, and why it is slow

Context (experiment 465, paper 130).  Smoothness probabilities in the quadratic
sieve are modelled by the Dickman function `ρ(u)`, and in the asymptotic analysis
of subexponential factoring one replaces `ρ(u)` by its leading term

`L(u) = exp (-u (log u + log log u - 1))`.

The experiment measured, over `1.2 · 10^6` smoothness tests with
`N ∈ {2^32 .. 2^44}`, that

* the empirical smooth-density / `ρ(u)` ratio sits in `0.877 – 0.913` at every
  scale, **equally for the `x^2 - N` pool and for the size-matched random
  control**, and
* the discrepancy has the size of the finite-`x` correction
  `log log v / log v ≈ 17–20 %` for the value sizes involved, shrinking only
  logarithmically, and
* the leading term `L(u)` is a useless proxy for `ρ(u)` at reachable `u`.

This file proves the analytic facts behind those three statements.

Main results:

* `rhoTwo_lt_one`, `rhoTwo_pos` — the exact Dickman value on `(1,2]` is a
  genuine probability, `ρ(u) = 1 - log u ∈ (0,1)`.
* `one_lt_dickmanLead` — on `(1,2]` the leading term is `> 1`: it is not even a
  probability there, so it cannot approximate `ρ`.
* `dickmanLead_two_gt_nine_mul_rho` — quantitatively, at `u = 2` the leading term
  overshoots the true value by more than a factor `9`.
* `dickmanLead_lt_one_of_three_le` — the leading term only becomes admissible
  from `u ≥ 3` onwards (and, per the experiment, only becomes *accurate* near
  `u ≈ 14.75`).
* `finiteCorrection_antitoneOn` — the finite-size correction `log log v / log v`
  decreases, but only logarithmically.
* `finiteCorrection_tendsto_zero` — it does vanish: nothing blocks convergence.
* `finiteCorrection_window` — in the experimental window `e^12 ≤ v ≤ e^20` it
  lies in `[0.1, 0.25]`, bracketing the measured `17–20 %` deficit.
-/

namespace DickmanFinite

open Real Filter Topology

/-- Leading-term Dickman model `L(u) = exp (-u (log u + log log u - 1))`. -/
noncomputable def dickmanLead (u : ℝ) : ℝ :=
  Real.exp (-u * (Real.log u + Real.log (Real.log u) - 1))

/-- The exact Dickman function on the interval `1 ≤ u ≤ 2`, where it is given in
closed form by `ρ(u) = 1 - log u`. -/
noncomputable def rhoTwo (u : ℝ) : ℝ := 1 - Real.log u

/-! ## `ρ` is a probability on `(1,2]`, the leading term is not -/










/-! ## The finite-size correction -/

/-- The finite-`x` correction term of the Dickman model at value size `v`:
`log log v / log v`. -/
noncomputable def finiteCorrection (v : ℝ) : ℝ := Real.log (Real.log v) / Real.log v



/-! ### The experimental window -/




end DickmanFinite


