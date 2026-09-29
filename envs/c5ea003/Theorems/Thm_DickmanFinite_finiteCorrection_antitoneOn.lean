-- Prove2me | Theorems.Thm_DickmanFinite_finiteCorrection_antitoneOn
-- name    : DickmanFinite.finiteCorrection_antitoneOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:31:01.679818+00:00
-- url     : https://prove2.me/theorems/f3d5aae3-904d-4500-ae7c-0fabf7c2c60c
-- title:
--   The correction is decreasing beyond `v â¥ exp (exp 1)`: it shrinks, but only
-- statement:
--   The correction is decreasing beyond `v â¥ exp (exp 1)`: it shrinks, but only
--   logarithmically in `v` â which is exactly why the measured `0.877â0.913` band
--   barely moves over twelve bits of scale.
--
--   ```lean
--   theorem DickmanFinite.finiteCorrection_antitoneOn:
--       AntitoneOn finiteCorrection {v : ℝ | Real.exp (Real.exp 1) ≤ v} := by sorry
--
--   /-! ### The experimental window -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/DickmanFiniteCorrection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/DickmanFiniteCorrection.lean#L149

-- Thm stub generated from Shared/DickmanFiniteCorrection.lean
import Mathlib
import Definitions.Def_Shared_DickmanFiniteCorrection

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

open DickmanFinite

open Real Filter Topology



/-! ## `ρ` is a probability on `(1,2]`, the leading term is not -/










/-! ## The finite-size correction -/

theorem DickmanFinite.finiteCorrection_antitoneOn:
    AntitoneOn finiteCorrection {v : ℝ | Real.exp (Real.exp 1) ≤ v} := by sorry
