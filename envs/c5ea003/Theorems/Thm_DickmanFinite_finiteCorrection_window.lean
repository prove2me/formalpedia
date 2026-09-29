-- Prove2me | Theorems.Thm_DickmanFinite_finiteCorrection_window
-- name    : DickmanFinite.finiteCorrection_window
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:30:48.477893+00:00
-- url     : https://prove2.me/theorems/da064821-2d3f-4f18-adec-58775dcad3b5
-- title:
--   The measured deficit has exactly the size of the finite-`x` correction.
-- statement:
--   **The measured deficit has exactly the size of the finite-`x` correction.**
--   Throughout the experimental window `exp 12 â¤ v â¤ exp 20` (value sizes of `12` to
--   `20` nats, i.e. the `x^2 - N` values sieved for `N` up to `2^44`) the correction
--   `log log v / log v` lies between `10 %` and `25 %`, bracketing the observed
--   `17â20 %` shortfall of the empirical density against `Ï(u)`.
--
--   ```lean
--   theorem DickmanFinite.finiteCorrection_window{v : ℝ} (h1 : Real.exp 12 ≤ v) (h2 : v ≤ Real.exp 20) :
--       0.1 ≤ finiteCorrection v ∧ finiteCorrection v ≤ 0.25 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/DickmanFiniteCorrection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/DickmanFiniteCorrection.lean#L190

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




/-! ### The experimental window -/

theorem DickmanFinite.finiteCorrection_window{v : ℝ} (h1 : Real.exp 12 ≤ v) (h2 : v ≤ Real.exp 20) :
    0.1 ≤ finiteCorrection v ∧ finiteCorrection v ≤ 0.25 := by sorry
