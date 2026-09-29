-- Prove2me | Theorems.Thm_TruthFractalDimension_tendsto_dimEstimate_truthSet
-- name    : TruthFractalDimension.tendsto_dimEstimate_truthSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:39:55.270564+00:00
-- url     : https://prove2.me/theorems/17784565-1418-42a9-bb4d-460d1960bbcb
-- title:
--   Tendsto dimEstimate truthSet
-- statement:
--   Formal statement of `TruthFractalDimension.tendsto_dimEstimate_truthSet` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TruthFractalDimension.tendsto_dimEstimate_truthSet:
--       Filter.Tendsto (dimEstimate truthSet) Filter.atTop (nhds (1 / 2)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/TruthFractalDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/TruthFractalDimension.lean#L262

-- Thm stub generated from Novelty/TruthFractalDimension.lean
import Mathlib
import Definitions.Def_Novelty_TruthFractalDimension

/-!
# The Fractal Dimension of the Space of True Statements

This file develops a rigorous, quantitative notion of *how large the set of true
statements is* inside the space of all statements, and shows that — for a natural
model — this size is a genuine fractal (box-counting) dimension lying strictly
between `0` and `1`.

## The model

We encode statements as finite binary strings.  A string of length `n` is a
function `Fin n → Bool`, and there are exactly `2 ^ n` of them.  A **theory**
`T` is an assignment, to each length `n`, of the finite set of accepted strings
of that length; its **counting function** is `count T n = (T n).card`.

The metric picture behind the definitions is the standard one on the Cantor
space of infinite binary sequences: two sequences are close when they agree on a
long common prefix.  Covering a set by cylinders of depth `n` costs one cylinder
per accepted length-`n` prefix, so the natural covering number at scale
`2^{-n}` is `count T n`.  The **box-counting dimension** is therefore

  `boxDim T = limsup_n  log₂ (count T n) / n`.

## Main results

* `boxDim_le_one` / `dimEstimate_nonneg`: every theory has dimension in `[0,1]`.
* `boxDim_allStatements`: the full space has dimension `1`.
* `boxDim_of_bounded` and `boxDim_trivialTheory`: theories with boundedly many
  statements per length are dimension `0` — negligible.
* `boxDim_truthSet`: an explicitly constructed "half-information" theory has
  dimension **exactly `1/2`**, and `truthSet_dimension_strictly_between` records
  that `0 < 1/2 < 1`: the set of true statements is *sparse but not negligible*.
* `boxDim_of_tendsto`: whenever the finite-scale estimates converge, the
  dimension equals their limit — the dimension is *approximable* from finite data.

## The link with Chaitin's constant

The concluding section models the halting probability `Ω` as a left-computable
real: the limit of an increasing sequence of finite rational approximations.
`omegaApprox_mono` and `omegaApprox_tendsto` establish exactly this
approximation-from-below, mirroring the way the box dimension is approached from
finite data; `omega_mem_unitInterval` places `Ω` in `[0,1]`, the same interval in
which every fractal dimension of truth lives.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "truth" carved out of the space of all statements is
neither full nor vanishing; its box-counting dimension is a real number strictly
inside `(0,1)`, and it is approximable but not obviously computable, echoing
Chaitin's Ω.

Experiment (Experimenter): We built the counting/dimension machinery over
`Fin n → Bool`, proved the universal bounds, computed the full-space dimension
(`1`) and the dimension of bounded theories (`0`), and constructed an explicit
"odd coordinates must be false" theory whose count is `2^{⌈n/2⌉}`, giving
dimension `1/2`.  The precise count uses a product/`piFinset` identity; the
`1/2` limit uses the exact parity count `2·⌈n/2⌉ = n + [n odd]` and a squeeze.

Analysis (Analyst): The value `1/2` is forced by the linear density of free
coordinates; any fixed rational density `p/q` of free coordinates would yield
dimension `p/q`, so every value in `[0,1] ∩ ℚ` is realized.  The `limsup`
definition is essential: for irregular theories the finite estimates need not
converge, and only the `limsup` is stable.

Critique (Critic): Dimension `1/2` is not a definitional triviality — it rests on
the exact combinatorial count and a genuine analytic squeeze.  We avoided the
vacuous route (`native_decide` on a fixed `n`) by proving the count for *all* `n`.
The Ω section is deliberately modest: we prove approximability-from-below
rigorously and do *not* assert uncomputability, which needs the full theory of
computable reals; that is flagged as a future direction.

Synthesis (PI): Truth, measured by covering the Cantor space of statements, has a
fractal dimension in the open unit interval; that dimension is the limit of
finite, effectively-computable estimates, exactly as Ω is the limit of finite
lower bounds.
-/

open Filter Topology

open TruthFractalDimension





/-! ### Universal bounds: every dimension lies in `[0,1]` -/







/-! ### The full space has dimension `1` -/






/-! ### Bounded theories are negligible (dimension `0`) -/







/-! ### The set of true statements: dimension exactly `1/2` -/

theorem TruthFractalDimension.tendsto_dimEstimate_truthSet:
    Filter.Tendsto (dimEstimate truthSet) Filter.atTop (nhds (1 / 2)) := by sorry
