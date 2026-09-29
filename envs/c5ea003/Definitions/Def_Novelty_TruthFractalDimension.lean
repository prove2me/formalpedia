-- Prove2me | Definitions.Def_Novelty_TruthFractalDimension
-- name    : Novelty_TruthFractalDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:21.375349+00:00
-- url     : https://prove2.me/theorems/0c27fc9e-ded1-413b-b402-d48f989bba39
-- title:
--   Aether Catalog definitions — Novelty_TruthFractalDimension
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.TruthFractalDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/TruthFractalDimension.lean by skeleton subtraction
import Mathlib

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

namespace TruthFractalDimension

/-- A **theory** assigns to each length `n` the finite set of accepted binary
strings (statements) of that length. -/
abbrev Theory := (n : ℕ) → Finset (Fin n → Bool)

/-- The number of statements of length `n` accepted by a theory. -/
def count (T : Theory) (n : ℕ) : ℕ := (T n).card

/-- The finite-scale dimension estimate: `log₂ (count T n) / n`. -/
noncomputable def dimEstimate (T : Theory) (n : ℕ) : ℝ :=
  Real.logb 2 (count T n) / n

/-- The **box-counting (fractal) dimension** of a theory. -/
noncomputable def boxDim (T : Theory) : ℝ := limsup (dimEstimate T) Filter.atTop

/-! ### Universal bounds: every dimension lies in `[0,1]` -/







/-! ### The full space has dimension `1` -/

/-- The theory that accepts *every* statement. -/
def allStatements : Theory := fun _ => Finset.univ





/-! ### Bounded theories are negligible (dimension `0`) -/




/-- A "trivial theory" that accepts a single statement (the all-false string) of
each length. -/
def trivialTheory : Theory := fun _ => {fun _ => false}



/-! ### The set of true statements: dimension exactly `1/2` -/

/-- The number of even indices below `n` (equivalently `⌈n/2⌉`). -/
def evenCount (n : ℕ) : ℕ := (Finset.univ.filter (fun i : Fin n => Even i.1)).card

/-- The **truth set**: statements in which every odd-indexed bit is `false`.
Exactly "half" of the coordinates carry information, modelling a truth predicate
that is genuinely constraining yet leaves a positive density of free choices. -/
noncomputable def truthSet : Theory := fun n =>
  Fintype.piFinset
    (fun i : Fin n => if Odd (i : ℕ) then ({false} : Finset Bool) else Finset.univ)










/-! ### Approximability of the dimension from finite data -/


/-! ### Link with Chaitin's constant `Ω`: approximability from below -/

/-- The `k`-th contribution to a halting-probability-style real determined by a
bit sequence `b`. -/
noncomputable def omegaTerm (b : ℕ → Bool) (k : ℕ) : ℝ :=
  (if b k then (1 : ℝ) else 0) / 2 ^ (k + 1)

/-- The finite lower approximation to `Ω` using the first `n` bits. -/
noncomputable def omegaApprox (b : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, omegaTerm b k

/-- The Chaitin-style constant associated with a bit sequence `b`. -/
noncomputable def chaitinOmega (b : ℕ → Bool) : ℝ := ∑' k, omegaTerm b k











end TruthFractalDimension


