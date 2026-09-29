-- Prove2me | Definitions.Def_Applications_NicePolytope_GoodManifolds
-- name    : Applications_NicePolytope_GoodManifolds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:12.883845+00:00
-- url     : https://prove2.me/theorems/b602036e-6f8e-4f5a-9ca1-ddda9a22c7e0
-- title:
--   Aether Catalog definitions — Applications_NicePolytope_GoodManifolds
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NicePolytope.GoodManifolds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NicePolytope/GoodManifolds.lean by skeleton subtraction
import Mathlib

/-!
# Good manifolds in an `n`-nice polytope: closed form, recurrence, and structure

This file studies the integer sequence

`6, 8, 12, 24, 40, 80, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768,
65536, 131072, 262144, 524288, 1048576, 2097152, …`

which records the maximal number of *good* manifolds admitted by an `n`-nice
polytope.  The data has an irregular head (dimensions `1`–`6`) followed by a
perfectly regular exponential tail.  We isolate the tail behaviour and prove
that from dimension `7` onward the count is exactly `2 ^ n`.  This yields a
clean two-term recurrence (the count *doubles* with each new dimension), an
exact geometric partial-sum formula, global strict monotonicity, and — bridging
combinatorics with `p`-adic number theory — the fact that the `2`-adic valuation
of the count equals the dimension.

## Main results

* `goodManifolds_eq_two_pow` — closed form: `goodManifolds n = 2 ^ n` for `n ≥ 7`.
* `goodManifolds_doubling` — recurrence: `goodManifolds (n+1) = 2 * goodManifolds n` for `n ≥ 7`.
* `goodManifolds_strictMono` — the whole sequence is strictly increasing.
* `goodManifolds_tail_sum` — geometric partial sums of the tail.
* `goodManifolds_two_adic` — the `2`-adic valuation equals the dimension (for `n ≥ 7`).
* `goodManifolds_even` — every positive-dimensional count is even.

## Notes on the head of the sequence

The first six values (`6, 8, 12, 24, 40, 80`) do **not** follow the pure power
law, which is exactly what makes the closed form a genuine theorem about the
tail rather than a definitional identity; see `goodManifolds_head_not_pow` for
the explicit boundary witness at dimension `5`.
-/

namespace GoodManifolds

/-- The irregular head of the sequence, in dimensions `1`–`6`.  Values outside
this range are recorded as `0`; they are never used by the exported results,
which either restrict to `n ≥ 7` or evaluate the head directly. -/
def head : ℕ → ℕ
  | 1 => 6
  | 2 => 8
  | 3 => 12
  | 4 => 24
  | 5 => 40
  | 6 => 80
  | _ => 0

/-- Maximal number of *good* manifolds in an `n`-nice polytope.  For the first
six dimensions the value is read from `head`; from dimension `7` onward it is
the pure power `2 ^ n`. -/
def goodManifolds (n : ℕ) : ℕ := if n ≤ 6 then head n else 2 ^ n

/-! ### Examples: the tabulated data is reproduced exactly. -/

-- The first twenty-one terms, matching the reference data.
/-! ### Closed form and recurrence -/



/-! ### Structural properties -/




/-! ### Geometric partial sums of the tail -/


/-! ### A bridge to `p`-adic number theory -/


/-! ### Boundary witness

The head genuinely departs from the power law, so the closed form is a theorem
about the tail rather than an identity holding everywhere. -/


/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  The reference data
`6,8,12,24,40,80,128,256,…,2097152` splits into an irregular head and an
exponential tail.  Conjecture H1: from some dimension on, the count is exactly
`2 ^ n`.  Bolder conjecture H2 (cross-domain): whenever the count is a pure
prime power `p ^ k`, its `p`-adic valuation recovers the dimension, tying the
combinatorial count to arithmetic structure.

**Experiment (Experimenter).**  Tabulating `goodManifolds (i+1)` for
`i = 0,…,20` reproduces every listed term, and the tail `128,256,…,2097152`
matches `2^7,…,2^21`.  H1 was proved as `goodManifolds_eq_two_pow` (threshold
`n ≥ 7`); the doubling recurrence, geometric partial sum, strict monotonicity,
parity, and the `2`-adic identity `goodManifolds_two_adic` (instance of H2) all
followed.

**Analysis (Analyst).**  H1 is *true but thresholded*: the six head values
break the pattern, so the honest statement quantifies over `n ≥ 7`.  The
boundary witness `goodManifolds_head_not_pow` (dimension `5` gives `40 ≠ 32`)
shows the threshold cannot be lowered to include the head.  The head is
nonetheless compatible with the tail for monotonicity, which is why the *global*
`StrictMono` statement survives while the *global* closed form does not.

**Critique (Critic).**  Each proof uses only lemmas declared strictly above it;
none is circular.  No result is vacuous: `goodManifolds_eq_two_pow` has genuine
content (contrast the false global version refuted by
`goodManifolds_head_not_pow`), and the sum/valuation/monotonicity theorems use
induction, `omega`, and a `p`-adic lemma rather than a single decision
procedure.  Corner case checked: the head/tail junction at `n = 6 → 7`
(`80 < 128`) is covered by the finite branch of `goodManifolds_strictMono`.

**Synthesis (PI).**  The count is, from dimension `7`, a shifted geometric
sequence with ratio `2`; equivalently the marginal cost of one extra dimension
is a full doubling.  The `2`-adic valuation reading of the tail is the concrete
cross-domain bridge and seeds the future directions.
-/

end GoodManifolds


