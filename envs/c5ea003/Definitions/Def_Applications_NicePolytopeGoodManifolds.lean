-- Prove2me | Definitions.Def_Applications_NicePolytopeGoodManifolds
-- name    : Applications_NicePolytopeGoodManifolds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:08.652708+00:00
-- url     : https://prove2.me/theorems/7c391750-60f3-4fb9-9338-ffd6fecfdced
-- title:
--   Aether Catalog definitions — Applications_NicePolytopeGoodManifolds
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NicePolytopeGoodManifolds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NicePolytopeGoodManifolds.lean by skeleton subtraction
import Mathlib
/-
# Good manifolds in an `n`-nice polytope: the two-layer structure of the maximal count

Let `a n` denote the maximal number of *good* manifolds carried by an `n`-nice
polytope.  From dimension seven onward this count is exactly `2 ^ n`; below that
threshold it exceeds `2 ^ n` by a small *defect*.  Writing `d n = a n − 2 ^ n`,
the observed data are

  `d = (0, 4, 4, 4, 8, 8, 16, 0, 0, …)`   (indexed from `n = 0`),

so `a = (1, 6, 8, 12, 24, 40, 80, 128, 256, …)`.

This file records the exact arithmetic structure of the sequence:

* **Two geometric layers.**  `a n = 2 ^ n + d n`, where `d` is a *second,
  faster–decaying* doubling layer: it takes the values `4, 8, 16` on contiguous
  blocks of lengths `3, 2, 1`, and vanishes once the dominant layer `2 ^ n`
  overtakes it (`n ≥ 7`).

* **Arithmetic fingerprint of the growth rate.**  For `n ≥ 7` the `2`-adic
  valuation of the count equals the dimension, `v₂(a n) = n`: the exponent of the
  base is legible directly in the prime factorisation.

* **Extremal doubling rate.**  The `n`-th root of the count converges to `2`,
  making `2` the exact exponential growth rate of the sequence.

* **A cumulative anomaly.**  The running totals `S n = Σ_{k ≤ n} a k` never
  become divisible by `2 ^ 7`; in fact `S n ≡ 43 (mod 128)` for every `n ≥ 6`.
  This *refutes* the natural guess that the onset of pure geometric behaviour is
  visible as a cumulative divisibility by `2 ^ 7`.

The sequence of counts `1, 6, 8, 12, 24, 40, 80, 128, 256, …` matches OEIS-style
"maximal number of good manifolds in an `n`-nice polytope" data.
-/


namespace NicePolytope

open Finset

/-- The *defect* `d n = a n − 2 ^ n`: the excess of the maximal good-manifold
count over the dominant geometric layer.  It is supported on `1 ≤ n ≤ 6`. -/
def defect : ℕ → ℕ
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 8
  | 5 => 8
  | 6 => 16
  | _ => 0

/-- The maximal number of good manifolds in an `n`-nice polytope,
`a n = 2 ^ n + d n`. -/
def a (n : ℕ) : ℕ := 2 ^ n + defect n

/-- Cumulative count `S n = Σ_{k ≤ n} a k`. -/
def S (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), a k

/-! ### Examples and sanity checks (PEGB: examples) -/

/-! ### The defect layer vanishes past the threshold -/



/-! ### Conjecture 1 — the defect is a truncated doubling layer -/






/-! ### Conjecture 2 — the `2`-adic valuation recovers the dimension -/


/-! ### Monotonicity and Conjecture 3 — extremal doubling rate -/




/-! ### Conjecture 4 — the cumulative divisibility test fails -/



/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  The maximal good-manifold count `a n` is not a
single geometric sequence with noisy head, but the *sum of two* geometric layers:
a dominant `2 ^ n` and a subdominant defect `d n` that is itself a truncated
doubling sequence.  Four falsifiable predictions follow (Conjectures 1–4 above).

**Experiment (Experimenter).**  We fixed the data
`a = 1, 6, 8, 12, 24, 40, 80, 128, 256, …` and computed:
the defect `d = 0,4,4,4,8,8,16,0,…`; the `2`-adic valuations
`v₂(a n) = 0,1,3,2,3,3,4,7,8,9,…`; and the running totals modulo `128`,
`S n % 128 = 1,7,15,27,51,91,43,43,43,…`.  These computations confirmed
Conjectures 1–3 and *refuted* Conjecture 4.

**Analysis (Analyst).**  Conjectures 1–3 are *true and structural*.  Conjecture 1
is exact block combinatorics; Conjecture 2 is immediate once the tail closed form
`a n = 2 ^ n` is isolated; Conjecture 3 holds because the sequence is eventually
*equal* to `2 ^ n`, so its `n`-th root is eventually the constant `2`.
Conjecture 4 is *false, and instructively so*: `S n = S 6 + Σ_{7 ≤ k ≤ n} 2^k
= 171 + (2^{n+1} − 128) = 2^{n+1} + 43`, hence `S n ≡ 43 (mod 128)` for `n ≥ 6`
and the earlier totals are all odd or `≡ 27,51,91`.  The cumulative total carries
a fixed residue `43`, so divisibility by `128` can never occur — the "global"
signal proposed in Conjecture 4 is drowned by the constant head contribution.

**Critique (Critic).**  None of the main theorems is vacuous: `defect_values`
quantifies over all `n`; `padicValNat_a` computes a genuine valuation;
`growth_root_tendsto` is a real limit statement using `rpow`; `S_never_div_128`
is a universally quantified *non-divisibility*, the sharp negative form of the
refuted conjecture.  Boundary cases: the valuation identity `v₂ = n` fails on the
head (e.g. `v₂(a 1) = 1 ≠ … ` genuinely, and `v₂(a 2) = 3`), which is exactly why
the hypothesis is guarded by `n ≥ 7`.

**Synthesis (PI).**  The count decomposes as two independent doubling layers; the
arithmetic of the tail is clean (valuation and root both legible), while the head
leaves a permanent cumulative residue that defeats naive divisibility tests.

**Generalization / extension.**  The two-layer picture suggests a general
principle: any count of the form `c · b^n + (truncated b-adic head)` has `b`-adic
valuation `n + v_b(c)` on its tail and `n`-th root tending to `b`, while its
partial sums carry a fixed residue determined solely by the head.  The present
file is the case `b = 2, c = 1`.

**Boundary / limit case.**  The threshold `n = 7` is sharp: at `n = 6` the defect
is still `16 ≠ 0`, and the `2`-adic valuation there is `4`, not `6`.  The
cumulative refutation (Conjecture 4) is likewise a genuine *counterexample* to the
divisibility heuristic, not a hard-but-true statement.
-/

end NicePolytope


