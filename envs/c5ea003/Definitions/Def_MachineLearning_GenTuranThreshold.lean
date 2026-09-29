-- Prove2me | Definitions.Def_MachineLearning_GenTuranThreshold
-- name    : MachineLearning_GenTuranThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:42:13.862769+00:00
-- url     : https://prove2.me/theorems/3943aa5f-f9d9-490e-a00d-1c7a182c648d
-- title:
--   Aether Catalog definitions — MachineLearning_GenTuranThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.GenTuranThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/GenTuranThreshold.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The parity gap between the proved and the necessary threshold for ex(n, K_{a,b}, K_{3,t})

The Janzer–Longbrake–Yepremyan theorem establishes `ex(n, K_{a,b}, K_{3,t}) = Θ(n^3)` for
`t ≥ 2·max{3, ⌈b/2⌉} + 1`.  The cubic *upper* bound (formalized in
`GenTuranK3tUpperBound.lean`) holds already at the conjectured **necessary** threshold
`t = b + 1`.  This file pins down, with exact arithmetic, the gap between the two thresholds:

* it is `0` exactly when `b` is even (so the proved threshold already meets the necessary one),
* it is `1` exactly when `b` is odd (the only remaining gap, which the conjecture claims is
  illusory).

We work over `ℕ` with `⌈b/2⌉ = (b+1)/2`.

## Catalog connections
* `Janzer-Longbrake-Yepremyan theorem for ex(n,K_{a,b},K_{3,t})`: `paperThreshold` is their
  hypothesis `2·max{3, ⌈b/2⌉}+1`.
* The leading constant in `GenTuranK3tUpperBound.KabCopies_cubic_of_K3tFree` collapses at the
  necessary threshold, recorded here in `cubic_constant_at_threshold`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The proved threshold `2·max{3,⌈b/2⌉}+1` and the necessary threshold
  `b+1` differ by exactly the parity of `b` (for `b ≥ 6`).
Experiment (Experimenter): Reduced the ceiling/`max` expression over `ℕ` to a single closed form
  `paperThreshold b = b + 1 + b % 2` (`b ≥ 6`), discharged by `omega`, then specialized to even
  and odd `b`.
Analysis (Analyst): The `max{3, ⋯}` clause is inert once `b ≥ 6` (since `⌈b/2⌉ ≥ 3`), so the gap
  is governed purely by whether doubling `⌈b/2⌉` recovers `b` (even) or overshoots by one (odd).
Critique (Critic): The closed form would be *false* for small `b` (e.g. `b ≤ 4`, where the `max`
  clause dominates), so the `6 ≤ b` guard is load-bearing and kept explicit.  No statement is
  vacuous; `necessary_lt_paper_iff_odd` is a genuine `↔`.
Synthesis (PI): The odd case is the unique frontier; closing it is exactly the stated conjecture.
-/

namespace GenTuranK3t

/-- The threshold under which Janzer–Longbrake–Yepremyan prove `ex(n,K_{a,b},K_{3,t}) = Θ(n^3)`:
`t ≥ 2·max{3, ⌈b/2⌉} + 1`, with `⌈b/2⌉ = (b+1)/2` over `ℕ`. -/
def paperThreshold (b : ℕ) : ℕ := 2 * max 3 ((b + 1) / 2) + 1

/-- The conjectured necessary threshold: `t ≥ b + 1` (equivalently `b ≤ t - 1`, so that
`K_{a,b}` can be `K_{3,t}`-free). -/
def necessaryThreshold (b : ℕ) : ℕ := b + 1







end GenTuranK3t


