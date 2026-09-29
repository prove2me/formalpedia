-- Prove2me | Definitions.Def_Shared_CFPeriodNull
-- name    : Shared_CFPeriodNull
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:08.582989+00:00
-- url     : https://prove2.me/theorems/75b16010-5536-4b5f-bdbf-f85f4754dbce
-- title:
--   Aether Catalog definitions — Shared_CFPeriodNull
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CFPeriodNull`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CFPeriodNull.lean by skeleton subtraction
import Mathlib
/-
# CFPERIOD-NULL: the continued-fraction period of `√N` as a symmetric channel

Formal core for Experiment 398.  We build the PQa (continued fraction of `√N`)
state machine over `ℤ`, prove its complete set of integral invariants, and
deduce the Pell/fundamental-unit output.
-/

namespace CFPeriodNull

/-! ## 1. The PQa state machine -/

/-- One state of the continued-fraction (PQa) algorithm for `√N`:
`m, d` describe the current complete quotient `(√N + m)/d`, and
`hp, h, qp, q` are the two most recent convergent numerators/denominators. -/
structure CFState where
  m : ℤ
  d : ℤ
  hp : ℤ
  h : ℤ
  qp : ℤ
  q : ℤ
deriving Repr, DecidableEq

/-- Initial state: `m = 0`, `d = 1`, `h₋₁ = 1, h₋₂ = 0`, `q₋₁ = 0, q₋₂ = 1`. -/
def CFState.init : CFState := ⟨0, 1, 0, 1, 1, 0⟩

/-- One PQa step with (arbitrary) partial quotient `a`. -/
def step (N : ℤ) (s : CFState) (a : ℤ) : CFState :=
  ⟨s.d * a - s.m, (N - (s.d * a - s.m) ^ 2) / s.d, s.h, a * s.h + s.hp, s.q,
    a * s.q + s.qp⟩

/-- The complete set of integral invariants of the PQa machine. -/
structure Inv (N : ℤ) (s : CFState) : Prop where
  dne : s.d ≠ 0
  ddvd : s.d ∣ N - s.m ^ 2
  rel1 : N * s.q = s.h * s.m + s.hp * s.d
  rel2 : s.q * s.m + s.qp * s.d = s.h
  det : (s.h * s.qp - s.hp * s.q) ^ 2 = 1




/-! ## 2. The Pell / fundamental-unit output of the machine -/



/-! ## 3. The concrete continued fraction of `√N` -/

/-- One step of the *actual* continued fraction of `√N`, with the floor
partial quotient `a = ⌊(⌊√N⌋ + m)/d⌋`. -/
def cfNext (N : ℕ) (s : CFState) : CFState :=
  step (N : ℤ) s (((Nat.sqrt N : ℤ) + s.m) / s.d)

/-- The state of the continued fraction of `√N` after `k` steps. -/
def cfRun (N : ℕ) : ℕ → CFState
  | 0 => CFState.init
  | k + 1 => cfNext N (cfRun N k)




/-! ## 4. The one factor-adjacent exit: a split square root of `1 mod N` -/



/-! ## 5. The negative-Pell dichotomy: a pure congruence bit -/





/-! ## 6. The cheap-period window carries no leverage -/






/-! ## 7. The cheap window is a density-zero family -/


/-! ## 8. Dirichlet no-pinning: the congruence bit never pins a factor -/



/-! ## 9. De-confounding: every partial quotient is pinned by `⌊√N⌋`

The raw experiment found `corr(max partial quotient, s) ≈ +0.99` in every
bucket; the reason is that the maximal partial quotient of `√N` is exactly
`2⌊√N⌋`, a pure `N`-size coordinate.  Here we prove both halves:
`a_k ≤ 2⌊√N⌋` for every `k ≥ 1`, with equality at the end of a period. -/

/-- Integer part of `√N`. -/
def a0 (N : ℕ) : ℤ := (Nat.sqrt N : ℤ)



/-- The "reduced" regime of the continued fraction of `√N`: the complete
quotient `(√N + m)/d` satisfies `0 < d`, `0 ≤ m < √N`, `d < √N + m` and
`√N < d + m`, all written with the integer coordinate `a0 N = ⌊√N⌋`. -/
structure Red (N : ℕ) (s : CFState) : Prop where
  dpos : 0 < s.d
  mnn : 0 ≤ s.m
  mle : s.m ≤ a0 N
  dle : s.d ≤ a0 N + s.m
  agt : a0 N < s.d + s.m








/-! ## 10. Verified instances (Lab Notes)

Machine-checked instances of the whole pipeline.  The computed period table for
`2 ≤ N ≤ 40` (non-squares) reproduces OEIS A003285:

```
N : 2  3  5  6  7  8 10 11 12 13 14 15 17 18 19 20 21 22 23 24 26 27 28 29 31
l : 1  2  1  2  4  2  1  2  2  5  4  2  1  2  6  2  6  6  4  2  1  2  4  5  8
```

with period-end unit norms `-1` exactly on the odd periods
(`N = 2, 5, 10, 13, 17, 26, 29, 37`), confirming the negative-Pell dichotomy.
-/









/-! ## 11. The exit is *exactly* the split-root event: prime powers are immune

Cycle-2 result.  The only factor-adjacent exit of the channel (Section 4) fires
only when `N` has at least two distinct prime factors: modulo an odd prime power
every square root of `1` is `± 1`, so the continued fraction of `√(p^k)` — no
matter how long its period — can never split `N`. -/





/-! ## 12. Cost side: denominators grow like Fibonacci, `d` stays `≤ 2⌊√N⌋`

Cycle-3 results.  The period-end witness is *exponentially large in the period*
(`q_l ≥ fib l`), while all the intermediate data stay inside the box
`0 ≤ m ≤ ⌊√N⌋`, `0 < d ≤ 2⌊√N⌋`.  So the channel's only unbounded coordinate is
the *number of steps*, which is what makes it a `O(√N)`-cost object rather than
a `poly(log N)` witness. -/




end CFPeriodNull


