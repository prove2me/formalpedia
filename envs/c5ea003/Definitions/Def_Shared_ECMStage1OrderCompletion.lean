-- Prove2me | Definitions.Def_Shared_ECMStage1OrderCompletion
-- name    : Shared_ECMStage1OrderCompletion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:48.448341+00:00
-- url     : https://prove2.me/theorems/0d1d389e-cc9f-4fbc-93ab-0f1ef8f7bf0b
-- title:
--   Aether Catalog definitions — Shared_ECMStage1OrderCompletion
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ECMStage1OrderCompletion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ECMStage1OrderCompletion.lean by skeleton subtraction
import Mathlib

/-!
# ECM stage 1: order completion, its exact firing criterion, and its firing cutoff

Context (experiments 570 / 595, papers 215 → 218 → 244).  The recorded question is
*mechanistic*: when a stage-1 elliptic-curve-method (ECM) run succeeds at a small
smoothness bound `B1`, is that success a **collision accident** (a chance gcd, whose
rate the folklore model puts at `1 - exp(-1.44·B1/p)`), or is it **order completion**
— the group order genuinely dividing the stage-1 scalar — *firing early inside the
prime schedule*?

That dichotomy is a statement about the scalar

```
k(B, C)  =  ∏ { q ^ ⌊log_q B⌋ : q prime, q ≤ C }
```

which stage 1 accumulates prime by prime, and about the set of group elements it
kills.  This file isolates the part of the picture that is an unconditional theorem,
in the form used by the experiments:

* **Firing criterion** (`dvd_stage1_iff`, `orderCompletes_iff`).  A point of order
  `n` is killed by the full stage-1 scalar `k(B) = k(B,B)` **iff** `n` is
  `B`-powersmooth.  No probability enters: the event is exactly a divisibility.
* **Order completion is impossible above the bound** (`not_orderCompletes_of_large_primePow`,
  `no_orderCompletion_of_large_prime_factor`).  If the order has a prime power
  divisor exceeding `B`, stage 1 provably never fires on it.  This is the formal
  content of the `found_q` cross-check: for the *large* factor `q` of the modulus,
  with `B1 ≪ q`, order completion cannot be responsible for a hit, so hits there
  measure the collision floor alone.
* **Firing cutoff = largest prime factor** (`firingCutoff_isLeast`,
  `dvd_stage1_prefix_iff`).  For an order that does fire, the *position in the
  schedule* at which it fires is not random: it is exactly the largest prime factor
  of the order.  This turns "early fire" into an arithmetic statement — a run fires
  inside the first `π(L)` of its `π(B)` prime steps precisely when the order has no
  prime factor above `L`.

The distributional consequences (exact firing rates, the gcd staircase, its
non-uniformity, multi-curve amplification, and the collision-floor comparison) are
in `Catalog.Shared.ECMStage1FiringRate`, which builds on this file.
-/

namespace ECMStage1

open Finset

/-! ## The stage-1 scalar and its factorization -/

/-- The stage-1 scalar truncated at prime cutoff `C`:
`k(B, C) = ∏ { q ^ ⌊log_q B⌋ : q prime, q ≤ C }`.  Stage 1 of ECM multiplies the
starting point by these prime powers one prime at a time, in increasing order, so
`stage1 B C` is exactly the scalar accumulated after all primes `≤ C`. -/
def stage1 (B C : ℕ) : ℕ := ∏ q ∈ (Finset.range (C + 1)).filter Nat.Prime, q ^ Nat.log q B

/-- The full stage-1 scalar at smoothness bound `B`. -/
def stage1Scalar (B : ℕ) : ℕ := stage1 B B

/-- `n` is `B`-powersmooth: every prime power exactly dividing `n` is at most `B`. -/
def Powersmooth (B n : ℕ) : Prop := ∀ q ∈ n.primeFactors, q ^ n.factorization q ≤ B





/-! ## The firing criterion -/




/-! ## The group-theoretic form -/

variable {G : Type*} [Group G]




/-! ## Where in the schedule it fires -/

/-- The largest prime factor of `n` (`0` for `n = 0, 1`). -/
def lpf (n : ℕ) : ℕ := n.primeFactors.sup id




/-- The number of prime steps of the schedule, `π(C)`. -/
def primeCount (C : ℕ) : ℕ := ((Finset.range (C + 1)).filter Nat.Prime).card




/-! ## Monotonicity of the schedule -/


end ECMStage1


