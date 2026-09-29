-- Prove2me | solution 1 for ECMStage1.stage1_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:36:55.082563+00:00
-- url     : https://prove2.me/submissions/1d6d2691-9642-4127-8bf1-b29108e5e84c

-- Sol generated from Shared/ECMStage1OrderCompletion.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1OrderCompletion

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

open ECMStage1

open Finset

/-! ## The stage-1 scalar and its factorization -/








/-! ## The firing criterion -/




/-! ## The group-theoretic form -/

variable {G : Type*} [Group G]




/-! ## Where in the schedule it fires -/









/-! ## Monotonicity of the schedule -/



open ECMStage1 in
theorem solution(B C : ℕ) : stage1 B C ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro q hq
  simp only [Finset.mem_filter] at hq
  exact pow_ne_zero _ hq.2.pos.ne'
