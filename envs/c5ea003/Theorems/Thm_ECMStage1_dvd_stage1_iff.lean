-- Prove2me | Theorems.Thm_ECMStage1_dvd_stage1_iff
-- name    : ECMStage1.dvd_stage1_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:31:38.166957+00:00
-- url     : https://prove2.me/theorems/9de8975e-41a6-4c6a-990a-f9f8c90e797a
-- title:
--   Exact firing criterion for a truncated schedule.
-- statement:
--   **Exact firing criterion for a truncated schedule.**  An order `n` is killed by
--   the scalar accumulated up to prime cutoff `C` iff each prime power exactly dividing
--   `n` is at most `B` *and* its prime has already entered the schedule.
--
--   ```lean
--   theorem ECMStage1.dvd_stage1_iff{n B C : ℕ} (hn : n ≠ 0) (hB : B ≠ 0) :
--       n ∣ stage1 B C ↔ ∀ q ∈ n.primeFactors, q ≤ C ∧ q ^ n.factorization q ≤ B := by sorry
--
--
--   /-! ## The group-theoretic form -/
--
--   variable {G : Type*} [Group G]
--
--
--
--
--   /-! ## Where in the schedule it fires -/
--
--
--
--
--
--
--
--
--
--   /-! ## Monotonicity of the schedule -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ECMStage1OrderCompletion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ECMStage1OrderCompletion.lean#L90

-- Thm stub generated from Shared/ECMStage1OrderCompletion.lean
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

theorem ECMStage1.dvd_stage1_iff{n B C : ℕ} (hn : n ≠ 0) (hB : B ≠ 0) :
    n ∣ stage1 B C ↔ ∀ q ∈ n.primeFactors, q ≤ C ∧ q ^ n.factorization q ≤ B := by sorry
