-- Prove2me | Theorems.Thm_ECMStage1_jumpSet_eq_primeFactors_filter
-- name    : ECMStage1.jumpSet_eq_primeFactors_filter
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:31:47.207971+00:00
-- url     : https://prove2.me/theorems/a4af8113-4057-4e8d-9754-ad5df3f4f91e
-- title:
--   Exact description of the firing positions.
-- statement:
--   **Exact description of the firing positions.**  The steps of the schedule at which
--   the firing count grows are *precisely* the prime divisors of the order that are at most
--   the smoothness bound.  Firing positions are therefore an arithmetic invariant of the
--   order, not a random subset of the schedule.
--
--   ```lean
--   theorem ECMStage1.jumpSet_eq_primeFactors_filter{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) :
--       jumpSet m B = m.primeFactors.filter (fun q => q ≤ B) := by sorry
--
--
--
--
--   /-! ## Early fire, quantitatively -/
--
--
--
--
--
--
--   /-! ## Several curves -/
--
--
--
--   /-! ## The collision heuristic is the wrong model -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ECMStage1FiringRate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ECMStage1FiringRate.lean#L149

-- Thm stub generated from Shared/ECMStage1FiringRate.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1OrderCompletion

/-!
# Exact stage-1 firing rates, the gcd staircase, and why the collision model is the wrong one

`Catalog.Shared.ECMStage1OrderCompletion` proved that stage-1 firing is a divisibility,
and that its position in the prime schedule is the largest prime factor of the point's
order.  This file turns those two facts into exact *counts*, which is the level at
which experiments 570 / 595 measured the phenomenon.

Working in the cyclic group of order `m` (the model of the group of points used
throughout the ECM literature: a random point is a uniformly random residue mod `m`),
we prove:

* **Exact rate** (`card_firingSet`).  The number of points killed by a scalar `k` is
  *exactly* `gcd(m, k)` — never a Poisson-type expression.  In particular the success
  rate at bound `B` is `gcd(m, k(B)) / m`.
* **Scale invariance of the firing count** (`card_firingSet_scale_invariant`).
  Multiplying the order by any factor coprime to the scalar changes neither the set
  of prime powers that matter nor the firing count: the mechanism does not degrade as
  the modulus grows, only the denominator does.
* **The gcd staircase** (`gcd_stage1_flat`, `jumpSet_subset_primeFactors`,
  `card_jumpSet_le`).  The cumulative firing count `C ↦ gcd(m, k(B,C))` is *flat*
  between prime divisors of `m` and jumps only at primes dividing `m`; there are at
  most `ω(m) ≤ log₂ m` jumps among the `π(B)` steps of the schedule.  So the
  firing-position distribution is a step function supported on `≤ log₂ m` positions:
  it cannot be the uniform distribution on the schedule once `π(B) > log₂ m`
  (`firing_positions_not_uniform`).  This is the unconditional skeleton under the
  observed KS rejections.
* **Early fire** (`gcd_stage1_full_dvd_prefix_mul_largePart`, `firing_by_cutoff_ge`).
  All but a factor `s = ∏ {q^{v_q(m)} : q ∣ m, q > L}` of the firing points already
  fire by cutoff `L`.  Orders whose large-prime part is small therefore fire in the
  first few percent of the schedule — quantitatively, not just qualitatively.
* **Multi-curve amplification** (`card_multiCurve_success`, `multiCurve_rate`).
  With `c` independent points the success count is exactly `m^c - (m - gcd(m,k))^c`,
  i.e. the rate is exactly `1 - (1 - ρ)^c` with `ρ = gcd(m,k)/m`.
* **The collision model is subdominant** (`orderCompletion_beats_collision_heuristic`).
  A single explicit order shows the order-completion rate exceeding the heuristic
  collision rate `≈ 1.44·B/m` by a factor `> 25`; the two models are not perturbations
  of one another.
-/

open ECMStage1

open Finset

/-! ## The exact firing count in a cyclic group of order `m` -/





/-! ## The gcd staircase: flatness between prime divisors -/

theorem ECMStage1.jumpSet_eq_primeFactors_filter{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) :
    jumpSet m B = m.primeFactors.filter (fun q => q ≤ B) := by sorry
