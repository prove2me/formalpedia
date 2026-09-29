-- Prove2me | Definitions.Def_Shared_ECMStage1FiringRate
-- name    : Shared_ECMStage1FiringRate
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:49:49.492753+00:00
-- url     : https://prove2.me/theorems/ab77db25-d4dd-4c27-a290-184f8ef6906f
-- title:
--   Aether Catalog definitions — Shared_ECMStage1FiringRate
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ECMStage1FiringRate`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ECMStage1FiringRate.lean by skeleton subtraction
import Mathlib
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

namespace ECMStage1

open Finset

/-! ## The exact firing count in a cyclic group of order `m` -/

/-- The residues mod `m` killed by the scalar `k`, i.e. the points on which a stage-1
run with scalar `k` fires. -/
def firingSet (m k : ℕ) : Finset ℕ := (Finset.range m).filter (fun a => m ∣ k * a)




/-! ## The gcd staircase: flatness between prime divisors -/


/-- The cutoffs at which the cumulative firing count actually increases. -/
def jumpSet (m B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter
    (fun C => Nat.gcd m (stage1 B C) ≠ Nat.gcd m (stage1 B (C - 1)))







/-! ## Early fire, quantitatively -/

/-- The part of `m` supported on primes above `L`. -/
def largePart (m L : ℕ) : ℕ :=
  ∏ q ∈ m.primeFactors.filter (fun q => L < q), q ^ m.factorization q





/-! ## Several curves -/



/-! ## The collision heuristic is the wrong model -/





end ECMStage1


