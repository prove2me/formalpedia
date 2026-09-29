-- Prove2me | solution 1 for ECMStage1.mem_firingSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:33:01.30053+00:00
-- url     : https://prove2.me/submissions/292de024-b376-413b-bd38-1456555b0239

-- Sol generated from Shared/ECMStage1FiringRate.lean
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









/-! ## Early fire, quantitatively -/






/-! ## Several curves -/



/-! ## The collision heuristic is the wrong model -/






open ECMStage1 in
theorem solution{m k a : ℕ} (hm : 0 < m) (ha : a < m) :
    a ∈ firingSet m k ↔ (m / Nat.gcd m k) ∣ a := by
  have key : m ∣ k * a ↔ (m / Nat.gcd m k) ∣ a := by
    set g := Nat.gcd m k with hgdef
    have hg : 0 < g := Nat.gcd_pos_of_pos_left k hm
    have hmg : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m k)
    have hkg : g * (k / g) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_right m k)
    have hcop : Nat.Coprime (m / g) (k / g) := Nat.coprime_div_gcd_div_gcd hg
    constructor
    · intro h
      rw [← hmg, ← hkg, mul_assoc] at h
      exact hcop.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_left hg).mp h)
    · intro h
      rw [← hmg, ← hkg, mul_assoc]
      exact Nat.mul_dvd_mul_left g (Dvd.dvd.mul_left h _)
  simp [firingSet, ha, key]
