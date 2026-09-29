-- Prove2me | solution 1 for ECMStage1.card_jumpSet_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:42:05.148404+00:00
-- url     : https://prove2.me/submissions/7b6e19cf-5eae-4db3-b6a2-a47b5d8b8c05

-- Sol generated from Shared/ECMStage1FiringRate.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1OrderCompletion
import Theorems.Thm_ECMStage1_gcd_stage1_flat

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



/-- **Jumps happen only at prime divisors of the order.**  Every step of the schedule
at which the firing count grows is a prime dividing `m`. -/
theorem jumpSet_subset_primeFactors {m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) :
    jumpSet m B ⊆ m.primeFactors := by
  intro C hC
  simp only [jumpSet, Finset.mem_filter, Finset.mem_range] at hC
  by_contra hCm
  refine hC.2 (gcd_stage1_flat hm hB (Nat.sub_le C 1) ?_).symm
  intro q hq hqC
  rcases Nat.lt_or_ge (C - 1) q with h | h
  · exfalso
    have : q = C := by omega
    exact hCm (this ▸ hq)
  · exact h


/-- Hence at most `ω(m)` of the `π(B)` schedule steps are firing positions, and
`ω(m) ≤ log₂ m`. -/
theorem card_primeFactors_le_log_two {m : ℕ} (hm : m ≠ 0) :
    m.primeFactors.card ≤ Nat.log 2 m := by
  have h1 : 2 ^ m.primeFactors.card ≤ ∏ q ∈ m.primeFactors, q := by
    calc 2 ^ m.primeFactors.card = ∏ _q ∈ m.primeFactors, 2 := by
          rw [Finset.prod_const]
      _ ≤ ∏ q ∈ m.primeFactors, q :=
          Finset.prod_le_prod' (fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le)
  have h2 : ∏ q ∈ m.primeFactors, q ≤ m :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)
  exact (Nat.le_log_iff_pow_le one_lt_two hm).mpr (h1.trans h2)




/-! ## Early fire, quantitatively -/






/-! ## Several curves -/



/-! ## The collision heuristic is the wrong model -/






open ECMStage1 in
theorem solution{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) :
    (jumpSet m B).card ≤ m.primeFactors.card ∧ m.primeFactors.card ≤ Nat.log 2 m :=
  ⟨Finset.card_le_card (jumpSet_subset_primeFactors hm hB), card_primeFactors_le_log_two hm⟩
