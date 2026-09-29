-- Prove2me | solution 1 for ECMStage1.card_firingSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:35:37.032651+00:00
-- url     : https://prove2.me/submissions/0e6b0b00-7542-4257-8b00-88be33e87ce7

-- Sol generated from Shared/ECMStage1FiringRate.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1OrderCompletion
import Theorems.Thm_ECMStage1_mem_firingSet_iff

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
theorem solution(m k : ℕ) (hm : 0 < m) : (firingSet m k).card = Nat.gcd m k := by
  set g := Nat.gcd m k with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left k hm
  set d := m / g with hd
  have hdg : d * g = m := by rw [hd]; exact Nat.div_mul_cancel (Nat.gcd_dvd_left m k)
  have hdpos : 0 < d := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m k)) hg
  have himg : firingSet m k = (Finset.range g).image (fun j => d * j) := by
    ext a
    rcases Nat.lt_or_ge a m with ha | ha
    · rw [mem_firingSet_iff hm ha]
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j, by nlinarith [hdg], rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact Dvd.intro j rfl
    · have hnot : a ∉ firingSet m k := by
        simp only [firingSet, Finset.mem_filter, Finset.mem_range]
        omega
      have hnot' : a ∉ (Finset.range g).image (fun j => d * j) := by
        simp only [Finset.mem_image, Finset.mem_range]
        rintro ⟨j, hj, rfl⟩
        nlinarith [hdg]
      simp [hnot, hnot']
  rw [himg, Finset.card_image_of_injective _ (mul_right_injective₀ hdpos.ne'), Finset.card_range]
