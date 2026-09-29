-- Prove2me | solution 1 for ECMStage1.gcd_stage1_full_dvd_prefix_mul_largePart
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:47:50.846693+00:00
-- url     : https://prove2.me/submissions/57d487cd-85e2-4ce4-8ce2-93488e18b78f

-- Sol generated from Shared/ECMStage1FiringRate.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1OrderCompletion
import Theorems.Thm_ECMStage1_factorization_prod_primePow
import Theorems.Thm_ECMStage1_stage1_factorization
import Theorems.Thm_ECMStage1_stage1_ne_zero

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


theorem largePart_ne_zero (m L : ℕ) : largePart m L ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ ?_
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos.ne'

theorem largePart_factorization (m L r : ℕ) :
    (largePart m L).factorization r =
      if r ∈ m.primeFactors ∧ L < r then m.factorization r else 0 := by
  rw [largePart, factorization_prod_primePow
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) _ r]
  simp [Finset.mem_filter, and_comm]



/-! ## Several curves -/



/-! ## The collision heuristic is the wrong model -/






open ECMStage1 in
theorem solution{m B L : ℕ} (hm : m ≠ 0) (hL : L ≤ B) :
    Nat.gcd m (stage1 B B) ∣ Nat.gcd m (stage1 B L) * largePart m L := by
  have hne1 : Nat.gcd m (stage1 B B) ≠ 0 := Nat.gcd_ne_zero_left hm
  have hne2 : Nat.gcd m (stage1 B L) * largePart m L ≠ 0 :=
    Nat.mul_ne_zero (Nat.gcd_ne_zero_left hm) (largePart_ne_zero m L)
  rw [← Nat.factorization_le_iff_dvd hne1 hne2, Finsupp.le_def]
  intro r
  by_cases hr : r.Prime
  · rw [Nat.factorization_mul (Nat.gcd_ne_zero_left hm) (largePart_ne_zero m L)]
    rw [Nat.factorization_gcd hm (stage1_ne_zero B B), Nat.factorization_gcd hm
      (stage1_ne_zero B L)]
    simp only [Finsupp.inf_apply, Finsupp.add_apply]
    rw [stage1_factorization B B hr, stage1_factorization B L hr,
      largePart_factorization m L r]
    by_cases hrL0 : r ≤ L
    · have hrB : r ≤ B := hrL0.trans hL
      simp [hrL0, hrB]
    · have hrL : L < r := by omega
      by_cases hmr : r ∈ m.primeFactors
      · have h1 : min (m.factorization r) (if r ≤ B then Nat.log r B else 0)
            ≤ m.factorization r := min_le_left _ _
        rw [if_pos (⟨hmr, hrL⟩ : r ∈ m.primeFactors ∧ L < r)]
        omega
      · have hz : m.factorization r = 0 := by
          simp only [Nat.mem_primeFactors, not_and, not_not] at hmr
          exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hm (hmr hr hd))
        simp [hz]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hr]
