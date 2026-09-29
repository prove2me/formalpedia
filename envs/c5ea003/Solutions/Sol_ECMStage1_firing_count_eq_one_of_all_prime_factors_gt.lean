-- Prove2me | solution 1 for ECMStage1.firing_count_eq_one_of_all_prime_factors_gt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:47:48.359253+00:00
-- url     : https://prove2.me/submissions/41dfd104-1bbd-41f7-8ba4-2da89cd2ed1b

-- Sol generated from Shared/ECMStage1SmoothPart.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1OrderCompletion
import Theorems.Thm_ECMStage1_dvd_stage1Scalar_iff

/-!
# The smooth part is the whole story: structure of the stage-1 firing count

Two files up we showed that stage-1 firing is the divisibility `orderOf g ∣ k(B)`, and
that the number of firing points of a cyclic group of order `m` is exactly `gcd(m, k(B))`.
This file identifies that number structurally and pushes the picture to the group shape
that actually occurs for elliptic curves over a prime field (a product of at most two
cyclic groups), and to the analytic comparison with the collision heuristic.

* `gcd_stage1Scalar_isGreatest`: `gcd(m, k(B))` **is** the largest `B`-powersmooth
  divisor of `m`, in the divisibility order.  So "how often does stage 1 fire" is
  literally "how big is the powersmooth part of the order".
* `firing_count_eq_one_of_all_prime_factors_gt`: if every prime factor of the order
  exceeds the bound, the firing count collapses to `1` (only the identity).  This is
  the `found_q` control in exact form: at the large prime factor of the modulus,
  order completion contributes a rate of `1/m`, so any hits there measure something
  else entirely.
* `card_firingSet_prod`: for a rank-two group `ℤ/m₁ × ℤ/m₂` — the actual shape of
  `E(𝔽_p)` — the firing count is the product `gcd(m₁,k)·gcd(m₂,k)` of the two
  smooth parts, and it is at least as large as in the cyclic case
  (`rank_two_fires_at_least_as_often`).
* `orderCompletion_exceeds_collision_baseline`: the analytic comparison.  Since
  `1 - exp(-x) ≤ x`, an order-completion rate above `1.44·B/m` provably exceeds the
  folklore collision baseline `1 - exp(-1.44·B/m)`; the numeric witness of the
  previous file is the special case `m = 720, B = 10`.
-/

open ECMStage1

open Finset

/-! ## The firing count is the powersmooth part of the order -/


/-- **The firing count is the largest powersmooth divisor.**  `gcd(m, k(B))` divides
`m`, is `B`-powersmooth, and every `B`-powersmooth divisor of `m` divides it. -/
theorem gcd_stage1Scalar_isGreatest {m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) :
    Nat.gcd m (stage1Scalar B) ∣ m ∧ Powersmooth B (Nat.gcd m (stage1Scalar B)) ∧
      ∀ d, d ∣ m → Powersmooth B d → d ∣ Nat.gcd m (stage1Scalar B) := by
  refine ⟨Nat.gcd_dvd_left _ _, ?_, ?_⟩
  · exact (dvd_stage1Scalar_iff (Nat.gcd_ne_zero_left hm) hB).mp (Nat.gcd_dvd_right _ _)
  · intro d hd hsm
    have hdz : d ≠ 0 := by
      rintro rfl
      exact hm (Nat.eq_zero_of_zero_dvd hd)
    exact Nat.dvd_gcd hd ((dvd_stage1Scalar_iff hdz hB).mpr hsm)



/-! ## Rank-two groups: the actual shape of `E(𝔽_p)` -/



/-! ## Against the collision baseline -/




open ECMStage1 in
theorem solution{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0)
    (hlarge : ∀ q ∈ m.primeFactors, B < q) : Nat.gcd m (stage1Scalar B) = 1 := by
  obtain ⟨-, hsm, -⟩ := gcd_stage1Scalar_isGreatest hm hB
  set d := Nat.gcd m (stage1Scalar B) with hd
  have hdz : d ≠ 0 := Nat.gcd_ne_zero_left hm
  by_contra hne
  obtain ⟨q, hq⟩ := Nat.exists_prime_and_dvd hne
  have hqd : q ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hq.1, hq.2, hdz⟩
  have hqm : q ∈ m.primeFactors :=
    Nat.primeFactors_mono (Nat.gcd_dvd_left m (stage1Scalar B)) hm hqd
  have h1 : q ^ d.factorization q ≤ B := hsm q hqd
  have h2 : 0 < d.factorization q :=
    Nat.Prime.factorization_pos_of_dvd hq.1 hdz hq.2
  have h3 : q ≤ q ^ d.factorization q := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ d.factorization q := Nat.pow_le_pow_right hq.1.pos h2
  have := hlarge q hqm
  omega
