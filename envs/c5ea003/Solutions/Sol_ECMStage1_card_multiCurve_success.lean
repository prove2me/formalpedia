-- Prove2me | solution 1 for ECMStage1.card_multiCurve_success
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:42:05.703643+00:00
-- url     : https://prove2.me/submissions/b71f1dc9-2f04-4e46-bc32-8b67b5dd533e

-- Sol generated from Shared/ECMStage1FiringRate.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1OrderCompletion
import Theorems.Thm_ECMStage1_card_firingSet

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
theorem solution(m k c : ℕ) (hm : 0 < m) :
    ((Fintype.piFinset (fun _ : Fin c => Finset.range m)).filter
        (fun a => ∃ i, m ∣ k * a i)).card = m ^ c - (m - Nat.gcd m k) ^ c := by
  classical
  have hfail : (Fintype.piFinset (fun _ : Fin c => Finset.range m)).filter
      (fun a => ¬ ∃ i, m ∣ k * a i)
      = Fintype.piFinset (fun _ : Fin c => (Finset.range m).filter (fun a => ¬ m ∣ k * a)) := by
    ext a
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_filter, not_exists]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  have hcardfail : (Fintype.piFinset
      (fun _ : Fin c => (Finset.range m).filter (fun a => ¬ m ∣ k * a))).card
      = (m - Nat.gcd m k) ^ c := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.range m) (p := fun a => m ∣ k * a)
    rw [Finset.card_range] at this
    have h2 : (firingSet m k).card = Nat.gcd m k := card_firingSet m k hm
    simp only [firingSet] at h2
    omega
  have htot : (Fintype.piFinset (fun _ : Fin c => Finset.range m)).card = m ^ c := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.card_range]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Fintype.piFinset (fun _ : Fin c => Finset.range m)) (p := fun a => ∃ i, m ∣ k * a i)
  rw [htot, hfail, hcardfail] at hsplit
  omega
