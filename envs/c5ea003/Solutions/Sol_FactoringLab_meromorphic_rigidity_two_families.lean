-- Prove2me | solution 1 for FactoringLab.meromorphic_rigidity_two_families
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:50:27.075146+00:00
-- url     : https://prove2.me/submissions/a4d5ac48-866f-4104-ab3b-55a283f83021

-- Sol generated from Probability/MeromorphicRigidity.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
import Definitions.Def_Probability_MeromorphicRigidity
import Theorems.Thm_FactoringLab_bigPrime_prime
import Theorems.Thm_FactoringLab_bigPrime_strictMono
import Theorems.Thm_FactoringLab_bigPrime_tendsto
import Theorems.Thm_FactoringLab_tendsto_inv_natCast_nhdsWithin
import Theorems.Thm_FactoringLab_tendsto_recip_semiprime
import Theorems.Thm_FactoringLab_three_lt_bigPrime
/-
# Meromorphic Rigidity (Factoring Lab, Phase A v19c — cycle 2)

Closing **Conjecture 2** of `FUTURE_DIRECTIONS.md`: the holomorphic rigidity
barrier survives the removal of entirety.

The previous cycle proved `FactoringLab.holomorphic_rigidity_barrier`: no
*entire* `f : ℂ → ℂ` satisfies `f(1/N) = 1/p` for every semiprime `N = pq`
with `p < q` prime.  The proof went through the identity theorem at the
accumulation point `0`, which needs `f` to be analytic *at* `0`.

Conjecture 2 asserted that this is an artifact: any function with an isolated,
non-essential singularity at `0` — i.e. any `f` meromorphic at `0`, which
includes every entire function, every finite-order entire function, every
rational function and every function with a pole of finite order — is already
pinned down by countably many values accumulating at `0`.  That is now the
theorem `FactoringLab.meromorphic_rigidity_barrier`, and the original HRB is
recovered from it as the corollary
`FactoringLab.holomorphic_rigidity_of_meromorphic`.

The mechanism replacing the identity theorem is Mathlib's dichotomy
`MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`: near an isolated
singularity a meromorphic function either vanishes identically or is nonzero on
a punctured neighbourhood.  The semiprimes `3q` force the first alternative for
`f − 1/3`; the semiprimes `5q` then contradict it.  Only the two families
`p = 3` and `p = 5` are used, so the barrier already applies to functions that
are only assumed to compute the factor for these two small primes
(`FactoringLab.meromorphic_rigidity_two_families`).
-/

open Filter Topology

open FactoringLab

/-! ## 1.  Reciprocals of a diverging integer sequence accumulate at `0` -/


/-! ## 2.  A prime family above `5` -/


theorem hugePrime_prime (n : ℕ) : (hugePrime n).Prime := bigPrime_prime (n + 2)

theorem five_lt_hugePrime (n : ℕ) : 5 < hugePrime n := by
  have h0 : 3 < bigPrime 0 := three_lt_bigPrime 0
  have h01 : bigPrime 0 < bigPrime 1 := bigPrime_strictMono (by omega)
  have h12 : bigPrime 1 < bigPrime 2 := bigPrime_strictMono (by omega)
  have h2n : bigPrime 2 ≤ bigPrime (n + 2) :=
    bigPrime_strictMono.monotone (by omega)
  unfold hugePrime
  omega

theorem hugePrime_tendsto : Tendsto hugePrime atTop atTop :=
  bigPrime_tendsto.comp (tendsto_add_atTop_nat 2)

/-- The reciprocals of the semiprimes `5q`, `q` prime above `5`, accumulate at
`0`. -/
theorem tendsto_recip_five_semiprime :
    Tendsto (fun n => (((5 * hugePrime n : ℕ) : ℂ))⁻¹) atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
  refine tendsto_inv_natCast_nhdsWithin (fun n => ?_) ?_
  · have := five_lt_hugePrime n; omega
  · exact Filter.tendsto_atTop_mono
      (fun n => Nat.le_mul_of_pos_left (hugePrime n) (by norm_num)) hugePrime_tendsto

/-! ## 3.  The meromorphic rigidity barrier -/






open FactoringLab in
theorem solution(f : ℂ → ℂ) (hf : MeromorphicAt f 0)
    (h3 : ∀ q : ℕ, q.Prime → 3 < q → f (((3 * q : ℕ) : ℂ))⁻¹ = ((3 : ℕ) : ℂ)⁻¹)
    (h5 : ∀ q : ℕ, q.Prime → 5 < q → f (((5 * q : ℕ) : ℂ))⁻¹ = ((5 : ℕ) : ℂ)⁻¹) :
    False := by
  set c : ℂ := ((3 : ℕ) : ℂ)⁻¹ with hc
  have hg : MeromorphicAt (fun z => f z - c) 0 := hf.sub (MeromorphicAt.const c 0)
  have hzero : ∀ n, f ((((3 * bigPrime n : ℕ) : ℂ))⁻¹) - c = 0 := by
    intro n
    rw [h3 (bigPrime n) (bigPrime_prime n) (three_lt_bigPrime n), sub_self]
  -- the second alternative of the meromorphic dichotomy is impossible
  have hnot : ¬ (∀ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, f z - c ≠ 0) := by
    intro hev
    have := tendsto_recip_semiprime.eventually hev
    obtain ⟨n, hn⟩ := this.exists
    exact hn (hzero n)
  have hall : ∀ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, f z - c = 0 :=
    hg.eventually_eq_zero_or_eventually_ne_zero.resolve_right hnot
  -- but the family `5q` also accumulates at `0`, and there `f = 1/5`
  obtain ⟨n, hn⟩ := (tendsto_recip_five_semiprime.eventually hall).exists
  rw [h5 (hugePrime n) (hugePrime_prime n) (five_lt_hugePrime n), sub_eq_zero] at hn
  rw [hc] at hn
  have h35 : ((5 : ℕ) : ℂ) = ((3 : ℕ) : ℂ) := inv_injective hn
  norm_num at h35
