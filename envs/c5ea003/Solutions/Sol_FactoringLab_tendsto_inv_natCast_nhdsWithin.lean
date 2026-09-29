-- Prove2me | solution 1 for FactoringLab.tendsto_inv_natCast_nhdsWithin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:47:46.19272+00:00
-- url     : https://prove2.me/submissions/c01aedb7-4743-4c46-925d-2821ab4c219f

-- Sol generated from Probability/MeromorphicRigidity.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
import Definitions.Def_Probability_MeromorphicRigidity
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






/-! ## 3.  The meromorphic rigidity barrier -/






open FactoringLab in
theorem solution{m : ℕ → ℕ} (hpos : ∀ n, 0 < m n)
    (htop : Tendsto m atTop atTop) :
    Tendsto (fun n => ((m n : ℕ) : ℂ)⁻¹) atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
  have hreal : Tendsto (fun n => ((m n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htop
  have hnorm : Tendsto (fun n => ‖((m n : ℕ) : ℂ)⁻¹‖) atTop (nhds 0) := by
    have heq : ∀ n, ‖((m n : ℕ) : ℂ)⁻¹‖ = ((m n : ℕ) : ℝ)⁻¹ := by
      intro n; rw [norm_inv, Complex.norm_natCast]
    simp only [heq]
    exact hreal.inv_tendsto_atTop
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_zero_iff_norm_tendsto_zero.2 hnorm) ?_
  filter_upwards with n
  have hne : ((m n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hpos n).ne'
  simpa using inv_ne_zero hne
