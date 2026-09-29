-- Prove2me | Theorems.Thm_FactoringLab_meromorphic_rigidity_two_families
-- name    : FactoringLab.meromorphic_rigidity_two_families
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:24.424524+00:00
-- url     : https://prove2.me/theorems/934ec1d6-e445-4db0-ba91-80e721df3c5b
-- title:
--   Meromorphic rigidity barrier.
-- statement:
--   **Meromorphic rigidity barrier.**  There is no function `f` meromorphic at
--   `0` — in particular no entire function, no function of finite order and no
--   function with a pole of finite order at `0` — with `f(1/(pq)) = 1/p` for all
--   primes `p < q`.  Only the two families `p = 3` and `p = 5` are used.
--
--   ```lean
--   theorem FactoringLab.meromorphic_rigidity_two_families(f : ℂ → ℂ) (hf : MeromorphicAt f 0)
--       (h3 : ∀ q : ℕ, q.Prime → 3 < q → f (((3 * q : ℕ) : ℂ))⁻¹ = ((3 : ℕ) : ℂ)⁻¹)
--       (h5 : ∀ q : ℕ, q.Prime → 5 < q → f (((5 * q : ℕ) : ℂ))⁻¹ = ((5 : ℕ) : ℂ)⁻¹) :
--       False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/MeromorphicRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/MeromorphicRigidity.lean#L87

-- Thm stub generated from Probability/MeromorphicRigidity.lean
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

theorem FactoringLab.meromorphic_rigidity_two_families(f : ℂ → ℂ) (hf : MeromorphicAt f 0)
    (h3 : ∀ q : ℕ, q.Prime → 3 < q → f (((3 * q : ℕ) : ℂ))⁻¹ = ((3 : ℕ) : ℂ)⁻¹)
    (h5 : ∀ q : ℕ, q.Prime → 5 < q → f (((5 * q : ℕ) : ℂ))⁻¹ = ((5 : ℕ) : ℂ)⁻¹) :
    False := by sorry
