-- Prove2me | Definitions.Def_Probability_MeromorphicRigidity
-- name    : Probability_MeromorphicRigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:25:45.186443+00:00
-- url     : https://prove2.me/theorems/4721629f-6659-4808-b3dd-daa384c3c952
-- title:
--   Aether Catalog definitions — Probability_MeromorphicRigidity
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.MeromorphicRigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/MeromorphicRigidity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
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

namespace FactoringLab

/-! ## 1.  Reciprocals of a diverging integer sequence accumulate at `0` -/


/-! ## 2.  A prime family above `5` -/

/-- Primes strictly larger than `5`, indexed by `ℕ`. -/
noncomputable def hugePrime (n : ℕ) : ℕ := bigPrime (n + 2)





/-! ## 3.  The meromorphic rigidity barrier -/





end FactoringLab


