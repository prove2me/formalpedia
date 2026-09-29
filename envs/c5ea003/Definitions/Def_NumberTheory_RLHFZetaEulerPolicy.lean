-- Prove2me | Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
-- name    : NumberTheory_RLHFZetaEulerPolicy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:47.32371+00:00
-- url     : https://prove2.me/theorems/00fee453-2cc8-4fe5-8bd1-08abf68d2250
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFZetaEulerPolicy
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFZetaEulerPolicy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFZetaEulerPolicy.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational

/-!
# Euler products from RLHF: the zeta policy on smooth-number response spaces

We instantiate the Gibbs variational principle of `NumberTheory.RLHFGibbsVariational`
with an arithmetic reward model.  The response space is the set of `{p, q}`-smooth
integers `p^a q^b` with bounded exponents, the SFT reference is uniform, and the reward is
the logarithmic (Dirichlet) reward `r(n) = -β s log n`.

The optimal (Gibbs) policy is then the **truncated zeta distribution** `π(n) ∝ n^{-s}`, and
the number-theoretic Euler product manifests itself as a *statistical independence* of the
prime exponents under the aligned policy, together with an *additive* decomposition of the
RLHF free energy over primes.

Main results:

* `RLHF.zeta_partition_factorizes` — Euler factorization of the normalizing constant.
* `RLHF.gibbs_zeta_policy` — the optimal RLHF policy is exactly `n^{-s} / ∑ n^{-s}`.
* `RLHF.gibbs_zeta_independent` — under the optimal policy the prime exponents are
  independent (the policy is a product of two truncated geometric laws).
* `RLHF.freeEnergy_euler_additive` — the RLHF free energy splits additively over the primes.
* `RLHF.smoothVal_injective` — unique factorization: the response space really is a set of
  distinct integers.
* `RLHF.euler_factor_tsum` — removing the exponent cutoff, the local partition function is
  the classical Euler factor `(1 - p^{-s})⁻¹`.
-/

namespace RLHF

open Finset

/-! ## 1. Uniform reference policies -/

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDist (Ω : Type*) [Fintype Ω] : Ω → ℝ :=
  fun _ => 1 / (Fintype.card Ω : ℝ)


/-! ## 2. The smooth-number response space -/

variable {A B : ℕ}

/-- The response space: pairs of bounded prime exponents. -/
abbrev Smooth (A B : ℕ) := Fin (A + 1) × Fin (B + 1)

/-- The integer named by a pair of exponents. -/
def smoothVal (p q : ℕ) (ab : Smooth A B) : ℕ := p ^ (ab.1 : ℕ) * q ^ (ab.2 : ℕ)



/-! ## 3. The Dirichlet (log) reward and the truncated zeta weights -/

/-- The Dirichlet reward model: `r(n) = -β s log n`.  Maximizing reward means preferring
*small* integers, with `s` the sharpness of the preference. -/
noncomputable def zetaReward (β s : ℝ) (p q : ℕ) : Smooth A B → ℝ :=
  fun ab => -(β * s) * Real.log (smoothVal p q ab : ℝ)

/-- The truncated zeta weight `n ↦ n^{-s}`. -/
noncomputable def zetaWeight (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-s)

/-- The truncated zeta normalizing constant over the smooth response space. -/
noncomputable def zetaSum (s : ℝ) (p q : ℕ) (A B : ℕ) : ℝ :=
  ∑ ab : Smooth A B, zetaWeight s (smoothVal p q ab)

/-- The local (single prime) partition function with exponents bounded by `A`. -/
noncomputable def localZeta (s : ℝ) (p : ℕ) (A : ℕ) : ℝ :=
  ∑ a : Fin (A + 1), zetaWeight s (p ^ (a : ℕ))






/-! ## 4. The optimal RLHF policy is the truncated zeta distribution -/





/-! ## 5. Additivity of the free energy over primes -/



/-! ## 6. Closed forms and the classical Euler factor -/






end RLHF


