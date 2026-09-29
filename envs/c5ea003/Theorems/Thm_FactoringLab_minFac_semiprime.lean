-- Prove2me | Theorems.Thm_FactoringLab_minFac_semiprime
-- name    : FactoringLab.minFac_semiprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:25.103421+00:00
-- url     : https://prove2.me/theorems/d286374b-8907-43b3-b82f-3621b92cd89e
-- title:
--   For distinct primes `p < q`, the least prime factor of the semiprime `p*q`
-- statement:
--   For distinct primes `p < q`, the least prime factor of the semiprime `p*q`
--   is `p`.
--
--   ```lean
--   theorem FactoringLab.minFac_semiprime{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
--       (p * q).minFac = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/BarrierBoundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/BarrierBoundary.lean#L28

-- Thm stub generated from Probability/BarrierBoundary.lean
import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
/-
# Adversarial review: where the barriers stop

This file is the Critic's contribution: it delimits precisely what the
structural-orthogonality framework does and does not say.

1. **The barriers are not information-theoretic.**  The smaller prime factor
   *is* a function of `N` alone (`FactoringLab.smaller_factor_is_N_only`,
   witnessed by `Nat.minFac`).  So "any computable function of `N` alone is
   `N`-only" must be read structurally, not informationally: what the proved
   barriers exclude are *specific structured classes* of such functions
   (polynomial, rational, holomorphically rigid, symmetric-power-sum).
2. **The near-equal-`N` test needs genuinely coarse bands.**  If the band label
   separates the population points (`Function.Injective` on `Ω`), the band mean
   reproduces the target exactly (`FactoringLab.bandMean_eq_self_of_injOn`) and
   the residual vanishes, so the test is vacuous.
3. **The constant-band-mean hypothesis is necessary.**  Without it an `N`-only
   invariant can have strictly nonzero covariance with the smaller factor:
   `FactoringLab.cov_pos_counterexample` exhibits `Ω = {6, 15}` with covariance
   `9/4 > 0`.
-/

open FactoringLab

/-! ### The barrier is structural, not informational -/

theorem FactoringLab.minFac_semiprime{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p * q).minFac = p := by sorry
