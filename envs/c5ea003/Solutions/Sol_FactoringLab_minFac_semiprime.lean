-- Prove2me | solution 1 for FactoringLab.minFac_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:50:27.592147+00:00
-- url     : https://prove2.me/submissions/b510d945-1e37-4bf5-9700-5877bb40b843

-- Sol generated from Probability/BarrierBoundary.lean
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



/-! ### The near-equal-`N` test is vacuous for fine bands -/

variable {ι κ : Type*} [DecidableEq κ]



/-! ### The constant-band-mean hypothesis cannot be dropped -/



open FactoringLab in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p * q).minFac = p := by
  have hN1 : p * q ≠ 1 := by
    have := hp.two_le; have := hq.two_le; nlinarith
  have hdvd : (p * q).minFac ∣ p * q := Nat.minFac_dvd _
  have hprime : ((p * q).minFac).Prime := Nat.minFac_prime hN1
  have hle : (p * q).minFac ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le ⟨q, rfl⟩
  rcases (Nat.Prime.dvd_mul hprime).1 hdvd with h | h
  · exact ((Nat.prime_dvd_prime_iff_eq hprime hp).1 h)
  · have : q ≤ p := Nat.le_of_dvd hp.pos (by
      rw [(Nat.prime_dvd_prime_iff_eq hprime hq).1 h] at hle
      exact absurd hle (by omega))
    omega
