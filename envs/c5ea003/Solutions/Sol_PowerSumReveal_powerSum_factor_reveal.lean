-- Prove2me | solution 1 for PowerSumReveal.powerSum_factor_reveal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:48.393531+00:00
-- url     : https://prove2.me/submissions/bacae3b7-2665-4a6c-b42c-05db6e435b4f

-- Sol generated from Geometry/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_gcd_powerSum_semiprime

/-!
# Power-sum GCD factor reveal

For a modulus `N` put

`powerSum N k = ∑_{a = 1}^{N} a ^ k`.

The main result of this file is a *complete* description of `gcd (powerSum N k) N`
when `N = p * q` is a semiprime and `k ≥ 1`:

`gcd (powerSum (p*q) k, p*q) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`.

The mechanism is a two-step reduction.

* *Periodicity.* The interval `[1, N]` with `N = p * m` covers every residue class
  modulo `p` exactly `m` times, so `powerSum (p*m) k ≡ m * ∑_{x ∈ ZMod p} x^k (mod p)`.
* *Fermat.* For `k ≥ 1`, `∑_{x ∈ ZMod p} x^k = -1` if `(p-1) ∣ k` and `= 0` otherwise.

Consequently `p ∣ powerSum (p*m) k ↔ ¬ (p-1) ∣ k` (when `p ∤ m`), and the gcd formula
follows from multiplicativity of `Nat.gcd` over coprime factors.

Specialising to `k = p - 1` gives the advertised **factor reveal**:
`gcd (powerSum (p*q) (p-1), p*q) = q` whenever `(q-1) ∤ (p-1)`.

## Main results

* `PowerSumReveal.sum_pow_zmod` — Fermat power-sum over `ZMod p`.
* `PowerSumReveal.powerSum_cast` — the periodicity reduction, in `ZMod p`.
* `PowerSumReveal.prime_dvd_powerSum_iff` — divisibility criterion.
* `PowerSumReveal.gcd_powerSum_semiprime` — the master gcd formula.
* `PowerSumReveal.powerSum_factor_reveal` — Theorem 1 (factor reveal at `k = p-1`).
-/

open PowerSumReveal

open Finset



/-! ## Step 1: the Fermat power sum over `ZMod p` -/


/-! ## Step 2: periodicity of `a ↦ a mod p` on an interval of length `p * m` -/





/-! ## Step 3: the divisibility criterion -/


/-! ## Step 4: the gcd formula -/



/-! ## Theorem 1: the factor reveal -/





open PowerSumReveal in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdvd : ¬ (q - 1) ∣ (p - 1)) :
    Nat.gcd (powerSum (p * q) (p - 1)) (p * q) = q := by
  have hk : p - 1 ≠ 0 := by
    have := hp.two_le; omega
  rw [gcd_powerSum_semiprime hp hq hpq hk, if_pos dvd_rfl, if_neg hdvd, one_mul]
