-- Prove2me | solution 1 for PowerSumReveal.powerSum_cast
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:44:30.478651+00:00
-- url     : https://prove2.me/submissions/1ec94f9f-69c6-4099-a3c2-e55fba85ba23

-- Sol generated from Geometry/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_powerSum_cast_eq_range
import Theorems.Thm_PowerSumReveal_sum_range_modCast

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


/-- Over `m` full periods the residues repeat, so the sum is `m` copies of the
sum over `ZMod p`. -/
theorem sum_range_mul_modCast (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) (m : ℕ) :
    ∑ a ∈ range (p * m), f (a : ZMod p) = m • ∑ x : ZMod p, f x := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hpm : p * (m + 1) = p * m + p := by ring
      have base : ∑ a ∈ range p, f ((p * m + a : ℕ) : ZMod p) = ∑ x : ZMod p, f x := by
        have hshift : ∀ a : ℕ, ((p * m + a : ℕ) : ZMod p) = (a : ZMod p) := by
          intro a; push_cast [ZMod.natCast_self]; ring
        simp only [hshift]
        exact sum_range_modCast p f
      rw [hpm, Finset.sum_range_add, ih, base, succ_nsmul]



/-! ## Step 3: the divisibility criterion -/


/-! ## Step 4: the gcd formula -/



/-! ## Theorem 1: the factor reveal -/





open PowerSumReveal in
theorem solution(p m : ℕ) [NeZero p] {k : ℕ} (hk : k ≠ 0) :
    ((powerSum (p * m) k : ℕ) : ZMod p) = (m : ZMod p) * ∑ x : ZMod p, x ^ k := by
  have hN : ((p * m : ℕ) : ZMod p) = 0 := by push_cast [ZMod.natCast_self]; ring
  rw [powerSum_cast_eq_range p (p * m) hk hN,
    sum_range_mul_modCast p (fun x => x ^ k) m, nsmul_eq_mul]
