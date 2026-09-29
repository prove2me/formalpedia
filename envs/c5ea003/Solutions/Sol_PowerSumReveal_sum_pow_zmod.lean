-- Prove2me | solution 1 for PowerSumReveal.sum_pow_zmod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:44:30.958145+00:00
-- url     : https://prove2.me/submissions/6f659bb7-1991-4775-9f91-d816d07a55d7

-- Sol generated from Geometry/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal

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
theorem solution(p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k ≠ 0) :
    ∑ x : ZMod p, x ^ k = if (p - 1) ∣ k then -1 else 0 := by
  classical
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using isUnit_iff_ne_zero
  calc ∑ x : ZMod p, x ^ k = ∑ x ∈ univ \ {(0 : ZMod p)}, x ^ k := by
        rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, zero_pow hk,
          add_zero]
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ k) := by simp [φ, ← hmap, univ.sum_map φ]
    _ = if (p - 1) ∣ k then -1 else 0 := by
        rw [FiniteField.sum_pow_units (ZMod p) k, hcard]
