-- Prove2me | solution 1 for SiegelWeilE8Contrarian.sigma3_eq_lower_bound_iff_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:18:03.795979+00:00
-- url     : https://prove2.me/submissions/fd60652d-0f2d-4e5b-a2c9-edea1c512cd9

-- Sol generated from Applications/SiegelWeilE8ThetaContrarian.lean
import Mathlib
import Definitions.Def_Applications_SiegelWeilE8ThetaContrarian

/-!
# Contrarian conjectures around the `E₈` / Siegel–Weil theta series

The companion file `SiegelWeilE8Theta.lean` establishes that the `E₈` vector
counts `rE8 n = 240·σ₃(n)` form the coefficient system of the weight-`4` Hecke
eigenform `E₄` (prime-power geometric form, Hecke three-term recurrence,
multiplicativity, and the global Hecke convolution identity).

Following the *contrarian* mandate, this file stress-tests bold conjectures about
that arithmetic system.  We both **prove** several nontrivial structural facts
and **disprove** two natural-looking but false strengthenings.

## Proved

* `sigma3_mod_six` — the congruence `σ₃(n) ≡ σ₁(n) (mod 6)`, a hidden linear
  relation between the weight-`4` and weight-`2` divisor systems, coming from
  `d³ ≡ d (mod 6)`.
* `sigma3_ge_cube` / `sigma3_ge` — the lower bounds `n³ ≤ σ₃(n)` and
  `n³ + 1 ≤ σ₃(n)` for `n ≥ 2`.
* `sigma3_eq_lower_bound_iff_prime` — the lower bound `σ₃(n) = n³ + 1` is attained
  **exactly** at the primes: a characterization of primality via the `E₄`
  Fourier coefficients.
* `rE8_ge_cube` — the E₈ vector count grows at least like `240·n³`.

## Disproved (contrarian counterexamples)

* `rE8_not_multiplicative` — the E₈ count `rE8` is *not* multiplicative; the
  correct coprime law necessarily carries the normalizing factor `240`.
* `hecke_recurrence_composite_fails` — the Hecke three-term recurrence genuinely
  **requires** primality of the base; it fails at `p = 6`.

See `FUTURE_DIRECTIONS.md` for the flagship open target `E₄² = E₈`
(`σ₇(n) = σ₃(n) + 120·∑ σ₃(m)σ₃(n−m)`), verified numerically here.
-/

open SiegelWeilE8Contrarian

open ArithmeticFunction Finset


/-! ### A hidden congruence between σ₃ and σ₁ -/



/-! ### Lower bounds and the prime characterization -/





/-! ### Contrarian disproofs -/



/-! ### Low-order corroboration -/



open SiegelWeilE8Contrarian in
theorem solution(n : ℕ) (hn : 2 ≤ n) :
    (sigma 3) n = n ^ 3 + 1 ↔ n.Prime := by
  constructor
  · intro heq
    by_contra hnp
    obtain ⟨d, hd, hd2, hdn⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
    have hsub : ({1, d, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Nat.one_mem_divisors.mpr (by omega)
      · exact Nat.mem_divisors.mpr ⟨hd, by omega⟩
      · exact Nat.mem_divisors_self _ (by omega)
    have hsum : ∑ x ∈ ({1, d, n} : Finset ℕ), x ^ 3 = 1 + d ^ 3 + n ^ 3 := by
      rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
        Finset.sum_singleton]; ring
    have hle : ∑ x ∈ ({1, d, n} : Finset ℕ), x ^ 3 ≤ (sigma 3) n := by
      rw [sigma_apply]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
    rw [hsum] at hle
    have : 2 ^ 3 ≤ d ^ 3 := Nat.pow_le_pow_left hd2 3
    omega
  · intro hp
    rw [sigma_apply, hp.divisors, Finset.sum_pair (by
      rintro rfl; exact absurd hp (by norm_num))]
    ring
