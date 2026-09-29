-- Prove2me | solution 1 for Bridges.AlexanderTorus.dvd_of_alexander_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:33:30.806412+00:00
-- url     : https://prove2.me/submissions/50a11c31-68d7-4a30-8e52-022dc9971df8

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
open Bridges.AlexanderTorus Polynomial in
theorem solution {d M : ℕ} (hd : Odd d) (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M)
    (h : alexander d ∣ alexander M) : d ∣ M := by
  -- `Δ_N(z) (z + 1) = z^N + 1` for odd `N` (alternating geometric sum)
  have heval : ∀ N : ℕ, Odd N → ∀ z : ℂ, aeval z (alexander N) * (z + 1) = z ^ N + 1 := by
    intro N hN z
    have hs : aeval z (alexander N) = ∑ i ∈ Finset.range N, (-z) ^ i := by
      unfold alexander
      simp only [map_sum, map_mul, map_pow, map_neg, map_one, aeval_X]
      exact Finset.sum_congr rfl fun i _ => (neg_pow z i).symm
    rw [hs]
    have hg := geom_sum_mul (-z) N
    rw [hN.neg_pow] at hg
    linear_combination -hg
  -- a primitive `2d`-th root of unity `ζ`: `ζ^d = -1` and `ζ ≠ -1`
  have h2d : (2 * d : ℕ) ≠ 0 := by omega
  have hζ := Complex.isPrimitiveRoot_exp (2 * d) h2d
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)) with hζdef
  have hζd : ζ ^ d = -1 :=
    (hζ.pow (by omega) (by ring : 2 * d = d * 2)).eq_neg_one_of_two_right
  have hζ1 : ζ + 1 ≠ 0 := by
    intro h0
    have hm : ζ = -1 := by linear_combination h0
    have hsq : ζ ^ 2 = 1 := by rw [hm]; norm_num
    have := hζ.dvd_of_pow_eq_one 2 hsq
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- `ζ` is a root of `Δ_d`, hence of `Δ_M`
  have hroot_d : aeval ζ (alexander d) = 0 := by
    have := heval d hd ζ
    rw [hζd, neg_add_cancel] at this
    exact (mul_eq_zero.mp this).resolve_right hζ1
  have hroot_M : aeval ζ (alexander M) = 0 := by
    obtain ⟨q, hq⟩ := h
    rw [hq, map_mul, hroot_d, zero_mul]
  have hζM : ζ ^ M = -1 := by
    have := heval M hM ζ
    rw [hroot_M, zero_mul] at this
    linear_combination -this
  -- so `ζ^(2M) = 1`, i.e. `2d ∣ 2M`
  have h2M : ζ ^ (2 * M) = 1 := by
    rw [mul_comm, pow_mul, hζM]
    norm_num
  have := hζ.dvd_of_pow_eq_one _ h2M
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
