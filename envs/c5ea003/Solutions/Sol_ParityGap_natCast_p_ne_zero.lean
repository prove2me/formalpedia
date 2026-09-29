-- Prove2me | solution 1 for ParityGap.natCast_p_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:59:14.913451+00:00
-- url     : https://prove2.me/submissions/0827a296-520b-4b4e-84ee-5ace52879201

-- Sol generated from Probability/CyclotomicRing.lean
import Mathlib
import Definitions.Def_Probability_CyclotomicRing
/-
# The ring `ℤ[ζ_p]` and its reduction modulo the prime `ζ - 1`

For the parity-gap / Chebotarev development we need an honest characteristic-zero model of
`ℤ[ζ_p]`, together with the reduction map onto `𝔽_p` that sends `ζ ↦ 1`.  Everything is built
by hand from `AdjoinRoot (cyclotomic p ℤ)`, so no algebraic number theory is imported:

* `ParityGap.CycRing p` — the ring `ℤ[X]/(Φ_p)`, a Noetherian domain;
* `ParityGap.zeta p` — the image of `X`, a primitive `p`-th root of unity in `CycRing p`;
* `ParityGap.red p : CycRing p →+* ZMod p` — the reduction sending `ζ ↦ 1`;
* `ParityGap.pi p = ζ - 1` — the ramified prime, with `red` vanishing exactly on multiples of it
  (`ParityGap.pi_dvd_of_red_eq_zero`);
* `ParityGap.exists_primitive_scaling` — every nonzero vector over `CycRing p` can be divided by
  a power of `π` so that at least one coordinate survives reduction.  This uses the Krull
  intersection theorem, which is where Noetherianity enters.
-/


open Polynomial

open ParityGap

variable (p : ℕ) [hp : Fact p.Prime]






















open ParityGap in
theorem solution: (p : CycRing p) ≠ 0 := by
  intro h
  have hmk : (AdjoinRoot.mk (cyclotomic p ℤ)) ((p : ℕ) : ℤ[X]) = 0 := by
    rw [map_natCast]; exact h
  have hdvd : cyclotomic p ℤ ∣ ((p : ℕ) : ℤ[X]) := AdjoinRoot.mk_eq_zero.mp hmk
  have hne : ((p : ℕ) : ℤ[X]) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℤ)).mpr hp.out.ne_zero
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  rw [natDegree_cyclotomic] at hle
  have : p.totient = p - 1 := Nat.totient_prime hp.out
  have h2 := hp.out.two_le
  simp only [Polynomial.natDegree_natCast] at hle
  omega
