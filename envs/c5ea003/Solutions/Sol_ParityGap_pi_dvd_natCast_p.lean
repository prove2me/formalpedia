-- Prove2me | solution 1 for ParityGap.pi_dvd_natCast_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:54:05.444709+00:00
-- url     : https://prove2.me/submissions/84cb0fa6-6771-491c-a7f9-b09f93bd8fae

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
theorem solution: pi p ∣ (p : CycRing p) := by
  obtain ⟨q, hq⟩ :
      (X - C (1 : ℤ)) ∣ (cyclotomic p ℤ) - C ((cyclotomic p ℤ).eval 1) :=
    X_sub_C_dvd_sub_C_eval
  have hmap := congrArg (AdjoinRoot.mk (cyclotomic p ℤ)) hq
  simp only [map_sub, AdjoinRoot.mk_self, map_mul, AdjoinRoot.mk_X, map_one, AdjoinRoot.mk_C]
    at hmap
  rw [eval_one_cyclotomic_prime] at hmap
  refine ⟨-(AdjoinRoot.mk (cyclotomic p ℤ) q), ?_⟩
  have hz : (AdjoinRoot.root (cyclotomic p ℤ) : CycRing p) = zeta p := rfl
  have hcast : (AdjoinRoot.of (cyclotomic p ℤ)) ((p : ℕ) : ℤ) = (p : CycRing p) := by
    simp
  rw [hz] at hmap
  rw [pi]
  rw [← hcast]
  linear_combination -hmap
