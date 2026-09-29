-- Prove2me | solution 1 for ParityGap.pi_dvd_of_red_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:56:50.993985+00:00
-- url     : https://prove2.me/submissions/9ad3f96b-36b7-4355-8628-c7c667e08fa5

-- Sol generated from Probability/CyclotomicRing.lean
import Mathlib
import Definitions.Def_Probability_CyclotomicRing
import Theorems.Thm_ParityGap_pi_dvd_natCast_p
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













@[simp] theorem red_mk (F : ℤ[X]) :
    red p (AdjoinRoot.mk (cyclotomic p ℤ) F) = ((F.eval 1 : ℤ) : ZMod p) := by
  rw [red, AdjoinRoot.lift_mk, eval₂_at_one]
  rfl









open ParityGap in
theorem solution{y : CycRing p} (h : red p y = 0) : pi p ∣ y := by
  induction y using AdjoinRoot.induction_on with
  | _ F =>
    rw [red_mk] at h
    obtain ⟨m, hm⟩ : (p : ℤ) ∣ F.eval 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (F.eval 1) p).mp h
      exact_mod_cast this
    obtain ⟨q, hq⟩ : (X - C (1 : ℤ)) ∣ F - C (F.eval 1) := X_sub_C_dvd_sub_C_eval
    have hmap := congrArg (AdjoinRoot.mk (cyclotomic p ℤ)) hq
    simp only [map_sub, map_mul, AdjoinRoot.mk_X, map_one, AdjoinRoot.mk_C] at hmap
    have hz : (AdjoinRoot.root (cyclotomic p ℤ) : CycRing p) = zeta p := rfl
    rw [hz] at hmap
    have hconst : (AdjoinRoot.of (cyclotomic p ℤ)) (F.eval 1) = (p : CycRing p) * (m : CycRing p) := by
      rw [hm]
      simp
    obtain ⟨c, hc⟩ := pi_dvd_natCast_p p
    refine ⟨AdjoinRoot.mk (cyclotomic p ℤ) q + c * (m : CycRing p), ?_⟩
    have : AdjoinRoot.mk (cyclotomic p ℤ) F
        = (zeta p - 1) * AdjoinRoot.mk (cyclotomic p ℤ) q
          + (p : CycRing p) * (m : CycRing p) := by
      rw [← hconst]
      linear_combination hmap
    rw [this, hc, pi]
    ring
