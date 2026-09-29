-- Prove2me | solution 1 for ParityGap.exists_primitive_scaling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:59:14.242907+00:00
-- url     : https://prove2.me/submissions/3a3d1af3-f945-42fa-8f4b-ac7fdbbabb19

-- Sol generated from Probability/CyclotomicRing.lean
import Mathlib
import Definitions.Def_Probability_CyclotomicRing
import Theorems.Thm_ParityGap_pi_dvd_of_red_eq_zero
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












@[simp] theorem red_zeta : red p (zeta p) = 1 := AdjoinRoot.lift_root _


theorem red_pi : red p (pi p) = 0 := by simp [pi]




theorem span_pi_ne_top : Ideal.span {pi p} ≠ ⊤ := by
  intro h
  have hunit : IsUnit (pi p) := by
    rwa [Ideal.span_singleton_eq_top] at h
  have h0 : IsUnit ((0 : ZMod p)) := by
    have := hunit.map (red p)
    rwa [red_pi] at this
  exact (not_isUnit_zero (M₀ := ZMod p)) h0

/-- Only `0` is divisible by every power of `π` (Krull intersection). -/
theorem eq_zero_of_forall_pi_pow_dvd {y : CycRing p} (h : ∀ m : ℕ, pi p ^ m ∣ y) : y = 0 := by
  have hbot : (⨅ i : ℕ, (Ideal.span {pi p}) ^ i) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isDomain _ (span_pi_ne_top p)
  have hmem : y ∈ ⨅ i : ℕ, (Ideal.span {pi p}) ^ i := by
    refine Ideal.mem_iInf.mpr fun i => ?_
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h i
  rw [hbot] at hmem
  simpa using hmem



open ParityGap in
theorem solution{ι : Type*} [Fintype ι] (v : ι → CycRing p)
    (hv : ∃ i, v i ≠ 0) :
    ∃ (m : ℕ) (w : ι → CycRing p), (∀ i, v i = pi p ^ m * w i) ∧ ∃ i, red p (w i) ≠ 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hv
  set P : ℕ → Prop := fun m => ∀ i, pi p ^ m ∣ v i with hP
  have hexists : ∃ m, ¬ P m := by
    by_contra hall
    push_neg at hall
    exact hi₀ (eq_zero_of_forall_pi_pow_dvd p (fun m => hall m i₀))
  set m₀ := Nat.find hexists with hm₀
  have hnot : ¬ P m₀ := Nat.find_spec hexists
  have hzero : P 0 := fun i => by simp
  have hm₀pos : 0 < m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h | h
    · exact absurd (h ▸ hzero) hnot
    · exact h
  have hprev : P (m₀ - 1) := by
    by_contra hc
    have hle : Nat.find hexists ≤ m₀ - 1 := Nat.find_le hc
    omega
  choose w hw using hprev
  refine ⟨m₀ - 1, w, hw, ?_⟩
  by_contra hall
  push_neg at hall
  apply hnot
  intro i
  obtain ⟨c, hc⟩ := pi_dvd_of_red_eq_zero p (hall i)
  have hm : m₀ = (m₀ - 1) + 1 := by omega
  refine ⟨c, ?_⟩
  calc v i = pi p ^ (m₀ - 1) * (pi p * c) := by rw [hw i, hc]
    _ = pi p ^ ((m₀ - 1) + 1) * c := by rw [pow_succ]; ring
    _ = pi p ^ m₀ * c := by rw [← hm]
