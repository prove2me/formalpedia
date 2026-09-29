-- Prove2me | solution 1 for Novelty.TraceProfile.fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:29:41.293878+00:00
-- url     : https://prove2.me/submissions/76e87ddf-eb56-4775-99a5-ae3e509adab2

-- Sol generated from Novelty/TraceProfileTraceSet.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
import Theorems.Thm_Novelty_TraceProfile_traceSet_eq_image_nonzero
/-
# TRACEPROFILE II — the trace set: exact size and one bit per prime

Phase A research file (Novelty domain), Paper 50 / Experiment 385.

For a finite commutative ring `R` and `N : R` the **trace set** is

`S_R(N) = {x + y : x * y = N}`,

the set of all residues that the trace `s = p + q` of a factorisation of `N` can
possibly take.  The experiment measured `|S_{ZMod m}(N)| = (m+1)/2` for odd primes
`m`, and the *joint law* `|S_{ZMod M#}(N)| / M# = 2^{-ω(M#)}` ("exactly one bit per
prime, additively independent").

This file proves the exact statements.

## Main results

* `mem_traceSet` — the defining membership criterion.
* `card_traceSet_ringEquiv` — the trace set is a ring-isomorphism invariant.
* `traceSet_prod` / `card_traceSet_prod` — the trace set of a product ring is the
  product of the trace sets: **CRT multiplicativity**.
* `card_traceSet_zmod_mul` — the arithmetic CRT form for coprime moduli.
* `card_traceSet_prime` — **the exact size over a prime field**:
  `2 * |S_p(N)| = p + 1` if `N` is a nonzero square mod `p`, and `p - 1` otherwise.
  (This *refines* the experimental reading `(m+1)/2`: the true value is
  `(m + χ(N))/2` with `χ` the quadratic character — a `±1` correction invisible at
  the measured precision, but it is the exact law.)
* `traceNat_primorial` — multiplicativity along a squarefree modulus.
* `traceNat_one_bit_per_prime` — **the joint law**:
  `∏ (p-1) ≤ 2^{ω} * |S_{M}(N)| ≤ ∏ (p+1)` for `M = ∏ p` squarefree odd,
  i.e. the trace set has density `2^{-ω(M)}` up to the `(1 ± 1/p)` corrections.
* `card_traceSet_lt_prime` — the trace really is constrained: over a prime field the
  trace set is a proper subset (about half the residues).
-/


open Novelty.TraceProfile

open Finset

/-! ## The trace set of a finite commutative ring -/

variable {R S : Type*} [CommRing R] [Fintype R] [DecidableEq R]
  [CommRing S] [Fintype S] [DecidableEq S]






/-! ## CRT multiplicativity -/




/-! ## The exact size over a prime field -/


variable {q : ℕ} [hq : Fact (Nat.Prime q)]








/-! ## The joint law: one bit per prime

To speak about a varying modulus we use the `Set.ncard` version of the trace-set
size, a *total* function of the modulus (no finiteness instance required). -/










open Novelty.TraceProfile in
theorem solution(N s : ZMod q) (hN : N ≠ 0) (hs : s ∈ traceSet N) :
    ((univ.filter (fun x : ZMod q => x ≠ 0)).filter
      (fun x => x + N * x⁻¹ = s)).card = if s ^ 2 = 4 * N then 1 else 2 := by
  rw [traceSet_eq_image_nonzero N hN] at hs
  simp only [mem_image, mem_filter, mem_univ, true_and] at hs
  obtain ⟨x₀, hx₀, hs₀⟩ := hs
  set y₀ : ZMod q := N * x₀⁻¹ with hy₀def
  have hy₀ : y₀ ≠ 0 := mul_ne_zero hN (inv_ne_zero hx₀)
  have hprod : x₀ * y₀ = N := by rw [hy₀def]; field_simp
  have hsum : x₀ + y₀ = s := hs₀
  have hset : ((univ.filter (fun x : ZMod q => x ≠ 0)).filter
      (fun x => x + N * x⁻¹ = s)) = {x₀, y₀} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, hxs⟩
      have hquad : x * x - s * x + N = 0 := by
        have h' : (x + N * x⁻¹) * x = s * x := by rw [hxs]
        field_simp at h'
        linear_combination h'
      have hfac : (x - x₀) * (x - y₀) = 0 := by
        rw [← hsum, ← hprod] at hquad
        linear_combination hquad
      rcases mul_eq_zero.1 hfac with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (sub_eq_zero.1 h)
    · rintro (rfl | rfl)
      · exact ⟨hx₀, hs₀⟩
      · refine ⟨hy₀, ?_⟩
        have hxy : N * y₀⁻¹ = x₀ := by
          rw [hy₀def]
          field_simp
        rw [hxy, ← hsum]
        ring
  rw [hset]
  by_cases h : s ^ 2 = 4 * N
  · rw [if_pos h]
    have hxy : x₀ = y₀ := by
      have hdiff : (x₀ - y₀) ^ 2 = 0 := by
        have hd : (x₀ - y₀) ^ 2 = s ^ 2 - 4 * N := by
          rw [← hsum, ← hprod]; ring
        rw [hd, h]; ring
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hdiff
      exact sub_eq_zero.1 this
    simp [hxy]
  · rw [if_neg h]
    have hne : x₀ ≠ y₀ := by
      intro he
      apply h
      rw [← hsum, ← hprod, he]
      ring
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
