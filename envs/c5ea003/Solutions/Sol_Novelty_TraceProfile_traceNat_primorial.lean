-- Prove2me | solution 1 for Novelty.TraceProfile.traceNat_primorial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:42:32.515765+00:00
-- url     : https://prove2.me/submissions/a8db0b2f-936a-4009-a4a3-2c671ce69557

-- Sol generated from Novelty/TraceProfileTraceSet.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
import Theorems.Thm_Novelty_TraceProfile_mem_traceSet
import Theorems.Thm_Novelty_TraceProfile_traceNat_eq_card
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




/-- The trace set is transported by any ring isomorphism. -/
theorem traceSet_ringEquiv (e : R ≃+* S) (N : R) :
    traceSet (e N) = (traceSet N).image e := by
  ext s
  simp only [mem_traceSet, mem_image]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨e.symm x + e.symm y, ⟨e.symm x, e.symm y, ?_, rfl⟩, by simp⟩
    apply e.injective
    simpa using hxy
  · rintro ⟨t, ⟨x, y, hxy, rfl⟩, rfl⟩
    exact ⟨e x, e y, by rw [← map_mul, hxy], by rw [map_add]⟩

theorem card_traceSet_ringEquiv (e : R ≃+* S) (N : R) :
    (traceSet (e N)).card = (traceSet N).card := by
  rw [traceSet_ringEquiv e N, Finset.card_image_of_injective _ e.injective]

/-! ## CRT multiplicativity -/

/-- **The trace set of a product ring is the product of the trace sets.** -/
theorem traceSet_prod (N : R) (M : S) :
    traceSet ((N, M) : R × S) = (traceSet N) ×ˢ (traceSet M) := by
  ext s
  simp only [mem_traceSet, mem_product, Prod.exists, Prod.ext_iff, Prod.mk_mul_mk,
    Prod.mk_add_mk]
  constructor
  · rintro ⟨x1, x2, y1, y2, ⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨x1, y1, h1, h3⟩, ⟨x2, y2, h2, h4⟩⟩
  · rintro ⟨⟨x1, y1, h1, h3⟩, ⟨x2, y2, h2, h4⟩⟩
    exact ⟨x1, x2, y1, y2, ⟨h1, h2⟩, h3, h4⟩

theorem card_traceSet_prod (N : R) (M : S) :
    (traceSet ((N, M) : R × S)).card = (traceSet N).card * (traceSet M).card := by
  rw [traceSet_prod, Finset.card_product]

/-- **CRT form.**  For coprime moduli the trace-set size is multiplicative. -/
theorem card_traceSet_zmod_mul {m n : ℕ} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (N : ℕ) :
    (traceSet ((N : ZMod (m * n)))).card
      = (traceSet ((N : ZMod m))).card * (traceSet ((N : ZMod n))).card := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  have he := card_traceSet_ringEquiv (ZMod.chineseRemainder h) ((N : ZMod (m * n)))
  rw [← he, map_natCast]
  have hpr : ((N : ZMod m × ZMod n)) = ((N : ZMod m), (N : ZMod n)) := by
    ext <;> simp
  rw [hpr, card_traceSet_prod]

/-! ## The exact size over a prime field -/


variable {q : ℕ} [hq : Fact (Nat.Prime q)]








/-! ## The joint law: one bit per prime

To speak about a varying modulus we use the `Set.ncard` version of the trace-set
size, a *total* function of the modulus (no finiteness instance required). -/



@[simp] theorem traceNat_one (N : ℕ) : traceNat 1 N = 1 := by
  rw [traceNat_eq_card, Finset.card_eq_one]
  refine ⟨0, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun x _ => Subsingleton.elim _ _⟩⟩
  rw [mem_traceSet]
  exact ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- **CRT multiplicativity, modulus form.** -/
theorem traceNat_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) (N : ℕ) :
    traceNat (m * n) N = traceNat m N * traceNat n N := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero hm hn⟩
  rw [traceNat_eq_card, traceNat_eq_card, traceNat_eq_card, card_traceSet_zmod_mul h]






open Novelty.TraceProfile in
theorem solution(N : ℕ) :
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      traceNat (∏ p ∈ P, p) N = ∏ p ∈ P, traceNat p N := by
  classical
  intro P
  induction P using Finset.induction with
  | empty => intro _; simp
  | @insert a P ha ih =>
      intro hP
      have hap : a.Prime := hP a (Finset.mem_insert_self a P)
      have hPp : ∀ p ∈ P, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ P, p) :=
        Nat.Coprime.prod_right fun p hp =>
          (Nat.coprime_primes hap (hPp p hp)).2 (by rintro rfl; exact ha hp)
      have hProd : (∏ p ∈ P, p) ≠ 0 :=
        Nat.ne_of_gt (Finset.prod_pos (fun p hp => (hPp p hp).pos))
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        traceNat_mul hap.ne_zero hProd hcop N, ih hPp]
