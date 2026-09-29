-- Prove2me | solution 1 for SmoothSparsity.smoothPool_card_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:54:05.579976+00:00
-- url     : https://prove2.me/submissions/906c7853-d14d-472f-8df0-3585bce4737d

-- Sol generated from Shared/SmoothCountSparsity.lean
import Mathlib
import Definitions.Def_Shared_NumberTheory_IsSmooth
import Definitions.Def_Shared_SmoothCountSparsity
import Theorems.Thm_SmoothSparsity_factorization_le_log_two
import Theorems.Thm_SmoothSparsity_mem_factorBase

/-!
# Rigorous sparsity of the smooth pool, from the exponent-vector injection

Context (experiment 465, paper 130).  The quadratic sieve needs `B`-smooth values
`x^2 - N`; the whole subexponential run time is a trade-off between the *size* of
the factor base (`π(B)` relations must be collected) and the *rarity* of smooth
values.  Everything asymptotic about that trade-off is Dickman heuristics; this
file records the part that is an unconditional theorem, and which is the true
reason the smooth pool is thin at fixed `B`:

> a `B`-smooth number `n ≤ x` is *determined* by its exponent vector, whose
> entries are at most `log₂ x`, so there are at most `(log₂ x + 1) ^ π(B)` of
> them — polylogarithmic in `x` for fixed `B`.

This is the finite, unconditional skeleton underneath the `ρ(u)` model: it forces
`B → ∞` with `x`, which is what makes the sieve subexponential rather than
polynomial.  It is proved here by an explicit injection of the smooth pool into
the space of exponent vectors, using the catalog predicate `isSmooth` of
`Catalog.Shared.NumberTheory.IsSmooth`.

Main results:

* `mem_smoothPool_iff` — the decidable pool predicate agrees with the catalog
  predicate `isSmooth`.
* `factorization_le_log_two` — every exponent of a number `≤ x` is `≤ log₂ x`.
* `smoothPool_card_le` — `Ψ(x,B) ≤ (log₂ x + 1) ^ π(B)`.
* `smoothPool_card_le_pow_pi` — the same bound with the factor base written as
  the prime-counting function.
* `smoothPool_one` — the extreme case `B = 1`: only `n = 1` is `1`-smooth.
-/

open SmoothSparsity

open Finset










open SmoothSparsity in
theorem solution(B x : ℕ) :
    (smoothPool B x).card ≤ (Nat.log 2 x + 1) ^ (factorBase B).card := by
  classical
  set k := Nat.log 2 x with hk
  -- the exponent-vector map
  set f : ℕ → (factorBase B → Fin (k + 1)) :=
    fun n p => ⟨min (n.factorization p) k, by omega⟩ with hf
  have hcard : Fintype.card (factorBase B → Fin (k + 1)) = (k + 1) ^ (factorBase B).card := by
    simp
  have hinj : Set.InjOn f (smoothPool B x) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, smoothPool, Finset.mem_filter, Finset.mem_Icc] at ha hb
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hfa : ∀ p, a.factorization p = b.factorization p := by
      intro p
      by_cases hp : p ∈ factorBase B
      · have := congrFun hab ⟨p, hp⟩
        simp only [hf, Fin.mk.injEq] at this
        have h1 : a.factorization p ≤ k :=
          factorization_le_log_two ha0 ha.1.2
        have h2 : b.factorization p ≤ k :=
          factorization_le_log_two hb0 hb.1.2
        omega
      · have hA : a.factorization p = 0 := by
          by_contra hcon
          have hmem : p ∈ a.primeFactors := by
            rw [← Nat.support_factorization]
            exact Finsupp.mem_support_iff.2 hcon
          exact hp (mem_factorBase.2
            ⟨Nat.prime_of_mem_primeFactors hmem, ha.2 p hmem⟩)
        have hB : b.factorization p = 0 := by
          by_contra hcon
          have hmem : p ∈ b.primeFactors := by
            rw [← Nat.support_factorization]
            exact Finsupp.mem_support_iff.2 hcon
          exact hp (mem_factorBase.2
            ⟨Nat.prime_of_mem_primeFactors hmem, hb.2 p hmem⟩)
        rw [hA, hB]
    have : a.factorization = b.factorization := Finsupp.ext hfa
    exact Nat.factorization_inj (Set.mem_setOf_eq ▸ ha0) (Set.mem_setOf_eq ▸ hb0) this
  calc (smoothPool B x).card
      ≤ (Finset.univ : Finset (factorBase B → Fin (k + 1))).card :=
        Finset.card_le_card_of_injOn f (fun n _ => Finset.mem_univ _) hinj
    _ = (k + 1) ^ (factorBase B).card := by rw [← hcard]; rfl
