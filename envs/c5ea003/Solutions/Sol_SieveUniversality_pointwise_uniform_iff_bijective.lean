-- Prove2me | solution 1 for SieveUniversality.pointwise_uniform_iff_bijective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:24:03.083984+00:00
-- url     : https://prove2.me/submissions/bbc2cc29-14ae-4565-a74e-31e6f76a7887

-- Sol generated from Shared/SievePolynomialUniversality.lean
import Mathlib
import Definitions.Def_Shared_QSRelationPoolRandom
import Definitions.Def_Shared_SievePolynomialUniversality

/-!
# Universality of on-average random-equivalence for sieve polynomials

The exact cancellation of `Catalog.Shared.QSRelationPoolRandom` invites the
question: is the quadratic sieve special?  It is not.  This file isolates the
combinatorial skeleton of the phenomenon and shows it is *universal*: for **any**
sieve map `f` on residues (any polynomial, any degree, any modulus), the number
of `x` per period hitting a given target residue averages to exactly
`|domain| / |targets|`, the random-model value.  Averaged over the target, no
sieve polynomial can be better or worse than random.

What the individual polynomial controls is only the *distribution* of that hit
count across targets, and the file characterises exactly when the pool is
random-equivalent target-by-target rather than merely on average:

* `sum_fiber_card` — the averaging identity (universality).
* `pointwise_uniform_iff_bijective` — pointwise random-equivalence holds iff the
  sieve map is a bijection of residues.
* `sq_not_pointwise_uniform` — for `x ↦ x^2` mod an odd prime it fails: the
  hit count is the `2`/`0` dichotomy, never the constant `1`.
* `qs_average_hits_eq_random` — but on average over the modulus residue the
  quadratic sieve hits exactly once per period, like a random sequence.

The moral for the experiment: any measured deviation of the `x^2 - N` pool from
the random control must come from the *interaction across primes* for one fixed
`N`, never from the one-prime statistics, which are pinned by these identities.
-/

open SieveUniversality

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]




/-! ## The quadratic sieve instance -/

variable {p : ℕ} [Fact p.Prime]





open SieveUniversality in
omit [Fintype β] in
theorem solution(f : α → β) :
    (∀ b, hitCount f b = 1) ↔ Function.Bijective f := by
  classical
  constructor
  · intro h
    constructor
    · intro x y hxy
      have hcard : (Finset.univ.filter (fun z => f z = f x)).card = 1 := h (f x)
      obtain ⟨z, hz⟩ := Finset.card_eq_one.1 hcard
      have hx : x ∈ Finset.univ.filter (fun z => f z = f x) := by simp
      have hy : y ∈ Finset.univ.filter (fun z => f z = f x) := by simp [hxy]
      rw [hz] at hx hy
      simp only [Finset.mem_singleton] at hx hy
      rw [hx, hy]
    · intro b
      have hcard : (Finset.univ.filter (fun z => f z = b)).card = 1 := h b
      obtain ⟨z, hz⟩ := Finset.card_eq_one.1 hcard
      have : z ∈ Finset.univ.filter (fun w => f w = b) := by rw [hz]; simp
      exact ⟨z, (Finset.mem_filter.1 this).2⟩
  · rintro ⟨hinj, hsurj⟩ b
    obtain ⟨a, rfl⟩ := hsurj b
    have : Finset.univ.filter (fun z => f z = f a) = {a} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hinj h, fun h => by rw [h]⟩
    rw [hitCount, this, Finset.card_singleton]
