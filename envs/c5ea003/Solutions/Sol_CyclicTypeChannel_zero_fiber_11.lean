-- Prove2me | solution 1 for CyclicTypeChannel.zero_fiber_11
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:03:43.027259+00:00
-- url     : https://prove2.me/submissions/9335af84-9ec9-417e-8a86-8c47020ea562

-- Sol generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
import Theorems.Thm_CyclicTypeChannel_box_fiber_11
import Theorems.Thm_CyclicTypeChannel_ordType_zero
/-
# The prime cyclic order: a closed form for the type-pair channel

The exact-value files compute the type-pair channel `Ipair n` for a finite list of
cyclic orders.  This file closes the *prime* case in complete generality: for
every prime `p` the channel of the cyclic order `C p` is

  `Ipair p = log₂ p - (p-1)(2p-1)/p² · log₂ (p-1) + (p-1)(p-2)/p² · log₂ (p-2)`.

(`Ipair_prime`; the two exact values `Ipair 3` and `Ipair 5` recorded in
`CyclicTypeChannelCRT.lean` are the instances `p = 3, 5`.)

Two consequences:

* `Ipair_prime_lt_one`: every **odd** prime order is *strictly below* the one-bit
  binary-fork cap, so among prime cyclic orders the cap is attained exactly at
  `p = 2` (`Ipair_prime_eq_one_iff`).  This upgrades the isolated computations
  `Ipair 3 < 1`, `Ipair 5 < 1` to an infinite statement and shows that the
  above-cap phenomenon of `C₄, C₆, C₁₀, C₁₂, C₁₆` is genuinely a *composite*
  phenomenon: a prime cyclic order has only two splitting types, and its fork is
  exactly the binary fork that papers 72–74 capped.
* `above_cap_imp_not_prime`: breaking the cap forces the cyclic order to be
  composite.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. The splitting type of a prime cyclic order -/

/-- For a prime order `p` the splitting type is binary: the exponent `0` gives the
split-completely type `1`, every other exponent gives the inert type `p`. -/
lemma ordType_prime {p a : ℕ} (hp : p.Prime) (ha : a < p) :
    ordType p a = if a = 0 then 1 else p := by
  rcases eq_or_ne a 0 with rfl | h
  · simp [ordType_zero hp.pos]
  · have hnd : ¬ p ∣ a := fun hdvd => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h) hdvd
      omega
    have hco : Nat.gcd a p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    simp [ordType, hco, h]

/-- The unordered type pair for a prime cyclic order. -/
lemma typePair_prime {p a b : ℕ} (hp : p.Prime) (ha : a < p) (hb : b < p) :
    typePair p (a, b) =
      if a = 0 ∧ b = 0 then (1, 1) else if a = 0 ∨ b = 0 then (1, p) else (p, p) := by
  have h1 : (1 : ℕ) ≤ p := hp.one_lt.le
  simp only [typePair, ordType_prime hp ha, ordType_prime hp hb]
  rcases eq_or_ne a 0 with rfl | ha0
  · rcases eq_or_ne b 0 with rfl | hb0
    · simp
    · simp [hb0, min_eq_left h1, max_eq_right h1]
  · rcases eq_or_ne b 0 with rfl | hb0
    · simp [ha0, min_eq_right h1, max_eq_left h1]
    · simp [ha0, hb0]

lemma mem_box_iff {n : ℕ} {x : ℕ × ℕ} : x ∈ CyclicTypeChannel.box n ↔ x.1 < n ∧ x.2 < n := by
  simp [CyclicTypeChannel.box, Finset.mem_product]


/-! ## 2. The three fibres in the CyclicTypeChannel.box -/











/-! ## 3. The pair entropy -/



/-! ## 4. The conditional entropy -/











/-! ### The nonzero fibres -/









/-! ## 5. Consequences: the cap among prime orders -/







/-! ## 6. Cross-checks against the enumerated values

`Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
prime formula is an independent check of the closed form. -/




open CyclicTypeChannel in
lemma solution{p : ℕ} (hp : p.Prime) :
    {x ∈ {y ∈ CyclicTypeChannel.box p | prodRes p y = 0} | typePair p x = (1, 1)} = {(0, 0)} := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_box_iff, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, _⟩, h⟩
    have hmem : (a, b) ∈ {x ∈ CyclicTypeChannel.box p | typePair p x = (1, 1)} := by
      rw [mem_filter, mem_box_iff]; exact ⟨⟨ha, hb⟩, h⟩
    rw [box_fiber_11 hp, Finset.mem_singleton] at hmem
    exact ⟨congrArg Prod.fst hmem, congrArg Prod.snd hmem⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨⟨hp.pos, hp.pos⟩, by simp [prodRes]⟩, ?_⟩
    rw [typePair_prime hp hp.pos hp.pos]; simp
