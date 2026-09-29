-- Prove2me | solution 1 for CyclicTypeChannel.zero_fiber_pp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:03:44.352005+00:00
-- url     : https://prove2.me/submissions/25f0f07d-1fd0-4830-93e0-bc67bc056a61

-- Sol generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
import Theorems.Thm_CyclicTypeChannel_ordType_zero
import Theorems.Thm_CyclicTypeChannel_prodRes_fiber
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


lemma card_prodRes_fiber {p c : ℕ} (hp : 0 < p) (hc : c < p) :
    #{x ∈ CyclicTypeChannel.box p | prodRes p x = c} = p := by
  rw [prodRes_fiber hp hc, Finset.card_image_of_injective _ (fun x y h => by
    simpa using congrArg Prod.fst h), Finset.card_range]


/-- On the `N ≡ 0` fibre either both exponents vanish or neither does. -/
lemma prodRes_zero_dichotomy {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : prodRes p (a, b) = 0) : (a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ b ≠ 0) := by
  rcases eq_or_ne a 0 with rfl | h1
  · refine Or.inl ⟨rfl, ?_⟩
    simpa [prodRes, Nat.mod_eq_of_lt hb] using h
  · rcases eq_or_ne b 0 with rfl | h2
    · exact absurd (by simpa [prodRes, Nat.mod_eq_of_lt ha] using h) h1
    · exact Or.inr ⟨h1, h2⟩



lemma origin_mem_zero_fiber {p : ℕ} (hp : p.Prime) :
    ({((0 : ℕ), (0 : ℕ))} : Finset (ℕ × ℕ)) ⊆ {y ∈ CyclicTypeChannel.box p | prodRes p y = 0} := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  rw [mem_filter, mem_box_iff]
  exact ⟨⟨hp.pos, hp.pos⟩, by simp [prodRes]⟩




/-! ### The nonzero fibres -/









/-! ## 5. Consequences: the cap among prime orders -/







/-! ## 6. Cross-checks against the enumerated values

`Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
prime formula is an independent check of the closed form. -/




open CyclicTypeChannel in
lemma solution{p : ℕ} (hp : p.Prime) :
    #{x ∈ {y ∈ CyclicTypeChannel.box p | prodRes p y = 0} | typePair p x = (p, p)} = p - 1 := by
  have hpne : p ≠ 1 := hp.ne_one
  have hsub : {x ∈ {y ∈ CyclicTypeChannel.box p | prodRes p y = 0} | typePair p x = (p, p)}
      = {y ∈ CyclicTypeChannel.box p | prodRes p y = 0} \ {(0, 0)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_box_iff, Finset.mem_sdiff, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro ⟨rfl, rfl⟩
      rw [typePair_prime hp hp.pos hp.pos] at h2
      simp only [and_self, if_true, Prod.mk.injEq] at h2
      exact hpne h2.symm
    · rintro ⟨⟨⟨ha, hb⟩, hres⟩, hne⟩
      refine ⟨⟨⟨ha, hb⟩, hres⟩, ?_⟩
      rw [typePair_prime hp ha hb]
      rcases prodRes_zero_dichotomy ha hb hres with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
      · exact absurd ⟨rfl, rfl⟩ hne
      · rw [if_neg (by tauto), if_neg (by tauto)]
  rw [hsub, Finset.card_sdiff_of_subset (origin_mem_zero_fiber hp), Finset.card_singleton,
    card_prodRes_fiber hp.pos hp.pos]
