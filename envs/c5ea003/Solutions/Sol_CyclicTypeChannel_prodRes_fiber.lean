-- Prove2me | solution 1 for CyclicTypeChannel.prodRes_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:59:04.772679+00:00
-- url     : https://prove2.me/submissions/bc780ef1-7515-413e-b2b1-9e7101b02401

-- Sol generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
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
lemma solution{p c : ℕ} (hp : 0 < p) (hc : c < p) :
    {x ∈ CyclicTypeChannel.box p | prodRes p x = c} = (range p).image (fun a => (a, (c + p - a) % p)) := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_box_iff, Finset.mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    refine ⟨a, ha, rfl, ?_⟩
    rw [prodRes] at h
    rcases lt_or_ge (a + b) p with hab | hab
    · have hc' : c = a + b := by rw [← h, Nat.mod_eq_of_lt hab]
      have e : c + p - a = b + p := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
    · have hlt : a + b - p < p := by omega
      have hc' : c = a + b - p := by
        rw [← h, Nat.mod_eq_sub_mod hab, Nat.mod_eq_of_lt hlt]
      have e : c + p - a = b := by omega
      rw [e, Nat.mod_eq_of_lt hb]
  · rintro ⟨a', ha', rfl, rfl⟩
    refine ⟨⟨ha', Nat.mod_lt _ hp⟩, ?_⟩
    rw [prodRes]
    rcases Nat.lt_or_ge c a' with h | h
    · have e : c + p - a' < p := by omega
      rw [Nat.mod_eq_of_lt e]
      have e2 : a' + (c + p - a') = c + p := by omega
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt hc]
    · have e : c + p - a' = (c - a') + p := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : c - a' < p)]
      have e2 : a' + (c - a') = c := by omega
      rw [e2, Nat.mod_eq_of_lt hc]
