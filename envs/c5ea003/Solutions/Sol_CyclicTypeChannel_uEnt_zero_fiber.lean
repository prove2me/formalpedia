-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_zero_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:41:13.380819+00:00
-- url     : https://prove2.me/submissions/5b7e4c41-d8c5-4bfe-9d59-1e66037afeef

-- Sol generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
import Theorems.Thm_CyclicTypeChannel_image_zero_fiber
import Theorems.Thm_CyclicTypeChannel_prodRes_fiber
import Theorems.Thm_CyclicTypeChannel_sum_logb_fiber
import Theorems.Thm_CyclicTypeChannel_zero_fiber_11
import Theorems.Thm_CyclicTypeChannel_zero_fiber_pp
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





/-! ## 2. The three fibres in the box -/











/-! ## 3. The pair entropy -/

lemma uEnt_eq_image_sum {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) :
    uEnt s g = Real.logb 2 s.card
      - (∑ v ∈ s.image g, (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ))
        / s.card := by
  rw [uEnt, sum_logb_fiber]


/-! ## 4. The conditional entropy -/


lemma card_prodRes_fiber {p c : ℕ} (hp : 0 < p) (hc : c < p) :
    #{x ∈ box p | prodRes p x = c} = p := by
  rw [prodRes_fiber hp hc, Finset.card_image_of_injective _ (fun x y h => by
    simpa using congrArg Prod.fst h), Finset.card_range]









/-! ### The nonzero fibres -/









/-! ## 5. Consequences: the cap among prime orders -/







/-! ## 6. Cross-checks against the enumerated values

`Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
prime formula is an independent check of the closed form. -/




open CyclicTypeChannel in
theorem solution{p : ℕ} (hp : p.Prime) :
    uEnt {y ∈ box p | prodRes p y = 0} (typePair p)
      = Real.logb 2 p - ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) := by
  have hpne : p ≠ 1 := hp.ne_one
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; norm_num
  have hne : ((1 : ℕ), (1 : ℕ)) ≠ (p, p) := by
    intro h; rw [Prod.mk.injEq] at h; exact hpne h.1.symm
  have hmem : ((1 : ℕ), (1 : ℕ)) ∉ ({(p, p)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]; exact hne
  have h11 : #{x ∈ {y ∈ box p | prodRes p y = 0} | typePair p x = (1, 1)} = 1 := by
    rw [zero_fiber_11 hp, Finset.card_singleton]
  rw [uEnt_eq_image_sum, image_zero_fiber hp, card_prodRes_fiber hp.pos hp.pos,
    Finset.sum_insert hmem, Finset.sum_singleton, h11, zero_fiber_pp hp]
  push_cast [hcast]
  simp
