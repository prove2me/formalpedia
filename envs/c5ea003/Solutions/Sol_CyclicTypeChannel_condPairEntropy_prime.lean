-- Prove2me | solution 1 for CyclicTypeChannel.condPairEntropy_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:42:39.690373+00:00
-- url     : https://prove2.me/submissions/40cbdb2d-356e-49bc-9682-6137283db6e2

-- Sol generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
import Theorems.Thm_CyclicTypeChannel_condPairEntropy_val_2
import Theorems.Thm_CyclicTypeChannel_prodRes_fiber
import Theorems.Thm_CyclicTypeChannel_uEnt_nonzero_fiber
import Theorems.Thm_CyclicTypeChannel_uEnt_zero_fiber
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

lemma card_box (n : ℕ) : (CyclicTypeChannel.box n).card = n * n := by
  simp [CyclicTypeChannel.box]

/-! ## 2. The three fibres in the CyclicTypeChannel.box -/











/-! ## 3. The pair entropy -/



/-! ## 4. The conditional entropy -/


lemma card_prodRes_fiber {p c : ℕ} (hp : 0 < p) (hc : c < p) :
    #{x ∈ CyclicTypeChannel.box p | prodRes p x = c} = p := by
  rw [prodRes_fiber hp hc, Finset.card_image_of_injective _ (fun x y h => by
    simpa using congrArg Prod.fst h), Finset.card_range]

lemma image_prodRes {p : ℕ} (hp : 0 < p) : (CyclicTypeChannel.box p).image (prodRes p) = range p := by
  ext c
  simp only [Finset.mem_image, mem_range]
  constructor
  · rintro ⟨x, _, rfl⟩
    exact Nat.mod_lt _ hp
  · intro hc
    exact ⟨(c, 0), by rw [mem_box_iff]; exact ⟨hc, hp⟩, by simp [prodRes, Nat.mod_eq_of_lt hc]⟩








/-! ### The nonzero fibres -/









/-! ## 5. Consequences: the cap among prime orders -/







/-! ## 6. Cross-checks against the enumerated values

`Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
prime formula is an independent check of the closed form. -/




open CyclicTypeChannel in
theorem solution{p : ℕ} (hp : p.Prime) :
    condPairEntropy p = Real.logb 2 p
      - ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) ^ 2
      - 2 * ((p : ℝ) - 1) / (p : ℝ) ^ 2
      - ((p : ℝ) - 1) * ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) / (p : ℝ) ^ 2 := by
  rcases eq_or_lt_of_le hp.two_le with h2 | h2
  · -- `p = 2`
    have hp2 : p = 2 := h2.symm
    subst hp2
    rw [condPairEntropy_val_2]
    norm_num
  · have hp3 : 3 ≤ p := by omega
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hcard : ((CyclicTypeChannel.box p).card : ℝ) = (p : ℝ) * p := by rw [card_box]; push_cast; ring
    rw [condPairEntropy, condEnt, image_prodRes hp.pos]
    have hterm : ∀ c ∈ range p,
        ((#{x ∈ CyclicTypeChannel.box p | prodRes p x = c} : ℝ) / (CyclicTypeChannel.box p).card) *
            uEnt {x ∈ CyclicTypeChannel.box p | prodRes p x = c} (typePair p)
          = (1 / (p : ℝ)) * uEnt {x ∈ CyclicTypeChannel.box p | prodRes p x = c} (typePair p) := by
      intro c hc
      rw [mem_range] at hc
      rw [card_prodRes_fiber hp.pos hc, hcard]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsplit : ∑ c ∈ range p, uEnt {x ∈ CyclicTypeChannel.box p | prodRes p x = c} (typePair p)
        = uEnt {x ∈ CyclicTypeChannel.box p | prodRes p x = 0} (typePair p)
          + ∑ c ∈ (range p).erase 0, uEnt {x ∈ CyclicTypeChannel.box p | prodRes p x = c} (typePair p) := by
      rw [← Finset.add_sum_erase _ _ (mem_range.2 hp.pos)]
    have hconst : ∀ c ∈ (range p).erase 0,
        uEnt {x ∈ CyclicTypeChannel.box p | prodRes p x = c} (typePair p)
          = Real.logb 2 p - (2 + ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2)) / (p : ℝ) := by
      intro c hc
      rw [Finset.mem_erase, mem_range] at hc
      exact uEnt_nonzero_fiber hp hp3 hc.2 hc.1
    rw [hsplit, Finset.sum_congr rfl hconst, Finset.sum_const,
      Finset.card_erase_of_mem (mem_range.2 hp.pos), Finset.card_range, uEnt_zero_fiber hp]
    have hcast1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le]; norm_num
    rw [nsmul_eq_mul, hcast1]
    field_simp
    ring
