-- Prove2me | solution 1 for CyclicTypeChannel.typeEntropy_formula
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:32:49.32429+00:00
-- url     : https://prove2.me/submissions/41d3a385-3323-4b30-83ba-a86fe05fba64

-- Sol generated from Shared/CyclicTypeChannel.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_card_ordType_eq_totient
import Theorems.Thm_CyclicTypeChannel_ordType_dvd
import Theorems.Thm_CyclicTypeChannel_ordType_mod
import Theorems.Thm_CyclicTypeChannel_uEnt_eq_shannon
/-
# The cyclic splitting-type channel

A self-contained, formally verified account of the *splitting-type channel* of a
cyclic field extension.

For a prime `f` the Galois group of `ℚ(ζ_f)/ℚ` is `(ℤ/f)ˣ ≅ C n` with `n = f - 1`.
Writing an unramified prime `p` as `g ^ a` for a fixed generator `g`, the residue
degree (= the order of the Frobenius `p mod f`) is

  `T(p) = ord_f(p) = n / gcd(a, n)`.

This file develops:

* a general finite (counting) Shannon-entropy framework `uEnt`, its conditional
  version `condEnt` and the mutual information `mutInfo`;
* the general structural facts: the Shannon form of `uEnt`, non-negativity, the
  `log₂ |s|` cap, and the *data-processing* inequality for deterministic
  coarsenings;
* the group-theoretic grounding: `orderOf (g ^ a) = ordType n a` for a generator
  `g` of a cyclic group of order `n`, and the exact type-count law
  `#{a : ordType n a = d} = φ d`;
* exact closed-form evaluations of the type channel and of the *type-pair
  channel* of a semiprime for `n = 2, 4, 6, 10, 12, 16`, culminating in the
  headline fact that the pair channel of `C₄` and `C₆` carries strictly more
  than one bit.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. A counting Shannon-entropy framework -/

variable {α β γ : Type*}





variable [DecidableEq β] {s : Finset α} {g : α → β}












/-! ## 2. The splitting type of a cyclic Frobenius -/







/-! ## 3. The type channel and the semiprime type-pair channel -/




















/-! ## 4. Base-two logarithms of the numerals that occur -/




















/-! ## 5. Faithfulness of the exponent model, and the exact `φ`-law for `H(T)` -/

/-- The splitting types occurring in the `C n` channel are exactly the divisors of `n`. -/
theorem image_ordType (n : ℕ) (hn : 0 < n) : (range n).image (ordType n) = n.divisors := by
  ext d
  simp only [mem_image, mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨a, _, rfl⟩
    exact ⟨ordType_dvd a, hn.ne'⟩
  · rintro ⟨hd, -⟩
    refine ⟨(n / d) % n, Nat.mod_lt _ hn, ?_⟩
    rw [ordType_mod, ordType, Nat.gcd_eq_left (Nat.div_dvd_of_dvd hd),
      Nat.div_div_self hd hn.ne']








open CyclicTypeChannel in
theorem solution(n : ℕ) (hn : 0 < n) :
    typeEntropy n
      = ∑ d ∈ n.divisors, ((Nat.totient d : ℝ) / n) * Real.logb 2 ((n : ℝ) / Nat.totient d) := by
  have hne : (range n).Nonempty := by
    exact ⟨0, mem_range.2 hn⟩
  rw [typeEntropy, uEnt_eq_shannon hne, image_ordType n hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d ∣ n := (Nat.mem_divisors.1 hd).1
  have hcard : (#{x ∈ range n | ordType n x = d}) = Nat.totient d :=
    card_ordType_eq_totient hn hd'
  have hphi : (0 : ℝ) < (Nat.totient d : ℝ) := by
    have : 0 < Nat.totient d := Nat.totient_pos.2 (Nat.pos_of_dvd_of_pos hd' hn)
    exact_mod_cast this
  have hN : (0 : ℝ) < (#(range n) : ℝ) := by
    simpa using (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))
  rw [hcard, card_range, Real.logb_div (ne_of_gt hphi) (ne_of_gt (by exact_mod_cast hn)),
    Real.logb_div (by exact_mod_cast hn.ne') (ne_of_gt hphi)]
  ring
