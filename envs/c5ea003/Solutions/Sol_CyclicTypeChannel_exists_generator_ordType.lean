-- Prove2me | solution 1 for CyclicTypeChannel.exists_generator_ordType
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:22:59.774321+00:00
-- url     : https://prove2.me/submissions/2213311d-f164-405f-b228-9270ba6e6721

-- Sol generated from Shared/CyclicTypeChannel.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_ordType_mod
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





/-- **Group-theoretic grounding.** In any finite group, the order of `g ^ a` is
given by the arithmetic function `ordType (orderOf g) a`; for a generator of a
cyclic group of order `n` this is exactly the Frobenius order used above. -/
theorem orderOf_pow_eq_ordType {G : Type*} [Group G] [Finite G] (g : G) (a : ℕ) :
    orderOf (g ^ a) = ordType (orderOf g) a := by
  rw [orderOf_pow, ordType, Nat.gcd_comm]


/-! ## 3. The type channel and the semiprime type-pair channel -/




















/-! ## 4. Base-two logarithms of the numerals that occur -/




















/-! ## 5. Faithfulness of the exponent model, and the exact `φ`-law for `H(T)` -/









open CyclicTypeChannel in
theorem solution(f : ℕ) [hf : Fact f.Prime] :
    ∃ g : (ZMod f)ˣ, orderOf g = f - 1 ∧
      ∀ u : (ZMod f)ˣ, ∃ a < f - 1, u = g ^ a ∧ orderOf u = ordType (f - 1) a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod f)ˣ)
  have hcard : Nat.card ((ZMod f)ˣ) = f - 1 := by
    have : Fintype.card ((ZMod f)ˣ) = f - 1 := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime hf.out]
    simpa [Nat.card_eq_fintype_card] using this
  have hord : orderOf g = f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hpos : 0 < f - 1 := by
    have := hf.out.two_le
    omega
  refine ⟨g, hord, fun u => ?_⟩
  have hk' : ∃ k : ℕ, g ^ k = u := by
    have := (mem_powers_iff_mem_zpowers (x := g) (y := u)).2 (hg u)
    exact this
  obtain ⟨k, rfl⟩ := hk'
  refine ⟨k % (f - 1), Nat.mod_lt _ hpos, ?_, ?_⟩
  · rw [← hord, pow_mod_orderOf]
  · rw [orderOf_pow_eq_ordType, hord, ← hord, ordType_mod]
