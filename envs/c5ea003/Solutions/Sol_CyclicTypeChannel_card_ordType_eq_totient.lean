-- Prove2me | solution 1 for CyclicTypeChannel.card_ordType_eq_totient
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:20:22.088156+00:00
-- url     : https://prove2.me/submissions/0f2bd6c8-d687-4a5b-83d0-de9287ee80c6

-- Sol generated from Shared/CyclicTypeChannel.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
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









open CyclicTypeChannel in
theorem solution{n d : ℕ} (hn : 0 < n) (hd : d ∣ n) :
    #{a ∈ range n | ordType n a = d} = Nat.totient d := by
  obtain ⟨k, hk⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp [hk] at hn)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp [hk] at hn)
  have key : ∀ a, a < n → ordType n a = d → Nat.gcd a n = k := by
    intro a _ hgd
    have h1 : Nat.gcd a n ∣ n := Nat.gcd_dvd_right _ _
    have h2 : Nat.gcd a n * d = n := by rw [← hgd, ordType]; exact Nat.mul_div_cancel' h1
    have : d * Nat.gcd a n = d * k := by rw [Nat.mul_comm] at h2; omega
    exact Nat.eq_of_mul_eq_mul_left hd0 this
  rw [Nat.totient]
  refine (Finset.card_bij' (fun m _ => m * k) (fun a _ => a / k) ?_ ?_ ?_ ?_).symm
  · intro m hm
    simp only [mem_filter, mem_range] at hm ⊢
    have hco : Nat.gcd m d = 1 := Nat.Coprime.symm hm.2
    refine ⟨by calc m * k < d * k := (Nat.mul_lt_mul_right hk0).2 hm.1
              _ = n := hk.symm, ?_⟩
    have hg : Nat.gcd (m * k) n = k := by
      rw [hk, Nat.mul_comm m k, Nat.mul_comm d k, Nat.gcd_mul_left, hco, Nat.mul_one]
    rw [ordType, hg, hk, Nat.mul_div_cancel _ hk0]
  · intro a ha
    simp only [mem_filter, mem_range] at ha ⊢
    have hg : Nat.gcd a n = k := key a ha.1 ha.2
    have hka : k ∣ a := hg ▸ Nat.gcd_dvd_left a n
    obtain ⟨m, rfl⟩ := hka
    rw [Nat.mul_div_cancel_left _ hk0]
    have hco : Nat.gcd m d = 1 := by
      rw [hk, Nat.mul_comm d k, Nat.gcd_mul_left] at hg
      exact Nat.eq_of_mul_eq_mul_left hk0 (by rw [Nat.mul_one]; exact hg)
    refine ⟨?_, Nat.Coprime.symm hco⟩
    have hlt : k * m < d * k := hk ▸ ha.1
    nlinarith [hlt]
  · intro m _
    exact Nat.mul_div_cancel _ hk0
  · intro a ha
    simp only [mem_filter, mem_range] at ha
    have hg : Nat.gcd a n = k := key a ha.1 ha.2
    exact Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_left a n)
