-- Prove2me | solution 1 for divisibility_pigeonhole
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:26:20.537052+00:00
-- url     : https://prove2.me/submissions/f7d3c2a8-6e6c-4538-8a45-65a3100a90e0

-- Sol generated from Speculative/NumberTheory/FibonacciDivisibilityPigeonhole.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_FibonacciDivisibilityPigeonhole
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci-Divisibility Pigeonhole Bridge

This file contains three theorems:

* `fib_dvd_of_dvd`: divisibility of indices implies divisibility of Fibonacci numbers.
* `fib_dvd_iff`: for `3 ≤ m`, `Nat.fib m ∣ Nat.fib n ↔ m ∣ n`.
* `divisibility_pigeonhole`: any `n+1` distinct numbers in `[1, 2n]` contain a
  divisibility pair.
-/





theorem solution(n : ℕ) (S : Finset ℕ) (hn : n ≥ 1)
    (hcard : S.card = n + 1) (hsub : S ⊆ Finset.Icc 1 (2 * n)) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by
  -- Map each element of S to its oddPart. The image lands in the set of odd numbers in Icc 1 (2n).
  have h_map : (S.image oddPart).card ≤ n := by
    -- The image of $S$ under $oddPart$ is a subset of the set of odd numbers in $[1, 2n]$, which has cardinality $n$.
    have h_image_subset : Finset.image oddPart S ⊆ Finset.image (fun k => 2 * k + 1) (Finset.range n) := by
      intro m hm
      obtain ⟨x, hx⟩ : ∃ x ∈ S, oddPart x = m := by
        aesop
      have h_odd : Odd m := by
        exact hx.2 ▸ Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => absurd ( Nat.dvd_of_mod_eq_zero h ) ( Nat.not_dvd_ordCompl ( by norm_num ) ( by linarith [ Finset.mem_Icc.mp ( hsub hx.1 ) ] ) ) )
      have h_range : m ≤ 2 * n := by
        exact hx.2 ▸ Nat.le_trans ( Nat.div_le_self _ _ ) ( Finset.mem_Icc.mp ( hsub hx.1 ) |>.2 );
      obtain ⟨ k, rfl ⟩ := h_odd; exact Finset.mem_image.mpr ⟨ k, Finset.mem_range.mpr ( by linarith ), rfl ⟩ ;
    exact le_trans ( Finset.card_le_card h_image_subset ) ( Finset.card_image_le.trans ( by simp ) );
  -- Since $S$ has $n+1$ elements and there are only $n$ possible odd parts, by the pigeonhole principle, there must be at least two elements in $S$ with the same odd part.
  obtain ⟨a, haS, b, hbS, hab⟩ : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ oddPart a = oddPart b := by
    contrapose! h_map;
    rw [ Finset.card_image_of_injOn fun a ha b hb hab => by contrapose! hab; exact h_map a ha b hb hab ] ; linarith;
  -- Given that $oddPart a = oddPart b$, we can write $a = oddPart a * 2^{v_2(a)}$ and $b = oddPart b * 2^{v_2(b)}$.
  obtain ⟨va, hva⟩ : ∃ va, a = oddPart a * 2 ^ va := by
    exact ⟨ _, Eq.symm ( Nat.div_mul_cancel ( Nat.ordProj_dvd _ _ ) ) ⟩
  obtain ⟨vb, hvb⟩ : ∃ vb, b = oddPart b * 2 ^ vb := by
    exact ⟨ _, Eq.symm ( Nat.div_mul_cancel ( Nat.ordProj_dvd _ _ ) ) ⟩;
  -- Without loss of generality, assume $va \leq vb$.
  by_cases h_cases : va ≤ vb;
  · exact ⟨ a, haS, b, hbS, hab.1, hva.symm ▸ hvb.symm ▸ mul_dvd_mul ( by simp +decide [ hab.2 ] ) ( pow_dvd_pow _ h_cases ) ⟩;
  · exact ⟨ b, hbS, a, haS, hab.1.symm, hvb.symm ▸ hva.symm ▸ hab.2.symm ▸ Nat.mul_dvd_mul_left _ ( pow_dvd_pow _ ( le_of_not_ge h_cases ) ) ⟩
