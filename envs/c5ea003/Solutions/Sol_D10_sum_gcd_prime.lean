-- Prove2me | solution 1 for D10.sum_gcd_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:13:27.436986+00:00
-- url     : https://prove2.me/submissions/9769a06b-a2b1-4562-b578-fada9ebc9da8

-- Sol generated from NumberTheory/MolienNecklaceCongruence.lean
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10
import Definitions.Def_NumberTheory_MolienNecklaceCongruence

/-!
# The Molien/Burnside machinery as an arithmetic engine: necklace congruences

This file is the number-theoretic pay-off of the Molien/Burnside framework of
`Catalog.NumberTheory.MolienBurnsideD10`.  The bridge is the *cycle-index* identity

`|X^g| = k ^ (number of ⟨g⟩-orbits on Y)`   for `X = Coloring Y k = (Y → Fin k)`,

proved here as `D10.Coloring.fixCount_coloring`.  Feeding it into the Burnside divisibility
`|G| ∣ ∑_{g ∈ G} |X^g|` for the rotation action of `ℤ/n` on itself yields the classical
**necklace congruence**

`n ∣ ∑_{a ∈ ℤ/n} k ^ gcd(n, a)`,

and, specialising to a prime, **Fermat's little theorem** `k^p ≡ k (mod p)`.  Thus the
Molien invariant, which the Klein four-group example of the companion file shows to be a
*strictly coarser* invariant than the Burnside mark vector, is nevertheless strong enough
to carry genuine arithmetic content.
-/

open D10

open Finset MulAction


open Coloring

variable {G Y : Type*} [Group G] [MulAction G Y] {k : ℕ}



instance : SMul G (Coloring Y k) := ⟨fun g f => (fun y => f (g⁻¹ • y) : Y → Fin k)⟩









variable {n : ℕ} [NeZero n]














open D10 in
theorem solution(p k : ℕ) [NeZero p] (hp : p.Prime) :
    (∑ a : ZMod p, k ^ Nat.gcd p a.val) = (p - 1) * k + k ^ p := by
  classical
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : ZMod p))]
  have hzero : k ^ Nat.gcd p (ZMod.val (0 : ZMod p)) = k ^ p := by
    rw [ZMod.val_zero, Nat.gcd_zero_right]
  have hother : ∀ a ∈ (Finset.univ.erase (0 : ZMod p)),
      k ^ Nat.gcd p a.val = k := by
    intro a ha
    rw [Finset.mem_erase] at ha
    have hval : a.val ≠ 0 := by
      intro h
      apply ha.1
      have hc := ZMod.natCast_rightInverse (n := p) a
      rw [h] at hc
      simpa using hc.symm
    have hlt : a.val < p := ZMod.val_lt a
    have : Nat.gcd p a.val = 1 := by
      rcases (Nat.coprime_or_dvd_of_prime hp a.val) with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hval) h) (not_le.mpr hlt)
    rw [this, pow_one]
  rw [Finset.sum_congr rfl hother, hzero, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
