-- Prove2me | solution 1 for D10.card_orbits_mul_card_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:07:27.127984+00:00
-- url     : https://prove2.me/submissions/4976ec58-4dc3-405c-8f00-ee201f6f49a9

-- Sol generated from NumberTheory/MolienNecklaceCongruence.lean
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10
import Definitions.Def_NumberTheory_MolienNecklaceCongruence
import Theorems.Thm_D10_sum_fixCount_eq_card_orbits_mul

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


theorem fixCount_translation (g : Rot n) :
    fixCount (ZMod n) g = if g = 1 then n else 0 := by
  by_cases hg : g = 1
  · subst hg
    simp [fixCount, ZMod.card]
  · have hne : Multiplicative.toAdd g ≠ 0 := fun h => hg (by simpa using h)
    rw [if_neg hg, fixCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    apply hne
    have : Multiplicative.toAdd g + y = y := hy
    linear_combination (norm := abel) this












open D10 in
theorem solution(g : Rot n) :
    Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (ZMod n)))
        * Nat.card (Subgroup.zpowers g) = n := by
  classical
  have hsum := sum_fixCount_eq_card_orbits_mul (X := ZMod n) (Subgroup.zpowers g)
  have hterm : ∀ s : Subgroup.zpowers g,
      fixCount (ZMod n) (s : Rot n) = if s = (1 : Subgroup.zpowers g) then n else 0 := by
    intro s
    have hiff : ((s : Rot n) = 1) ↔ (s = 1) :=
      ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
    rw [fixCount_translation]
    simp only [hiff]
  have hval : (∑ s : Subgroup.zpowers g, fixCount (ZMod n) (s : Rot n)) = n := by
    simp only [hterm]
    rw [Finset.sum_ite_eq' Finset.univ (1 : Subgroup.zpowers g) (fun _ => n)]
    rw [if_pos (Finset.mem_univ _)]
  rw [hval] at hsum
  rw [Nat.card_eq_fintype_card (α := (Subgroup.zpowers g : Subgroup (Rot n)))]
  exact hsum.symm
