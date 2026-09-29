-- Prove2me | solution 1 for Cryptography.BerggrenModular.Dive.reachableReveal_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:11:03.574616+00:00
-- url     : https://prove2.me/submissions/93e84623-4f01-4975-b3bc-b8d042685db9

-- Sol generated from Cryptography/BerggrenModular/TrialDivisionEquivalence.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_BlumImmunity
import Definitions.Def_Cryptography_BerggrenModular_TrialDivisionEquivalence

/-!
# Trial-division equivalence and the guidance null for gcd dives

Experiment 555 measures the modular Berggren descent as a factoring device: a
"dive" walks nodes of the mod-`N` tree and tests `gcd(value, N)`.  The measured
exponent is `α = 1.007 ± 0.088` — the work to split `N` scales like the *smallest
prime factor*, i.e. trial division, and not like `√p_min` (Pollard ρ).  Two
further findings are (i) the various guidance heuristics gave no honest
improvement, and (ii) the naive `z = 12–24` "improvements" were pure
traversal-shape artefacts.

This file proves the exact combinatorial theorems behind those three statements
for the *ambient* model — a gcd dive that inspects `t` residues modulo `N` — and
then couples them back to the Berggren tree through
`Cryptography.BerggrenModular.BlumImmunity`.

## Main results

* `card_revealSet_semiprime` — modulo `N = p·q` exactly `p + q − 2` residues have
  a nontrivial gcd with `N`: the per-node hit rate is `(p+q−2)/pq ≍ 1/p_min`.
* `card_hitSet` — an **exact** formula for the number of `t`-node dives that
  succeed while inspecting the index set `S`.
* `hitSet_card_eq_of_card_eq` — **the guidance null.**  The success count depends
  on the inspection schedule `S` *only through its cardinality*: no ordering, no
  selection rule, no traversal shape changes it by a single dive.  Any measured
  "improvement" at fixed node budget is an artefact.
* `hitSet_card_eq_scaled` — the sharp form: examining `s` of `t` nodes has exactly
  the success rate of examining the first `s`.
* `hitSet_card_le_union_bound` — the union bound `#hits ≤ s·(p+q−2)·N^{t−1}`.
* `trial_division_scaling` — **α = 1.**  If the dive inspects fewer than `p/4`
  nodes its success probability is below `1/2`; equivalently
  `needs_linear_in_min_prime`: constant success needs `Ω(p_min)` nodes.  A ρ-like
  `O(√p_min)` dive is therefore impossible in this model.
* `card_reachableReveal` and `berggren_undersampling_ratio` — the Berggren
  hypotenuse stream can reach only `p − 1` of the `p + q − 2` revealing residues
  when `p ≡ 3 (mod 4)`: a strict, quantified under-sampling.
-/

open Cryptography
open BerggrenModular
open Dive

/-! ## The revealing residues -/










/-- A concrete instance of the count: modulo `15` the revealing residues are
`{3,5,6,9,10,12}`, six of them, and `3 + 5 - 2 = 6`. -/
example : revealSet 15 = {3, 5, 6, 9, 10, 12} := by decide

/-! ## Dives: sampling `t` nodes and inspecting a schedule `S` -/









/-! ## The guidance null -/




/-! ## Trial-division scaling: `α = 1` -/





/-! ## Coupling back to the Berggren tree: strict under-sampling -/






open Cryptography.BerggrenModular.Dive in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (revealSet (p * q)).filter (fun x => ¬ p ∣ x)
      = ((Finset.range (p * q)).filter (fun x => q ∣ x)).erase 0 := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  ext x
  simp only [revealSet, Reveals, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hx, h1, h2⟩, hnp⟩
    refine ⟨?_, hx, ?_⟩
    · rintro rfl
      simp only [Nat.gcd_zero_left] at h2
      omega
    · -- `gcd x N > 1` forces a prime factor, which must be `q`
      obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd x (p * q)) (by omega)
      have hrN : r ∣ p * q := hrd.trans (Nat.gcd_dvd_right _ _)
      have hrx : r ∣ x := hrd.trans (Nat.gcd_dvd_left _ _)
      rcases (Nat.Prime.dvd_mul hr).1 hrN with h | h
      · exact absurd (((Nat.prime_dvd_prime_iff_eq hr hp).1 h) ▸ hrx) hnp
      · exact ((Nat.prime_dvd_prime_iff_eq hr hq).1 h) ▸ hrx
  · rintro ⟨hx0, hx, hqx⟩
    have hnp : ¬ p ∣ x := by
      intro hpx
      have : p * q ∣ x := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpx hqx
      exact hx0 (Nat.eq_zero_of_dvd_of_lt this hx)
    refine ⟨⟨hx, ?_, ?_⟩, hnp⟩
    · have hqg : q ∣ Nat.gcd x (p * q) := Nat.dvd_gcd hqx (dvd_mul_left q p)
      have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) hqg
      omega
    · have hgd : Nat.gcd x (p * q) ∣ p * q := Nat.gcd_dvd_right _ _
      have hgx : Nat.gcd x (p * q) ∣ x := Nat.gcd_dvd_left _ _
      rcases Nat.lt_or_ge (Nat.gcd x (p * q)) (p * q) with h | h
      · exact h
      · exfalso
        have : Nat.gcd x (p * q) = p * q :=
          le_antisymm (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hgd) h
        rw [this] at hgx
        exact hx0 (Nat.eq_zero_of_dvd_of_lt hgx hx)
