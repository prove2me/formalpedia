-- Prove2me | solution 1 for Cryptography.BerggrenModular.Dive.trial_division_scaling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:13:00.632109+00:00
-- url     : https://prove2.me/submissions/6a56afbc-727a-4221-ac16-0718beaffa68

-- Sol generated from Cryptography/BerggrenModular/TrialDivisionEquivalence.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_BlumImmunity
import Definitions.Def_Cryptography_BerggrenModular_TrialDivisionEquivalence
import Theorems.Thm_Cryptography_BerggrenModular_Dive_card_revealSet_semiprime
import Theorems.Thm_Cryptography_BerggrenModular_Dive_hitSet_card_le_union_bound

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








theorem card_le_of_card_S (t : ℕ) (S : Finset (Fin t)) : S.card ≤ t := by
  simpa using S.card_le_univ

/-! ## The guidance null -/




/-! ## Trial-division scaling: `α = 1` -/





/-! ## Coupling back to the Berggren tree: strict under-sampling -/






open Cryptography.BerggrenModular.Dive in
theorem solution{p q t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hle : p ≤ q) (S : Finset (Fin t)) (hs : 4 * S.card < p) :
    2 * (hitSet (p * q) t S).card < (p * q) ^ t := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hNpos : 0 < p * q := Nat.mul_pos (by omega) (by omega)
  rcases Nat.eq_zero_or_pos S.card with h0 | h1
  · -- an empty schedule never succeeds
    have hempty : hitSet (p * q) t S = ∅ := by
      rw [Finset.card_eq_zero] at h0
      simp [hitSet, h0]
    rw [hempty]
    simpa using pow_pos hNpos t
  · have hb := hitSet_card_le_union_bound (p * q) t S h1
    rw [card_revealSet_semiprime hp hq hpq] at hb
    have hst : S.card ≤ t := card_le_of_card_S t S
    have ht1 : 1 ≤ t := le_trans h1 hst
    have hpow : (p * q) * (p * q) ^ (t - 1) = (p * q) ^ t := by
      rw [← pow_succ']; congr 1; omega
    -- the arithmetic core: `2·s·(p+q−2) < p·q` whenever `4s < p ≤ q`
    have harith : 2 * (S.card * (p + q - 2)) < p * q := by
      obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, q = b + 2 := ⟨q - 2, by omega⟩
      have hab : a ≤ b := by omega
      have hsub : a + 2 + (b + 2) - 2 = a + b + 2 := by omega
      rw [hsub]
      nlinarith [S.card, hs, hab, Nat.zero_le a, Nat.zero_le b]
    have hpos : 0 < (p * q) ^ (t - 1) := pow_pos hNpos _
    calc 2 * (hitSet (p * q) t S).card
        ≤ 2 * (S.card * (p + q - 2) * (p * q) ^ (t - 1)) := by omega
      _ = (2 * (S.card * (p + q - 2))) * (p * q) ^ (t - 1) := by ring
      _ < (p * q) * (p * q) ^ (t - 1) := by
          exact Nat.mul_lt_mul_of_lt_of_le harith (le_refl _) hpos
      _ = (p * q) ^ t := hpow
