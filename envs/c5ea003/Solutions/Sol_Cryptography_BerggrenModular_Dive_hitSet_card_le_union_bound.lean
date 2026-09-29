-- Prove2me | solution 1 for Cryptography.BerggrenModular.Dive.hitSet_card_le_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:11:02.956214+00:00
-- url     : https://prove2.me/submissions/8f381a0b-86d6-48e3-a445-beef555c4003

-- Sol generated from Cryptography/BerggrenModular/TrialDivisionEquivalence.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_BlumImmunity
import Definitions.Def_Cryptography_BerggrenModular_TrialDivisionEquivalence
import Theorems.Thm_Cryptography_BerggrenModular_Dive_miss_eq

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





theorem card_reveal_add_card_avoid (N : ℕ) : (revealSet N).card + (avoidSet N).card = N := by
  simpa [revealSet, avoidSet, Finset.card_range] using
    Finset.card_filter_add_card_filter_not (s := Finset.range N) (p := Reveals N)





/-- A concrete instance of the count: modulo `15` the revealing residues are
`{3,5,6,9,10,12}`, six of them, and `3 + 5 - 2 = 6`. -/
example : revealSet 15 = {3, 5, 6, 9, 10, 12} := by decide

/-! ## Dives: sampling `t` nodes and inspecting a schedule `S` -/


theorem card_samples (N t : ℕ) : (samples N t).card = N ^ t := by
  simp [samples, Fintype.card_piFinset, Finset.card_range]



/-- Counting streams with a prescribed value-set on a schedule `S` and free values
elsewhere.  This is the combinatorial engine behind every count in this file. -/
theorem card_piFinset_ite {t : ℕ} (S : Finset (Fin t)) (A B : Finset ℕ) :
    (Fintype.piFinset (fun j => if j ∈ S then A else B)).card
      = A.card ^ S.card * B.card ^ (t - S.card) := by
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 1
  · congr 1
    simp
  · congr 1
    rw [Finset.filter_not]
    simp [Finset.card_sdiff]

theorem card_miss (N t : ℕ) (S : Finset (Fin t)) :
    ((samples N t).filter (fun f => ¬ ∃ i ∈ S, Reveals N (f i))).card
      = (avoidSet N).card ^ S.card * N ^ (t - S.card) := by
  rw [miss_eq, card_piFinset_ite, Finset.card_range]

/-- **Exact success count of a gcd dive.**  Out of the `N^t` value streams, the
schedule `S` succeeds on all but `(N − r)^{|S|} · N^{t−|S|}` of them, where
`r = #revealSet N`. -/
theorem card_hitSet (N t : ℕ) (S : Finset (Fin t)) :
    (hitSet N t S).card + (avoidSet N).card ^ S.card * N ^ (t - S.card) = N ^ t := by
  have h := Finset.card_filter_add_card_filter_not (s := samples N t)
    (p := fun f => ∃ i ∈ S, Reveals N (f i))
  rw [card_samples] at h
  calc (hitSet N t S).card + (avoidSet N).card ^ S.card * N ^ (t - S.card)
      = (hitSet N t S).card
          + ((samples N t).filter (fun f => ¬ ∃ i ∈ S, Reveals N (f i))).card := by
        rw [card_miss]
    _ = N ^ t := h

theorem card_le_of_card_S (t : ℕ) (S : Finset (Fin t)) : S.card ≤ t := by
  simpa using S.card_le_univ

/-! ## The guidance null -/




/-! ## Trial-division scaling: `α = 1` -/

/-- The elementary convexity bound `(b+d)^{s+1} ≤ b^{s+1} + (s+1)·d·(b+d)^s`. -/
theorem pow_add_le (b d s : ℕ) : (b + d) ^ (s + 1) ≤ b ^ (s + 1) + (s + 1) * d * (b + d) ^ s := by
  induction s with
  | zero => simp
  | succ n ih =>
      have hb : b ^ (n + 1) ≤ (b + d) ^ (n + 1) := Nat.pow_le_pow_left (Nat.le_add_right _ _) _
      calc (b + d) ^ (n + 2) = (b + d) * (b + d) ^ (n + 1) := by ring
        _ ≤ (b + d) * (b ^ (n + 1) + (n + 1) * d * (b + d) ^ n) := Nat.mul_le_mul_left _ ih
        _ = b ^ (n + 2) + d * b ^ (n + 1) + (n + 1) * d * (b + d) ^ (n + 1) := by ring
        _ ≤ b ^ (n + 2) + d * (b + d) ^ (n + 1) + (n + 1) * d * (b + d) ^ (n + 1) := by gcongr
        _ = b ^ (n + 2) + (n + 2) * d * (b + d) ^ (n + 1) := by ring




/-! ## Coupling back to the Berggren tree: strict under-sampling -/






open Cryptography.BerggrenModular.Dive in
theorem solution(N t : ℕ) (S : Finset (Fin t)) (hS : 1 ≤ S.card) :
    (hitSet N t S).card ≤ S.card * (revealSet N).card * N ^ (t - 1) := by
  have hs : S.card ≤ t := card_le_of_card_S t S
  obtain ⟨s, hsdef⟩ : ∃ s, S.card = s + 1 := ⟨S.card - 1, by omega⟩
  have hexact := card_hitSet N t S
  set a := (avoidSet N).card with ha
  set r := (revealSet N).card with hr
  have hsum : r + a = N := card_reveal_add_card_avoid N
  have hkey : N ^ (s + 1) ≤ a ^ (s + 1) + (s + 1) * r * N ^ s := by
    have := pow_add_le a r s
    rw [show a + r = N by omega] at this
    exact this
  have hmul : N ^ (s + 1) * N ^ (t - (s + 1)) = N ^ t := by
    rw [← pow_add]; congr 1; omega
  have hmul2 : N ^ s * N ^ (t - (s + 1)) = N ^ (t - 1) := by
    rw [← pow_add]; congr 1; omega
  have hbound : N ^ t ≤ a ^ (s + 1) * N ^ (t - (s + 1)) + (s + 1) * r * N ^ (t - 1) := by
    calc N ^ t = N ^ (s + 1) * N ^ (t - (s + 1)) := hmul.symm
      _ ≤ (a ^ (s + 1) + (s + 1) * r * N ^ s) * N ^ (t - (s + 1)) :=
          Nat.mul_le_mul_right _ hkey
      _ = a ^ (s + 1) * N ^ (t - (s + 1)) + (s + 1) * r * (N ^ s * N ^ (t - (s + 1))) := by ring
      _ = a ^ (s + 1) * N ^ (t - (s + 1)) + (s + 1) * r * N ^ (t - 1) := by rw [hmul2]
  rw [hsdef] at hexact ⊢
  omega
