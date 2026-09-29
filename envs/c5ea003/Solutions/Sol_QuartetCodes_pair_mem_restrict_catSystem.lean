-- Prove2me | solution 1 for QuartetCodes.pair_mem_restrict_catSystem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:32:10.643228+00:00
-- url     : https://prove2.me/submissions/e9faa83b-b0ec-43e5-8b6e-f0f6b256c35e

-- Sol generated from Combinatorics/QuartetCodes.lean
import Mathlib
import Definitions.Def_Combinatorics_Core
import Definitions.Def_Combinatorics_QuartetCodes

/-!
# Quartet signatures as ternary codes

A phylogenetic tree is encoded as a word in the ternary cube indexed by quadruples of leaves: each
four-leaf set admits exactly three resolved quartet types, recorded by `code3` and, for the
caterpillar with leaf order `π`, by `qcode π`.  Under this dictionary the catalog predicate
`AgreementSubtrees.AgreeOn` on a four-leaf set becomes *equality of a letter*
(`qcode_eq_of_agreeOn`), so "no common quartet" becomes "no constant coordinate" in a ternary code.

The file proves:

* the exact ternary balance `three_mul_qclass_card` — each of the three types is displayed by
  exactly one third of all leaf orders;
* the first-moment construction `exists_quartet_avoiding_family` and, via the bridge to split
  systems, the exponential lower bound `exponential_lower_bound`:
  `¬ IsAgreementThreshold (3^v) (4v+2) 4`;
* the explicit optimal five-leaf pair `not_isAgreementThreshold_five_two`;
* the adversarial collapse `card_le_three_of_pairwise_full_distance`: over a ternary alphabet a
  family at full Hamming distance has at most three members, so the weaker avoidance notion is
  genuinely needed.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Quartet avoidance is a coding condition: if the ternary signatures of a family of trees never agree
in a coordinate, no four leaves carry a common quartet, and a random code should provide such
families with only logarithmically many trees per leaf.

## Experiment (Experimenter)
The first-moment computation is exact rather than asymptotic because the three quartet types are
exactly equinumerous under right translation by a transposition inside the quartet
(`qclass_card_eq_of_swap`): the probability that `m+1` random leaf orders agree on a fixed quartet
is exactly `3^{-m}`, and there are at most `n^4` ordered quadruples.

## Analysis (Analyst)
The union bound `n^4 < 3^m` costs one tree per `3^{1/4} ≈ 1.316` leaves.  The companion files show
the truth is nearer `1.7` per tree, so the loss is in the union bound, not in the encoding.

## Critique (Critic)
The bridge lemmas `qcode_eq_{zero,one,two}_iff_restrict` are stated in terms of the catalog's own
`restrict`, so the ternary letter is proved to record the actual restriction of the split system,
not a convenient surrogate; and `card_le_three_of_pairwise_full_distance` rules out the naive
"large minimum distance" reading of the conjecture.
-/

open Finset

open QuartetCodes








/-! ## Caterpillar trees and their quartet signatures -/


variable {n : ℕ}










/-! ## The counting (first-moment) lower bound -/


variable {n k : ℕ}










/-! ## Bridge to the split-system language of `Combinatorics.Core` -/


open AgreementSubtrees

variable {n : ℕ}


lemma univ_filter_inter (p : Fin n → Prop) [DecidablePred p] (A : Finset (Fin n)) :
    ((Finset.univ : Finset (Fin n)).filter p) ∩ A = A.filter p := by
  ext x; simp [and_comm]

lemma mem_restrict_catSystem {π : Equiv.Perm (Fin n)} {A S : Finset (Fin n)} :
    S ∈ AgreementSubtrees.restrict (catSystem π) A ↔ ∃ t : Fin n, A.filter (fun x => π x ≤ t) = S := by
  unfold AgreementSubtrees.restrict catSystem
  rw [Finset.image_image]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [← univ_filter_inter, ht]⟩
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [univ_filter_inter, ht]⟩











/-! ## Adversarial check: pure distance in ternary signature space is too weak -/





open QuartetCodes in
theorem solution{π : Equiv.Perm (Fin n)} {a b c d : Fin n} (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ({a, b} : Finset (Fin n)) ∈ AgreementSubtrees.restrict (catSystem π) {a, b, c, d}
      ↔ max (π a).val (π b).val < min (π c).val (π d).val := by
  rw [mem_restrict_catSystem]
  constructor
  · rintro ⟨t, ht⟩
    have ha : π a ≤ t := by
      have : a ∈ ({a, b, c, d} : Finset (Fin n)).filter (fun x => π x ≤ t) := by
        rw [ht]; simp
      exact (Finset.mem_filter.1 this).2
    have hb : π b ≤ t := by
      have : b ∈ ({a, b, c, d} : Finset (Fin n)).filter (fun x => π x ≤ t) := by
        rw [ht]; simp
      exact (Finset.mem_filter.1 this).2
    have hc : ¬ (π c ≤ t) := by
      intro hle
      have : c ∈ ({a, b, c, d} : Finset (Fin n)).filter (fun x => π x ≤ t) :=
        Finset.mem_filter.2 ⟨by simp, hle⟩
      rw [ht] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hac rfl
      · exact hbc rfl
    have hd : ¬ (π d ≤ t) := by
      intro hle
      have : d ∈ ({a, b, c, d} : Finset (Fin n)).filter (fun x => π x ≤ t) :=
        Finset.mem_filter.2 ⟨by simp, hle⟩
      rw [ht] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact had rfl
      · exact hbd rfl
    rw [Fin.le_def] at ha hb
    rw [Fin.not_le, Fin.lt_def] at hc hd
    omega
  · intro hcond
    refine ⟨max (π a) (π b), ?_⟩
    have hmax : (max (π a) (π b)).val = max (π a).val (π b).val := Fin.coe_max _ _
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hle⟩
      rw [Fin.le_def, hmax] at hle
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hle (by omega)
      · exact absurd hle (by omega)
    · rintro (rfl | rfl)
      · exact ⟨by simp, le_max_left _ _⟩
      · exact ⟨by simp, le_max_right _ _⟩
