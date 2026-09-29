-- Prove2me | solution 1 for QuartetCodes.three_mul_qclass_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:21:57.737139+00:00
-- url     : https://prove2.me/submissions/2500f5e6-87c6-48f1-93da-b4bea43f472c

-- Sol generated from Combinatorics/QuartetCodes.lean
import Mathlib
import Definitions.Def_Combinatorics_Core
import Definitions.Def_Combinatorics_QuartetCodes
import Theorems.Thm_QuartetCodes_code3_swap_23
import Theorems.Thm_QuartetCodes_code3_swap_24
import Theorems.Thm_QuartetCodes_perm_val_ne
import Theorems.Thm_QuartetCodes_qclass_card_eq_of_swap

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





/-- The three code values of `Fin 3` are exhaustive. -/
lemma fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by revert x; decide



/-! ## Caterpillar trees and their quartet signatures -/


variable {n : ℕ}



/-- Precomposing the leaf order with the transposition of the second and third leaf of a quartet
swaps the quartet types `0` and `1`. -/
lemma qcode_mul_swap_bc {π : Equiv.Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    qcode (π * Equiv.swap b c) a b c d = Equiv.swap (0 : Fin 3) 1 (qcode π a b c d) := by
  have ha : (π * Equiv.swap b c) a = π a := by
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac]
  have hb : (π * Equiv.swap b c) b = π c := by simp [Equiv.Perm.mul_apply]
  have hc : (π * Equiv.swap b c) c = π b := by simp [Equiv.Perm.mul_apply]
  have hd : (π * Equiv.swap b c) d = π d := by
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hbd) (Ne.symm hcd)]
  unfold qcode
  rw [ha, hb, hc, hd]
  exact code3_swap_23 (perm_val_ne hab) (perm_val_ne hac) (perm_val_ne had) (perm_val_ne hbc)
    (perm_val_ne hbd) (perm_val_ne hcd)

/-- Precomposing the leaf order with the transposition of the second and fourth leaf of a quartet
swaps the quartet types `0` and `2`. -/
lemma qcode_mul_swap_bd {π : Equiv.Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    qcode (π * Equiv.swap b d) a b c d = Equiv.swap (0 : Fin 3) 2 (qcode π a b c d) := by
  have ha : (π * Equiv.swap b d) a = π a := by
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab had]
  have hb : (π * Equiv.swap b d) b = π d := by simp [Equiv.Perm.mul_apply]
  have hc : (π * Equiv.swap b d) c = π c := by
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hbc) hcd]
  have hd : (π * Equiv.swap b d) d = π b := by simp [Equiv.Perm.mul_apply]
  unfold qcode
  rw [ha, hb, hc, hd]
  exact code3_swap_24 (perm_val_ne hab) (perm_val_ne hac) (perm_val_ne had) (perm_val_ne hbc)
    (perm_val_ne hbd) (perm_val_ne hcd)






/-! ## The counting (first-moment) lower bound -/


variable {n k : ℕ}










/-! ## Bridge to the split-system language of `Combinatorics.Core` -/


open AgreementSubtrees

variable {n : ℕ}














/-! ## Adversarial check: pure distance in ternary signature space is too weak -/





open QuartetCodes in
theorem solution{a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (t : Fin 3) :
    3 * (qclass a b c d t).card = Fintype.card (Equiv.Perm (Fin n)) := by
  have hswap01 : ∀ u : Fin 3, (qclass a b c d u).card
      = (qclass a b c d (Equiv.swap (0 : Fin 3) 1 u)).card := by
    refine qclass_card_eq_of_swap (Equiv.swap b c) (Equiv.swap (0 : Fin 3) 1) ?_ ?_ ?_
    · exact Equiv.swap_mul_self b c
    · exact Equiv.swap_mul_self (0 : Fin 3) 1
    · intro π; exact qcode_mul_swap_bc hab hac had hbc hbd hcd
  have hswap02 : ∀ u : Fin 3, (qclass a b c d u).card
      = (qclass a b c d (Equiv.swap (0 : Fin 3) 2 u)).card := by
    refine qclass_card_eq_of_swap (Equiv.swap b d) (Equiv.swap (0 : Fin 3) 2) ?_ ?_ ?_
    · exact Equiv.swap_mul_self b d
    · exact Equiv.swap_mul_self (0 : Fin 3) 2
    · intro π; exact qcode_mul_swap_bd hab hac had hbc hbd hcd
  have h01 : (qclass a b c d 0).card = (qclass a b c d 1).card := by
    simpa using hswap01 0
  have h02 : (qclass a b c d 0).card = (qclass a b c d 2).card := by
    simpa using hswap02 0
  have hsum : Fintype.card (Equiv.Perm (Fin n))
      = ∑ u : Fin 3, (qclass a b c d u).card := by
    rw [← Finset.card_univ]
    simp only [qclass]
    exact Finset.card_eq_sum_card_fiberwise
      (f := fun π : Equiv.Perm (Fin n) => qcode π a b c d)
      (t := (Finset.univ : Finset (Fin 3)))
      (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [hsum, Fin.sum_univ_three]
  rcases fin3_cases t with h | h | h <;> subst h <;> omega
