-- Prove2me | solution 1 for QuartetCodes.qcode_eq_two_iff_restrict
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:46:44.669605+00:00
-- url     : https://prove2.me/submissions/1188fb19-7c1c-4d6f-9ac6-ed943d85cd6e

-- Sol generated from Combinatorics/QuartetCodes.lean
import Mathlib
import Definitions.Def_Combinatorics_Core
import Definitions.Def_Combinatorics_QuartetCodes
import Theorems.Thm_QuartetCodes_code3_eq_two_iff
import Theorems.Thm_QuartetCodes_pair_mem_restrict_catSystem
import Theorems.Thm_QuartetCodes_perm_val_ne

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














/-! ## Adversarial check: pure distance in ternary signature space is too weak -/





open QuartetCodes in
theorem solution{π : Equiv.Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    qcode π a b c d = 2 ↔
      (({a, d} : Finset (Fin n)) ∈ AgreementSubtrees.restrict (catSystem π) {a, b, c, d} ∨
        ({b, c} : Finset (Fin n)) ∈ AgreementSubtrees.restrict (catSystem π) {a, b, c, d}) := by
  have hset1 : ({a, d, b, c} : Finset (Fin n)) = {a, b, c, d} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hset2 : ({b, c, a, d} : Finset (Fin n)) = {a, b, c, d} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [qcode, code3_eq_two_iff (perm_val_ne hab) (perm_val_ne hac) (perm_val_ne had)
      (perm_val_ne hbc) (perm_val_ne hbd) (perm_val_ne hcd),
    show (AgreementSubtrees.restrict (catSystem π) ({a, b, c, d} : Finset (Fin n)))
      = AgreementSubtrees.restrict (catSystem π) ({a, d, b, c} : Finset (Fin n)) by rw [hset1],
    pair_mem_restrict_catSystem hab hac (Ne.symm hbd) (Ne.symm hcd)]
  rw [show (AgreementSubtrees.restrict (catSystem π) ({a, d, b, c} : Finset (Fin n)))
      = AgreementSubtrees.restrict (catSystem π) ({b, c, a, d} : Finset (Fin n)) by rw [hset1, hset2],
    pair_mem_restrict_catSystem (Ne.symm hab) hbd (Ne.symm hac) hcd]
