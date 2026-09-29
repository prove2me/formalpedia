-- Prove2me | solution 1 for QuartetCodes.code3_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:15:41.253044+00:00
-- url     : https://prove2.me/submissions/b199492b-0aed-4923-b134-5f6d6b58c083

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














/-! ## Adversarial check: pure distance in ternary signature space is too weak -/





open QuartetCodes in
theorem solution(p q r s : ℕ) :
    code3 p q r s = 1 ↔ (max p r < min q s ∨ max q s < min p r) := by
  unfold code3
  split_ifs with h1 h2
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h; exfalso; omega
  · exact iff_of_true rfl h2
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h h2
