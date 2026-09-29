-- Prove2me | Definitions.Def_Combinatorics_QuartetCodes
-- name    : Combinatorics_QuartetCodes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:45:29.090064+00:00
-- url     : https://prove2.me/theorems/d25dc418-b543-4cd3-825c-bb3e82719dcc
-- title:
--   Aether Catalog definitions — Combinatorics_QuartetCodes
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.QuartetCodes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/QuartetCodes.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_Core

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

namespace QuartetCodes

/-- The three resolved quartet types of four (distinct) positions `p q r s`:
`0` means the pairing `{p,q} | {r,s}`, `1` means `{p,r} | {q,s}`, `2` means `{p,s} | {q,r}`. -/
def code3 (p q r s : ℕ) : Fin 3 :=
  if max p q < min r s ∨ max r s < min p q then 0
  else if max p r < min q s ∨ max q s < min p r then 1
  else 2







/-! ## Caterpillar trees and their quartet signatures -/

section Caterpillar

variable {n : ℕ}

/-- The quartet type that the caterpillar tree with leaf order `π` displays on the four leaves
`a b c d`. -/
def qcode (π : Equiv.Perm (Fin n)) (a b c d : Fin n) : Fin 3 :=
  code3 (π a).val (π b).val (π c).val (π d).val




/-- The set of leaf orders realising a prescribed quartet type on `a b c d`. -/
def qclass (a b c d : Fin n) (t : Fin 3) : Finset (Equiv.Perm (Fin n)) :=
  {π : Equiv.Perm (Fin n) | qcode π a b c d = t}




end Caterpillar

/-! ## The counting (first-moment) lower bound -/

section LowerBound

variable {n k : ℕ}

/-- The families of leaf orders that all display one and the same quartet type on `a b c d`. -/
def sameCodeSet (i₀ : Fin k) (a b c d : Fin n) : Finset (Fin k → Equiv.Perm (Fin n)) :=
  {T | ∀ i, qcode (T i) a b c d = qcode (T i₀) a b c d}





/-- The set of quadruples of pairwise distinct leaves. -/
def distinctQuads (n : ℕ) : Finset (Fin n × Fin n × Fin n × Fin n) :=
  {q | q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧ q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧
    q.2.2.1 ≠ q.2.2.2}



end LowerBound

/-! ## Bridge to the split-system language of `Combinatorics.Core` -/

section Bridge

open AgreementSubtrees

variable {n : ℕ}

/-- The split system displayed by the caterpillar tree with leaf order `π`: its splits are the
initial segments of the order. -/
def catSystem (π : Equiv.Perm (Fin n)) : SplitSystem (Fin n) :=
  (Finset.univ : Finset (Fin n)).image (fun t => (Finset.univ : Finset (Fin n)).filter
    (fun x => π x ≤ t))












end Bridge

/-! ## Adversarial check: pure distance in ternary signature space is too weak -/

section CodingCollapse


end CodingCollapse

end QuartetCodes


