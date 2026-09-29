-- Prove2me | Theorems.Thm_QuartetCodes_code3_swap_23
-- name    : QuartetCodes.code3_swap_23
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:26:19.572176+00:00
-- url     : https://prove2.me/theorems/a6f536ca-0a0e-4373-b21d-a945ccd4798d
-- title:
--   Transposing the second and third position swaps the quartet types `0` and `1`.
-- statement:
--   Transposing the second and third position swaps the quartet types `0` and `1`.
--
--   ```lean
--   theorem QuartetCodes.code3_swap_23{p q r s : ℕ} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
--       (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
--       code3 p r q s = Equiv.swap (0 : Fin 3) 1 (code3 p q r s) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/QuartetCodes.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/QuartetCodes.lean#L90

-- Thm stub generated from Combinatorics/QuartetCodes.lean
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

theorem QuartetCodes.code3_swap_23{p q r s : ℕ} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    code3 p r q s = Equiv.swap (0 : Fin 3) 1 (code3 p q r s) := by sorry
