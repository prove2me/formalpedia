-- Prove2me | Theorems.Thm_QuartetCodes_eight_mul_card_image_sigD_le
-- name    : QuartetCodes.eight_mul_card_image_sigD_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:28:03.120487+00:00
-- url     : https://prove2.me/theorems/8f8397db-8da9-482c-92e3-5c53d126445b
-- title:
--   Packing bound with the exact conjectural index.
-- statement:
--   **Packing bound with the exact conjectural index.**  At most `n!/8` leaf orders carry distinct
--   quartet signatures.
--
--   ```lean
--   theorem QuartetCodes.eight_mul_card_image_sigD_le(hn : 4 ≤ n) :
--       8 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD).card ≤ Nat.factorial n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/QuartetCodesIndexEight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/QuartetCodesIndexEight.lean#L195

-- Thm stub generated from Combinatorics/QuartetCodesIndexEight.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesIndexEight
import Definitions.Def_Combinatorics_QuartetCodesRate

/-!
# The caterpillar quartet code has at most `n!/8` codewords

`Combinatorics.QuartetCodesRate` proves the packing bound `2 · #code ≤ n!` from the reversal
symmetry of a caterpillar.  Here the bound is improved to the conjecturally exact index,
`8 · #code ≤ n!`, by adding the two *cherry* symmetries: exchanging the two leaves at either end of
the caterpillar does not change any quartet.

Because a degenerate quadruple (one with a repeated leaf) is *not* invariant under the cherry
symmetry, the signature used here is the honest one: it is the quartet letter on quadruples of
pairwise distinct leaves and a fixed dummy value elsewhere (`sigD`).

The three generators are reversal `r`, the exchange `a` of the two lowest positions, and
`b = r * a * r`, the exchange of the two highest positions.  Their eight products are pairwise
distinct as soon as `n ≥ 4`, which is verified by evaluating each of them at the first and the last
leaf position.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
The quartet-signature fibres of `Sym(n)` have size exactly `8`; the computation in
`ComputationalEvidence.md` confirms this for `n = 4, 5, 6, 7`, and `card_image_sig5 = 15 = 5!/8`
confirms it formally at `n = 5`.  The `≤ n!/8` half should be provable for all `n` by exhibiting
the eight symmetries.

## Experiment (Experimenter)
The delicate point is the cherry symmetry: swapping the two *values* `0` and `1` flips the
comparison between the leaves carrying them, so the order-congruence lemma `code3_congr` does not
apply.  Instead the invariance is proved by direct case analysis (`code3_sw01`, ~1000 branches
discharged by `omega`), which is valid precisely because the two swapped values are the two global
minima and therefore stay the "low pair" of every quadruple containing both.

## Analysis (Analyst)
The three symmetries are the automorphisms of an unrooted caterpillar, and the argument shows they
act freely on `Sym(n)`, giving the packing bound `8 · #code ≤ n!`.  The converse inequality —
identifiability of the caterpillar from its quartets up to these eight relabellings — is the open
half recorded in `FUTURE_DIRECTIONS.md`.

## Critique (Critic)
Invariance is stated for the signature on *all* quadruples with a dummy value on degenerate ones, so
the theorem is about a genuine finite code, and no quadruple is quietly excluded.  The eight
symmetries are proved pairwise distinct for every `n ≥ 4`, not just for small `n`.
-/

open Finset

open QuartetCodes


variable {n : ℕ}

theorem QuartetCodes.eight_mul_card_image_sigD_le(hn : 4 ≤ n) :
    8 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD).card ≤ Nat.factorial n := by sorry
