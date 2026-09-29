-- Prove2me | Definitions.Def_Combinatorics_QuartetCodesIndexEight
-- name    : Combinatorics_QuartetCodesIndexEight
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:48:14.759683+00:00
-- url     : https://prove2.me/theorems/0e90c144-a5d8-4dc4-9c0e-d41c2685e451
-- title:
--   Aether Catalog definitions — Combinatorics_QuartetCodesIndexEight
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.QuartetCodesIndexEight`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/QuartetCodesIndexEight.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
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

namespace QuartetCodes

section IndexEight

variable {n : ℕ}

/-- Exchange of the two smallest values. -/
def sw01 (x : ℕ) : ℕ := if x = 0 then 1 else if x = 1 then 0 else x


/-- Whether the four entries of a quadruple are pairwise distinct. -/
def QuadDistinct (q : Fin n × Fin n × Fin n × Fin n) : Prop :=
  q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧ q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧
    q.2.2.1 ≠ q.2.2.2

instance : DecidablePred (QuadDistinct (n := n)) := fun _ => by unfold QuadDistinct; infer_instance

/-- The quartet signature on nondegenerate quadruples (dummy value `0` on degenerate ones). -/
def sigD (π : Equiv.Perm (Fin n)) : Fin n × Fin n × Fin n × Fin n → Fin 3 :=
  fun q => if QuadDistinct q then qcode π q.1 q.2.1 q.2.2.1 q.2.2.2 else 0

/-- The exchange of the two lowest positions. -/
def lowSwap (hn : 4 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩




/-- The eight caterpillar symmetries: products of the reversal `r` and the two cherry
exchanges `a` and `b = r * a * r`. -/
def symm8 (hn : 4 ≤ n) : Fin 8 → Equiv.Perm (Fin n) :=
  let a := lowSwap hn
  let r := (Fin.revPerm : Equiv.Perm (Fin n))
  let b := r * a * r
  ![1, a, b, a * b, r, r * a, r * b, r * a * b]



/-- Evaluation of a permutation at the first and the last position. -/
def evalEnds (hn : 4 ≤ n) (g : Equiv.Perm (Fin n)) : ℕ × ℕ :=
  ((g ⟨0, by omega⟩).val, (g ⟨n - 1, by omega⟩).val)








end IndexEight

end QuartetCodes


