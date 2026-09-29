-- Prove2me | Theorems.Thm_CutIndexedSingleton_hammingDist_le_of_proj_eq
-- name    : CutIndexedSingleton.hammingDist_le_of_proj_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:23:27.265619+00:00
-- url     : https://prove2.me/theorems/c9fa4455-a9de-4f10-8fde-763edb8b4abd
-- title:
--   Two words that agree on a cut differ on at most its complement.
-- statement:
--   Two words that agree on a cut differ on at most its complement.
--
--   ```lean
--   theorem CutIndexedSingleton.hammingDist_le_of_proj_eq{x y : Word n q} {S : Finset (Fin n)}
--       (h : proj S x = proj S y) : hammingDist x y ≤ n - S.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CutIndexedSingleton.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CutIndexedSingleton.lean#L301

-- Thm stub generated from Novelty/CutIndexedSingleton.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedSingleton

/-!
# Cut-indexed defects I: finite cut data and the cut-wise Singleton inequality

A *tensor network* on `n` sites with local dimension `q` assigns to every **cut**
`S ⊆ Fin n` a *bond dimension* `rank S`: the number of internal degrees of
freedom that have to cross the cut in order to reconstruct the global object
from its two halves.  This file isolates the purely finite, order-theoretic
content of that notion and proves the sharpest Singleton-type inequality it
supports.

## Finite cut data

`CutData n q` (this file) is a function `rank : Finset (Fin n) → ℕ` together with
a *total* dimension `total` and three axioms:

* `rank_empty_le` : the empty cut carries a single bond, `rank ∅ ≤ 1`;
* `rank_mono`     : enlarging a cut cannot decrease the bond dimension;
* `rank_insert_le`: one extra site multiplies the bond dimension by at most `q`.

A cut datum is **`d`-resolving** (`CutData.Resolving`) when every cut missing at
most `d - 1` sites already carries the whole object: `rank S = total` as soon as
`n - |S| < d`.  This is the abstract shadow of "minimum distance `d`": a
codeword, or a tensor-network state, is determined by any `n - d + 1` of its
sites.

## Main results

* `CutData.rank_le_pow`            : `rank S ≤ q ^ |S|` (the local Hilbert-space bound);
* `CutData.rank_le_mul_of_subset`  : `rank T ≤ q ^ (|T| - |S|) * rank S` for `S ⊆ T`
  — the *cut-monotonicity* engine of the file;
* `CutData.cutwise_singleton`      : **the cut-wise Singleton inequality**
  `total ≤ q ^ (k - |S|) * rank S` for every cut `S` with `|S| ≤ k := n + 1 - d`;
* `CutData.singleton_bound`        : the classical Singleton bound `total ≤ q ^ k`,
  recovered at the empty cut `S = ∅`;
* `CutData.cutDefect_eq_zero_iff`  : the *cut-indexed defect*
  `δ(S) = q ^ (k - |S|) * rank S - total` vanishes precisely at the cuts where the
  cut-wise inequality is tight;
* `CutData.rank_eq_pow_of_saturated`: **rigidity.**  If the *global* Singleton
  bound is saturated (`total = q ^ k`, the MDS condition) then *every* defect
  with `|S| ≤ k` vanishes and moreover `rank S = q ^ |S|`: an MDS cut datum is
  maximally entangled across every cut below the plateau.

## Codes as cut data

`codeCutData C` turns a finite codebook `C ⊆ (Fin n → Fin q)` into cut data with
`rank S = ` the number of distinct restrictions of codewords to `S` (the
classical bond dimension across the cut), and
`resolving_codeCutData` shows that minimum distance `d` makes it `d`-resolving.
Specialising the abstract theorems gives:

* `singleton_bound_of_minDist`   : the Singleton bound `|C| ≤ q ^ (n + 1 - d)`;
* `cutRank_eq_pow_of_isMDS`      : every `|S| ≤ k` projection of an MDS code is
  onto (`the "every k coordinates form an information set" theorem`);
* `fiber_card_of_isMDS`          : every such projection is *balanced* — each of
  the `q ^ |S|` patterns has exactly `q ^ (k - |S|) `preimages.  This is the
  combinatorial input to the entropy plateau of `CutIndexedEntropy.lean`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the Singleton bound is not a statement about codes but
about *cut data*: any assignment of bond dimensions to cuts that (a) grows by a
factor at most `q` per site and (b) already saturates at co-size `< d` obeys
`total ≤ q ^ (k - |S|) * rank S` at every cut, with the classical bound the
`S = ∅` shadow of a whole family of cut-indexed inequalities.

Experiment (Experimenter): formalised `CutData` with the three axioms above.  The
proof engine turned out to be a *single-site* induction (`rank_insert_le`),
iterated over `T \ S` by `Finset.induction`; no distance hypothesis enters until
the very last step, where `Finset.exists_superset_card_eq` produces an
information set `T ⊇ S` of size exactly `k`.

Experiment (Experimenter, second run): the rigidity statement was first attempted
as "MDS ⇒ projections are injective on a `k`-set", which is *false* in the range
`|S| < k`; the correct statement is *surjectivity* `rank S = q ^ |S|`, obtained by
squeezing `q ^ k = total ≤ q ^ (k - |S|) * rank S ≤ q ^ (k - |S|) * q ^ |S| = q ^ k`.
The same squeeze, applied to each fibre viewed as a sub-cut-datum, gives the exact
fibre count `q ^ (k - |S|)` — a genuinely recursive use of the main theorem.

Analysis (Analyst): the defect `δ(S)` is monotone in nothing and vanishes at
`S = ∅` exactly for MDS data, but its vanishing for *all* `S` is strictly
stronger than MDS only when `q = 1`; for `q ≥ 2` the two are equivalent, which is
the content of `rank_eq_pow_of_saturated`.

Critique (Critic): the axiom `rank_empty_le : rank ∅ ≤ 1` (rather than `= 1`)
keeps the empty codebook inside the theory, at no cost to any theorem; and the
hypothesis `1 ≤ d` in the Singleton statements is necessary — with `d = 0` the
`ℕ`-truncated `k = n + 1` exceeds `n` and no information set of that size exists.
-/

open Finset

open CutIndexedSingleton

variable {n q : ℕ}


/-! ## Abstract finite cut data -/


open CutData

variable (D : CutData n q)













/-! ## Codes as cut data -/

theorem CutIndexedSingleton.hammingDist_le_of_proj_eq{x y : Word n q} {S : Finset (Fin n)}
    (h : proj S x = proj S y) : hammingDist x y ≤ n - S.card := by sorry
