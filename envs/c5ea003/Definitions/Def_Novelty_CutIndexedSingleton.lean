-- Prove2me | Definitions.Def_Novelty_CutIndexedSingleton
-- name    : Novelty_CutIndexedSingleton
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:10:14.658258+00:00
-- url     : https://prove2.me/theorems/ec5f324a-bfbe-4f0e-a980-50a79a535764
-- title:
--   Aether Catalog definitions — Novelty_CutIndexedSingleton
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CutIndexedSingleton`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CutIndexedSingleton.lean by skeleton subtraction
import Mathlib

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

namespace CutIndexedSingleton

variable {n q : ℕ}

/-- A word of length `n` over an alphabet of size `q`. -/
abbrev Word (n q : ℕ) := Fin n → Fin q

/-! ## Abstract finite cut data -/

/-- **Finite tensor-network cut data** on `n` sites with local dimension `q`:
a bond dimension for every cut, a total dimension, and the three structural
axioms (unit empty cut, monotonicity, one-site growth). -/
structure CutData (n q : ℕ) where
  /-- the bond dimension across the cut `S | Sᶜ`. -/
  rank : Finset (Fin n) → ℕ
  /-- the total dimension of the object being cut. -/
  total : ℕ
  /-- the empty cut carries at most one bond. -/
  rank_empty_le : rank ∅ ≤ 1
  /-- enlarging a cut cannot decrease the bond dimension. -/
  rank_mono : ∀ {S T : Finset (Fin n)}, S ⊆ T → rank S ≤ rank T
  /-- adding one site multiplies the bond dimension by at most `q`. -/
  rank_insert_le : ∀ (S : Finset (Fin n)) (a : Fin n), rank (insert a S) ≤ q * rank S

namespace CutData

variable (D : CutData n q)

/-- The **Singleton dimension** `k = n + 1 - d` of a `d`-resolving cut datum. -/
def sdim (n d : ℕ) : ℕ := n + 1 - d

/-- A cut datum is `d`-**resolving** when every cut missing fewer than `d` sites
already carries the whole object. -/
def Resolving (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), n - S.card < d → D.rank S = D.total






/-- The **cut-indexed defect** of a `d`-resolving cut datum: the slack in the
cut-wise Singleton inequality at the cut `S`. -/
def cutDefect (d : ℕ) (S : Finset (Fin n)) : ℕ :=
  q ^ (sdim n d - S.card) * D.rank S - D.total




end CutData

/-! ## Codes as cut data -/

/-- The restriction of a word to a cut. -/
def proj (S : Finset (Fin n)) (c : Word n q) : {i // i ∈ S} → Fin q := fun i => c i.1

/-- The **classical bond dimension** of a codebook across a cut: the number of
distinct patterns the codewords produce on `S`. -/
def cutRank (C : Finset (Word n q)) (S : Finset (Fin n)) : ℕ := (C.image (proj S)).card

/-- A codebook has **minimum distance at least `d`** when distinct codewords
disagree on at least `d` sites. -/
def MinDist (C : Finset (Word n q)) (d : ℕ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y

lemma cutRank_empty_le (C : Finset (Word n q)) : cutRank C (∅ : Finset (Fin n)) ≤ 1 := by
  classical
  simpa [cutRank] using Finset.card_le_univ (C.image (proj (∅ : Finset (Fin n))))

lemma cutRank_mono {C : Finset (Word n q)} {S T : Finset (Fin n)} (h : S ⊆ T) :
    cutRank C S ≤ cutRank C T := by
  classical
  have himg : C.image (proj S) = (C.image (proj T)).image
      (fun y : {i // i ∈ T} → Fin q => fun i : {i // i ∈ S} => y ⟨i.1, h i.2⟩) := by
    rw [Finset.image_image]
    rfl
  rw [cutRank, himg]
  exact Finset.card_image_le

lemma cutRank_insert_le (C : Finset (Word n q)) (S : Finset (Fin n)) (a : Fin n) :
    cutRank C (insert a S) ≤ q * cutRank C S := by
  classical
  have hinj : Set.InjOn (fun y : {i // i ∈ insert a S} → Fin q =>
      ((fun i : {i // i ∈ S} => y ⟨i.1, Finset.mem_insert_of_mem i.2⟩),
        y ⟨a, Finset.mem_insert_self a S⟩))
      (C.image (proj (insert a S)) : Set _) := by
    intro y _ z _ hyz
    funext i
    obtain ⟨i, hi⟩ := i
    rcases Finset.mem_insert.mp hi with rfl | hiS
    · exact congrArg Prod.snd hyz
    · exact congrFun (congrArg Prod.fst hyz) ⟨i, hiS⟩
  have hmap : ∀ y ∈ C.image (proj (insert a S)),
      ((fun i : {i // i ∈ S} => y ⟨i.1, Finset.mem_insert_of_mem i.2⟩),
        y ⟨a, Finset.mem_insert_self a S⟩) ∈ (C.image (proj S)) ×ˢ (Finset.univ : Finset (Fin q)) := by
    intro y hy
    refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ?_, Finset.mem_univ _⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨c, hc, rfl⟩
  have := Finset.card_le_card_of_injOn _ hmap hinj
  simpa [cutRank, Finset.card_product, mul_comm] using this



/-- The cut data of a finite codebook. -/
def codeCutData (C : Finset (Word n q)) : CutData n q where
  rank := cutRank C
  total := C.card
  rank_empty_le := cutRank_empty_le C
  rank_mono := cutRank_mono
  rank_insert_le := cutRank_insert_le C






/-- A codebook is **MDS** when it meets the Singleton bound with equality. -/
def IsMDS (C : Finset (Word n q)) (d : ℕ) : Prop :=
  MinDist C d ∧ C.card = q ^ CutData.sdim n d


/-! ### Fibres -/

/-- The fibre of the codebook over a pattern on a cut. -/
def fiber (C : Finset (Word n q)) (S : Finset (Fin n)) (y : {i // i ∈ S} → Fin q) :
    Finset (Word n q) :=
  C.filter (fun c => proj S c = y)






end CutIndexedSingleton


