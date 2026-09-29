-- Prove2me | solution 1 for CutIndexedSingleton.singleton_bound_of_minDist
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:45:51.212984+00:00
-- url     : https://prove2.me/submissions/6301540c-0fef-497d-ada2-af4688ef8130

import Mathlib
import Definitions.Def_Novelty_CutIndexedSingleton

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Novelty/CutIndexedSingleton.lean ====
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

-- [dropped: platform already declares Word]
-- [dropped: platform already declares CutData]
namespace CutData

variable (D : CutData n q)

-- [dropped: platform already declares sdim]
-- [dropped: platform already declares Resolving]
theorem rank_le_pow (S : Finset (Fin n)) : D.rank S ≤ q ^ S.card := by
  classical
  induction S using Finset.induction with
  | empty => simpa using D.rank_empty_le
  | insert a S ha ih =>
      calc D.rank (insert a S) ≤ q * D.rank S := D.rank_insert_le S a
        _ ≤ q * q ^ S.card := Nat.mul_le_mul_left _ ih
        _ = q ^ (insert a S).card := by rw [Finset.card_insert_of_notMem ha]; ring

/-- Adding a whole block `E` of sites multiplies the bond dimension by at most
`q ^ |E|`. -/
theorem rank_union_le (S E : Finset (Fin n)) :
    D.rank (S ∪ E) ≤ q ^ E.card * D.rank S := by
  classical
  induction E using Finset.induction with
  | empty => simp
  | insert a E ha ih =>
      have h1 : S ∪ insert a E = insert a (S ∪ E) := by
        ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      rw [h1]
      calc D.rank (insert a (S ∪ E)) ≤ q * D.rank (S ∪ E) := D.rank_insert_le _ _
        _ ≤ q * (q ^ E.card * D.rank S) := Nat.mul_le_mul_left _ ih
        _ = q ^ (insert a E).card * D.rank S := by
            rw [Finset.card_insert_of_notMem ha]; ring

/-- **Cut monotonicity with a rate.**  Between nested cuts the bond dimension
grows by at most one factor of `q` per extra site. -/
theorem rank_le_mul_of_subset {S T : Finset (Fin n)} (h : S ⊆ T) :
    D.rank T ≤ q ^ (T.card - S.card) * D.rank S := by
  classical
  have hu : S ∪ (T \ S) = T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hx | ⟨hx, -⟩)
      · exact h hx
      · exact hx
    · intro hx
      by_cases hs : x ∈ S
      · exact Or.inl hs
      · exact Or.inr ⟨hx, hs⟩
  have hcard : (T \ S).card = T.card - S.card := Finset.card_sdiff_of_subset h
  have := D.rank_union_le S (T \ S)
  rwa [hu, hcard] at this

/-- **The cut-wise Singleton inequality.**  For `d`-resolving cut data, every cut
`S` of size at most `k = n + 1 - d` obeys
`total ≤ q ^ (k - |S|) * rank S`. -/
theorem cutwise_singleton {d : ℕ} (hres : D.Resolving d) (hd : 1 ≤ d)
    {S : Finset (Fin n)} (hS : S.card ≤ sdim n d) :
    D.total ≤ q ^ (sdim n d - S.card) * D.rank S := by
  classical
  obtain ⟨T, hST, hT⟩ := Finset.exists_superset_card_eq (s := S) hS (by simp [sdim]; omega)
  have h1 : D.rank T = D.total := by
    refine hres T ?_
    rw [hT]
    simp only [sdim]
    omega
  have h2 := D.rank_le_mul_of_subset hST
  rw [h1, hT] at h2
  exact h2

/-- **The Singleton bound**, the shadow of the cut-wise inequality at the empty
cut. -/
theorem singleton_bound {d : ℕ} (hres : D.Resolving d) (hd : 1 ≤ d) :
    D.total ≤ q ^ sdim n d := by
  have h := D.cutwise_singleton hres hd (S := (∅ : Finset (Fin n))) (by simp)
  simp only [Finset.card_empty, Nat.sub_zero] at h
  calc D.total ≤ q ^ sdim n d * D.rank ∅ := h
    _ ≤ q ^ sdim n d * 1 := Nat.mul_le_mul_left _ D.rank_empty_le
    _ = q ^ sdim n d := by ring

/-- The **cut-indexed defect** of a `d`-resolving cut datum: the slack in the
cut-wise Singleton inequality at the cut `S`. -/
-- [dropped: platform already declares cutDefect]
theorem cutDefect_eq_zero_iff {d : ℕ} (hres : D.Resolving d) (hd : 1 ≤ d)
    {S : Finset (Fin n)} (hS : S.card ≤ sdim n d) :
    D.cutDefect d S = 0 ↔ q ^ (sdim n d - S.card) * D.rank S = D.total := by
  have h := D.cutwise_singleton hres hd hS
  constructor
  · intro h0
    have : q ^ (sdim n d - S.card) * D.rank S ≤ D.total := by
      simpa [cutDefect] using Nat.sub_eq_zero_iff_le.mp h0
    omega
  · intro h0
    simp [cutDefect, h0]

/-- **Rigidity of saturated (MDS) cut data.**  If the global Singleton bound is
saturated, `total = q ^ k`, then every cut of size at most `k` is *maximally*
entangled: `rank S = q ^ |S|`, and hence every cut-indexed defect vanishes. -/
theorem rank_eq_pow_of_saturated {d : ℕ} (hres : D.Resolving d) (hd : 1 ≤ d)
    (hq : 0 < q) (hsat : D.total = q ^ sdim n d)
    {S : Finset (Fin n)} (hS : S.card ≤ sdim n d) :
    D.rank S = q ^ S.card := by
  have h := D.cutwise_singleton hres hd hS
  rw [hsat] at h
  have hsplit : q ^ sdim n d = q ^ (sdim n d - S.card) * q ^ S.card := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at h
  have hpos : 0 < q ^ (sdim n d - S.card) := Nat.pow_pos hq
  exact le_antisymm (D.rank_le_pow S) (Nat.le_of_mul_le_mul_left h hpos)

/-- Saturated cut data have vanishing defect at every cut below the plateau. -/
theorem cutDefect_eq_zero_of_saturated {d : ℕ} (hres : D.Resolving d) (hd : 1 ≤ d)
    (hq : 0 < q) (hsat : D.total = q ^ sdim n d)
    {S : Finset (Fin n)} (hS : S.card ≤ sdim n d) :
    D.cutDefect d S = 0 := by
  refine (D.cutDefect_eq_zero_iff hres hd hS).mpr ?_
  rw [D.rank_eq_pow_of_saturated hres hd hq hsat hS, ← pow_add, hsat]
  congr 1
  omega

end CutData

/-! ## Codes as cut data -/

-- [dropped: platform already declares proj]
-- [dropped: platform already declares cutRank]
-- [dropped: platform already declares MinDist]
-- [dropped: platform already declares cutRank_empty_le]
-- [dropped: platform already declares cutRank_mono]
-- [dropped: platform already declares cutRank_insert_le]
lemma hammingDist_le_of_proj_eq {x y : Word n q} {S : Finset (Fin n)}
    (h : proj S x = proj S y) : hammingDist x y ≤ n - S.card := by
  classical
  have hsub : ({i | x i ≠ y i} : Finset (Fin n)) ⊆ Sᶜ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at *
    intro hiS
    exact hi (congrFun h ⟨i, hiS⟩)
  have := Finset.card_le_card hsub
  simpa [hammingDist, Finset.card_compl] using this

/-- **Distance resolves cuts.**  A code of minimum distance `d` is determined by
any set of `n - d + 1` sites. -/
lemma cutRank_eq_card_of_minDist {C : Finset (Word n q)} {d : ℕ} {S : Finset (Fin n)}
    (hd : MinDist C d) (h : n - S.card < d) : cutRank C S = C.card := by
  classical
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  by_contra hne
  have h1 := hd x hx y hy hne
  have h2 := hammingDist_le_of_proj_eq hxy
  omega

/-- The cut data of a finite codebook. -/
-- [dropped: platform already declares codeCutData]
@[simp] lemma codeCutData_rank (C : Finset (Word n q)) (S : Finset (Fin n)) :
    (codeCutData C).rank S = cutRank C S := rfl

@[simp] lemma codeCutData_total (C : Finset (Word n q)) : (codeCutData C).total = C.card := rfl

/-- Minimum distance `d` makes the cut data of a code `d`-resolving. -/
lemma resolving_codeCutData {C : Finset (Word n q)} {d : ℕ} (hd : MinDist C d) :
    (codeCutData C).Resolving d := fun _ h => cutRank_eq_card_of_minDist hd h

/-- **Cut-wise Singleton inequality for codes.** -/
theorem cutwise_singleton_code {C : Finset (Word n q)} {d : ℕ} (hd : MinDist C d) (hd1 : 1 ≤ d)
    {S : Finset (Fin n)} (hS : S.card ≤ CutData.sdim n d) :
    C.card ≤ q ^ (CutData.sdim n d - S.card) * cutRank C S :=
  (codeCutData C).cutwise_singleton (resolving_codeCutData hd) hd1 hS

/-- **The Singleton bound** `|C| ≤ q ^ (n + 1 - d)`. -/
theorem singleton_bound_of_minDist {C : Finset (Word n q)} {d : ℕ} (hd : MinDist C d)
    (hd1 : 1 ≤ d) : C.card ≤ q ^ CutData.sdim n d :=
  (codeCutData C).singleton_bound (resolving_codeCutData hd) hd1

/-- A codebook is **MDS** when it meets the Singleton bound with equality. -/
-- [dropped: platform already declares IsMDS]
theorem cutRank_eq_pow_of_isMDS {C : Finset (Word n q)} {d : ℕ} (hmds : IsMDS C d)
    (hd1 : 1 ≤ d) (hq : 0 < q) {S : Finset (Fin n)} (hS : S.card ≤ CutData.sdim n d) :
    cutRank C S = q ^ S.card :=
  (codeCutData C).rank_eq_pow_of_saturated (resolving_codeCutData hmds.1) hd1 hq hmds.2 hS

/-! ### Fibres -/

/-- The fibre of the codebook over a pattern on a cut. -/
-- [dropped: platform already declares fiber]
lemma minDist_fiber {C : Finset (Word n q)} {d : ℕ} (hd : MinDist C d) (S : Finset (Fin n))
    (y : {i // i ∈ S} → Fin q) : MinDist (fiber C S y) d := by
  intro x hx z hz hxz
  exact hd x (Finset.mem_of_mem_filter _ hx) z (Finset.mem_of_mem_filter _ hz) hxz

lemma cutRank_fiber_le_one {C : Finset (Word n q)} (S : Finset (Fin n))
    (y : {i // i ∈ S} → Fin q) : cutRank (fiber C S y) S ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
  rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hz).2]

/-- **Fibres of a distance-`d` code are small.**  Over any cut of size at most
`k`, each pattern has at most `q ^ (k - |S|)` codewords above it. -/
theorem fiber_card_le {C : Finset (Word n q)} {d : ℕ} (hd : MinDist C d) (hd1 : 1 ≤ d)
    {S : Finset (Fin n)} (hS : S.card ≤ CutData.sdim n d) (y : {i // i ∈ S} → Fin q) :
    (fiber C S y).card ≤ q ^ (CutData.sdim n d - S.card) := by
  have h := cutwise_singleton_code (minDist_fiber hd S y) hd1 hS
  calc (fiber C S y).card ≤ q ^ (CutData.sdim n d - S.card) * cutRank (fiber C S y) S := h
    _ ≤ q ^ (CutData.sdim n d - S.card) * 1 :=
        Nat.mul_le_mul_left _ (cutRank_fiber_le_one S y)
    _ = q ^ (CutData.sdim n d - S.card) := by ring

lemma sum_fiber_card (C : Finset (Word n q)) (S : Finset (Fin n)) :
    ∑ y : {i // i ∈ S} → Fin q, (fiber C S y).card = C.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (f := proj S) (t := (Finset.univ : Finset ({i // i ∈ S} → Fin q)))
    (fun x _ => Finset.mem_univ _)).symm

/-- **Balanced fibres of an MDS code.**  Over any cut of size at most `k`, every
pattern has *exactly* `q ^ (k - |S|)` codewords above it: the projection of an
MDS code is a uniform covering map. -/
theorem fiber_card_of_isMDS {C : Finset (Word n q)} {d : ℕ} (hmds : IsMDS C d) (hd1 : 1 ≤ d)
    {S : Finset (Fin n)} (hS : S.card ≤ CutData.sdim n d)
    (y : {i // i ∈ S} → Fin q) :
    (fiber C S y).card = q ^ (CutData.sdim n d - S.card) := by
  classical
  set k := CutData.sdim n d with hk
  set M := q ^ (k - S.card) with hM
  by_contra hne
  have hlt : (fiber C S y).card < M := lt_of_le_of_ne (fiber_card_le hmds.1 hd1 hS y) hne
  have hall : ∀ z : {i // i ∈ S} → Fin q, (fiber C S z).card ≤ M := fun z =>
    fiber_card_le hmds.1 hd1 hS z
  have hsum : ∑ z : {i // i ∈ S} → Fin q, (fiber C S z).card
      < ∑ _z : {i // i ∈ S} → Fin q, M := by
    refine Finset.sum_lt_sum (fun z _ => hall z) ⟨y, Finset.mem_univ y, hlt⟩
  rw [sum_fiber_card, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
    Fintype.card_fin, smul_eq_mul, hmds.2] at hsum
  have hpow : q ^ S.card * M = q ^ k := by
    rw [hM, ← pow_add]
    congr 1
    omega
  rw [hpow] at hsum
  exact absurd hsum (lt_irrefl _)

end CutIndexedSingleton
section
open Finset
open CutIndexedSingleton
open CutData
variable {n q : ℕ}
variable (D : CutData n q)

theorem solution {C : Finset (Word n q)} {d : ℕ} (hd : MinDist C d)
    (hd1 : 1 ≤ d) :
    C.card ≤ q ^ CutData.sdim n d := by
  first
  | exact CutIndexedSingleton.singleton_bound_of_minDist hd hd1
  | exact CutIndexedSingleton.singleton_bound_of_minDist
  | exact @CutIndexedSingleton.singleton_bound_of_minDist C d hd hd1
  | apply CutIndexedSingleton.singleton_bound_of_minDist
  | exact CutIndexedSingleton.singleton_bound_of_minDist ..


end
