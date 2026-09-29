-- Prove2me | solution 1 for MagnitudeTope.card_pair_with_empty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:27:19.593108+00:00
-- url     : https://prove2.me/submissions/2ccac056-d3a5-45e3-8c6d-b21eb6570974

-- Sol generated from Geometry/MagnitudeTopeGraphsHilbert.lean
import Mathlib
import Definitions.Def_Geometry_MagnitudeTopeGraphs
import Definitions.Def_Geometry_MagnitudeTopeGraphsDiagonal
import Definitions.Def_Geometry_MagnitudeTopeGraphsHilbert
/-
# Magnitude chains of tope graphs in arbitrary length, and their Vandermonde counts

This file continues `Geometry/MagnitudeTopeGraphs.lean` and
`Geometry/MagnitudeTopeGraphsDiagonal.lean`.  There the magnitude chain generators
`Gen1`, `Gen2`, the differential `δ₂`, the tope graph of the coordinate arrangement in
`ℝⁿ` and its Coxeter Cayley-graph model were introduced, and the bidegree `(2,2)` part of
the magnitude homology was computed.  Here we extend the count of the degree-2 chain
groups and of the cycle groups to *all* lengths `ℓ`, and record the general
finite-graph form of the `(2,2)` computation.

11. **The `(2,2)` computation for an arbitrary finite connected graph.**
    `MH_{2,2}(G) = ker δ₂` is free abelian of rank `#MC_{2,2}(G) - #MC_{1,2}(G)`
    (`finrank_ker_delta2_two`, `MH22_free_of_finite`).

12. **Degree-2 chains of the tope graph in arbitrary length.** A `(2,ℓ)`-chain of the
    tope graph is a tope `y` together with an *ordered pair of nonempty sets of
    hyperplanes* `(a,b)` with `|a| + |b| = ℓ` (`topeGen2EquivGeneral`).

13. **Counting them.** Pairs of subsets of an `n`-set with total size `ℓ` biject with
    `ℓ`-subsets of a `2n`-set, so there are `C(2n,ℓ)` of them (`card_pair_card_sum`);
    discarding the `2·C(n,ℓ)` pairs with an empty member (`card_subsetPair`) gives
    `#MC_{2,ℓ}(topeGraph n) = 2ⁿ · (C(2n,ℓ) - 2·C(n,ℓ))`
    (`card_tope_gen2_general`), which for `ℓ = 2` recovers `2ⁿ·n²`.

14. **The cycle group in arbitrary length.** Since `δ₂` is surjective for `ℓ ≥ 2` and
    `#MC_{1,ℓ} = 2ⁿ·C(n,ℓ)`, the `(2,ℓ)`-cycles of the tope graph form a free abelian
    group of rank `2ⁿ · (C(2n,ℓ) - 3·C(n,ℓ))` (`finrank_tope_cycles_general`,
    `tope_cycles_free_general`); for `ℓ = 2` this is `2ⁿ·C(n+1,2)`, the Hilbert-function
    value obtained before.  Everything transports to the Coxeter Cayley graph of
    `(ℤ/2)ⁿ` (`cayley_cycles_finrank_general`).

Everything is self-contained: only `Mathlib` and the two companion files are imported.
-/


open MagnitudeTope

open Finset

open scoped Classical

/-! ## 11. The `(2,2)` computation for an arbitrary finite connected graph -/


variable {V : Type*} [Finite V] {G : SimpleGraph V}




/-! ## 12. Degree-2 chains of the tope graph in arbitrary length -/


variable {n : ℕ}












/-! ## 14. The cycle group of the tope graph in arbitrary length -/


variable {n : ℕ}







open MagnitudeTope in
theorem solution(n ℓ : ℕ) (hl : 1 ≤ ℓ) :
    ((univ.filter (fun p : Finset (Fin n) × Finset (Fin n) => p.1.card + p.2.card = ℓ)).filter
      (fun p => ¬(p.1.Nonempty ∧ p.2.Nonempty))).card = 2 * n.choose ℓ := by
  classical
  have h : ((univ.filter
        (fun p : Finset (Fin n) × Finset (Fin n) => p.1.card + p.2.card = ℓ)).filter
      (fun p => ¬(p.1.Nonempty ∧ p.2.Nonempty)))
      = ((univ : Finset (Fin n)).powersetCard ℓ).image (fun b => ((∅ : Finset (Fin n)), b)) ∪
        ((univ : Finset (Fin n)).powersetCard ℓ).image (fun a => (a, (∅ : Finset (Fin n)))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_powersetCard, Finset.subset_univ,
      Finset.not_nonempty_iff_eq_empty, not_and_or, Prod.mk.injEq]
    constructor
    · rintro ⟨hcard, rfl | rfl⟩
      · exact Or.inl ⟨b, by simpa using hcard, rfl, rfl⟩
      · exact Or.inr ⟨a, by simpa using hcard, rfl, rfl⟩
    · rintro (⟨c, hc, rfl, rfl⟩ | ⟨c, hc, rfl, rfl⟩) <;> simp [hc]
  have hdisj : Disjoint
      (((univ : Finset (Fin n)).powersetCard ℓ).image (fun b => ((∅ : Finset (Fin n)), b)))
      (((univ : Finset (Fin n)).powersetCard ℓ).image (fun a => (a, (∅ : Finset (Fin n))))) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_image, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Prod.mk.injEq] at h1 h2
    obtain ⟨c, hc, rfl, rfl⟩ := h1
    obtain ⟨d, hd, hd1, hd2⟩ := h2
    subst hd1
    simp at hd
    omega
  rw [h, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (by intro x y hxy; simpa using hxy),
    Finset.card_image_of_injective _ (by intro x y hxy; simpa using hxy),
    Finset.card_powersetCard]
  simp [two_mul]
