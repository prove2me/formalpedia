-- Prove2me | Definitions.Def_Geometry_MagnitudeTopeGraphsHilbert
-- name    : Geometry_MagnitudeTopeGraphsHilbert
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:03.975832+00:00
-- url     : https://prove2.me/theorems/72e32e49-653a-4a2b-a53c-231fdaf298ca
-- title:
--   Aether Catalog definitions — Geometry_MagnitudeTopeGraphsHilbert
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.MagnitudeTopeGraphsHilbert`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/MagnitudeTopeGraphsHilbert.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_MagnitudeTopeGraphs
import Definitions.Def_Geometry_MagnitudeTopeGraphsDiagonal
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


namespace MagnitudeTope

open Finset

open scoped Classical

/-! ## 11. The `(2,2)` computation for an arbitrary finite connected graph -/

section GeneralFinite

variable {V : Type*} [Finite V] {G : SimpleGraph V}



end GeneralFinite

/-! ## 12. Degree-2 chains of the tope graph in arbitrary length -/

section TopeChains

variable {n : ℕ}

/-- A symmetric difference equals its left argument exactly when the right one is empty. -/
lemma symmDiff_eq_left_iff {α : Type*} [DecidableEq α] (s t : Finset α) :
    symmDiff s t = s ↔ t = ∅ := by
  constructor
  · intro h
    have := congrArg (fun u => symmDiff s u) h
    simpa [symmDiff_symmDiff_cancel_left] using this
  · rintro rfl; simp

/-- Ordered pairs of *nonempty* sets of hyperplanes with total size `ℓ`. -/
def SubsetPair (n ℓ : ℕ) : Type :=
  {p : Finset (Fin n) × Finset (Fin n) //
    p.1.Nonempty ∧ p.2.Nonempty ∧ p.1.card + p.2.card = ℓ}

instance (n ℓ : ℕ) : Finite (SubsetPair n ℓ) := Subtype.finite

/-- **Degree-2 magnitude chains of the tope graph in length `ℓ`** are triples: a tope `y`
together with the nonempty sets `a = x Δ y` and `b = y Δ z` of hyperplanes separating it
from the two other topes, of total size `ℓ`. -/
def topeGen2EquivGeneral (n ℓ : ℕ) :
    Gen2 (topeGraph n) ℓ ≃ Finset (Fin n) × SubsetPair n ℓ where
  toFun g := (g.1.2.1, ⟨(symmDiff g.1.1 g.1.2.1, symmDiff g.1.2.1 g.1.2.2), by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact g.2.1 (by simpa [symmDiff_eq_bot] using h), by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact g.2.2.1 (by simpa [symmDiff_eq_bot] using h), by
      rw [← topeGraph_dist, ← topeGraph_dist]; exact g.2.2.2⟩)
  invFun p := ⟨(symmDiff p.1 p.2.1.1, p.1, symmDiff p.1 p.2.1.2), by
      intro h
      exact (Finset.nonempty_iff_ne_empty.mp p.2.2.1) ((symmDiff_eq_left_iff _ _).mp h), by
      intro h
      exact (Finset.nonempty_iff_ne_empty.mp p.2.2.2.1) ((symmDiff_eq_left_iff _ _).mp h.symm),
      by
      rw [topeGraph_dist, topeGraph_dist, symmDiff_comm (symmDiff p.1 p.2.1.1) p.1,
        symmDiff_symmDiff_cancel_left, symmDiff_symmDiff_cancel_left]
      exact p.2.2.2.2⟩
  left_inv g := by
    apply Subtype.ext
    obtain ⟨⟨x, y, z⟩, h1, h2, h3⟩ := g
    simp only [Prod.mk.injEq]
    refine ⟨?_, trivial, ?_⟩
    · rw [symmDiff_comm x y, symmDiff_symmDiff_cancel_left]
    · rw [symmDiff_symmDiff_cancel_left]
  right_inv p := by
    obtain ⟨y, ⟨a, b⟩, hp⟩ := p
    refine Prod.ext rfl (Subtype.ext ?_)
    simp only [Prod.mk.injEq]
    constructor
    · rw [symmDiff_comm (symmDiff y a) y, symmDiff_symmDiff_cancel_left]
    · rw [symmDiff_symmDiff_cancel_left]

/-- A pair of subsets of an `n`-set with total size `ℓ` is the same thing as an
`ℓ`-subset of the disjoint union of two `n`-sets. -/
def pairSumEquiv (n ℓ : ℕ) :
    {p : Finset (Fin n) × Finset (Fin n) // p.1.card + p.2.card = ℓ} ≃
      {S : Finset (Fin n ⊕ Fin n) // S.card = ℓ} where
  toFun p := ⟨p.1.1.disjSum p.1.2, by rw [Finset.card_disjSum]; exact p.2⟩
  invFun S := ⟨(S.1.toLeft, S.1.toRight), by
    rw [Finset.card_toLeft_add_card_toRight]; exact S.2⟩
  left_inv p := by
    apply Subtype.ext
    simp [Finset.toLeft_disjSum, Finset.toRight_disjSum]
  right_inv S := by
    apply Subtype.ext
    simp [Finset.toLeft_disjSum_toRight]






end TopeChains

/-! ## 14. The cycle group of the tope graph in arbitrary length -/

section TopeCycles

variable {n : ℕ}





end TopeCycles

end MagnitudeTope


