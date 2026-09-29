-- Prove2me | Definitions.Def_Geometry_MagnitudeTopeGraphsDiagonal
-- name    : Geometry_MagnitudeTopeGraphsDiagonal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:42:15.473038+00:00
-- url     : https://prove2.me/theorems/95f31b83-8d46-45d8-afa2-52996a4d43fb
-- title:
--   Aether Catalog definitions — Geometry_MagnitudeTopeGraphsDiagonal
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.MagnitudeTopeGraphsDiagonal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/MagnitudeTopeGraphsDiagonal.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_MagnitudeTopeGraphs
/-
# The diagonal part `MH_{2,2}` of the magnitude homology of tope graphs

This file continues `Geometry/MagnitudeTopeGraphs.lean`, where the magnitude chain
generators `Gen1`, `Gen2`, the differential `δ₂`, the tope graph of the coordinate
arrangement in `ℝⁿ` and its Cayley-graph model were introduced, and where the group of
`(2,2)`-cycles was identified up to a splitting.  Here we finish that computation:

7. **Degree-3 chains.** `Gen3 G ℓ` is empty for `ℓ < 3`; consequently *any* differential
   `δ₃` into the `(2,2)`-cycles is zero, and therefore
   `MH_{2,2}(G) = ker δ₂` (`MH22_equiv_cycles`).

8. **The rank of the cycles.** For a connected graph with finitely many chains,
   `rk (ker δ₂) + #Gen1 = #Gen2` in every length `ℓ ≥ 2`
   (`finrank_ker_delta2_add`), because `δ₂` is surjective onto a free module.

9. **The bidegree `(2,2)` magnitude homology of the tope graph.** Combining 8 with the
   counts `#Gen1 = 2ⁿ·C(n,2)` and `#Gen2 = 2ⁿ·n²` and the identity
   `C(n,2) + C(n+1,2) = n²`, we get
   `MH_{2,2}(topeGraph n) ≅ ℤ^{2ⁿ·C(n+1,2)}`,
   i.e. the rank is `2ⁿ` times `C(n+1,2)`, the value at degree `2` of the Hilbert
   function of the polynomial ring in `n` variables — the Stanley–Reisner ring of the
   simplex attached to each tope of the Boolean arrangement.

10. **Transport to the Coxeter Cayley graph.** Magnitude chains in degree 2 and the
    differential `δ₂` are natural under graph isomorphisms, so the same computation holds
    for the Cayley graph of the Coxeter group `(ℤ/2)ⁿ`.

Everything is self-contained: only `Mathlib` and the companion file are imported.
-/


namespace MagnitudeTope

open scoped Classical

/-! ## 7. Degree-3 chains vanish in length 2, so `MH_{2,2} = ker δ₂` -/

section Degree3

variable {V : Type*} {G : SimpleGraph V}

/-- Generators of the magnitude chain group `MC_{3,ℓ}(G)`: quadruples of vertices with
consecutive entries distinct and total length `ℓ`. -/
def Gen3 (G : SimpleGraph V) (ℓ : ℕ) : Type _ :=
  {p : V × V × V × V // p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2.1 ∧ p.2.2.1 ≠ p.2.2.2 ∧
      G.dist p.1 p.2.1 + G.dist p.2.1 p.2.2.1 + G.dist p.2.2.1 p.2.2.2 = ℓ}




end Degree3

/-! ### Finiteness of the chain groups of a finite graph -/

section Finiteness

variable {V : Type*} [Finite V] (G : SimpleGraph V) (ℓ : ℕ)

instance instFiniteGen1 : Finite (Gen1 G ℓ) := Subtype.finite

instance instFiniteGen2 : Finite (Gen2 G ℓ) := Subtype.finite

instance instFiniteGen3 : Finite (Gen3 G ℓ) := Subtype.finite

end Finiteness

/-! ## 8. The rank of the `(2,ℓ)`-cycles of a finite graph -/

section Rank

variable {V : Type*} {G : SimpleGraph V}



end Rank

/-! ## 9. `MH_{2,2}` of the tope graph -/

section TopeDiagonal

variable {n : ℕ}




end TopeDiagonal

/-! ## 10. Transport along graph isomorphisms, and the Coxeter Cayley graph -/

section Transport

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Degree-2 magnitude chain generators are transported along a graph isomorphism. -/
def genEquiv2 (e : G ≃g H) (ℓ : ℕ) : Gen2 G ℓ ≃ Gen2 H ℓ where
  toFun g := ⟨(e g.1.1, e g.1.2.1, e g.1.2.2), by
      simpa using (e.toEquiv.injective.ne_iff).mpr g.2.1, by
      simpa using (e.toEquiv.injective.ne_iff).mpr g.2.2.1, by
      rw [iso_dist_eq, iso_dist_eq]; exact g.2.2.2⟩
  invFun g := ⟨(e.symm g.1.1, e.symm g.1.2.1, e.symm g.1.2.2), by
      simpa using (e.symm.toEquiv.injective.ne_iff).mpr g.2.1, by
      simpa using (e.symm.toEquiv.injective.ne_iff).mpr g.2.2.1, by
      rw [iso_dist_eq, iso_dist_eq]; exact g.2.2.2⟩
  left_inv g := by apply Subtype.ext; simp
  right_inv g := by apply Subtype.ext; simp





end Transport

end MagnitudeTope


