-- Prove2me | Theorems.Thm_MagnitudeTope_ker_delta2_equiv
-- name    : MagnitudeTope.ker_delta2_equiv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:33:16.40746+00:00
-- url     : https://prove2.me/theorems/145bab29-5921-48b1-8c03-4a3c3283a79d
-- title:
--   The `(2,ℓ)`-cycles are isomorphic along a graph isomorphism.
-- statement:
--   The `(2,ℓ)`-cycles are isomorphic along a graph isomorphism.
--
--   ```lean
--   theorem MagnitudeTope.ker_delta2_equiv(e : G ≃g H) (hG : G.Connected) (hH : H.Connected) (ℓ : ℕ) :
--       Nonempty (LinearMap.ker (delta2 hG ℓ) ≃ₗ[ℤ] LinearMap.ker (delta2 hH ℓ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/MagnitudeTopeGraphsDiagonal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/MagnitudeTopeGraphsDiagonal.lean#L199

-- Thm stub generated from Geometry/MagnitudeTopeGraphsDiagonal.lean
import Mathlib
import Definitions.Def_Geometry_MagnitudeTopeGraphs
import Definitions.Def_Geometry_MagnitudeTopeGraphsDiagonal
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


open MagnitudeTope

open scoped Classical

/-! ## 7. Degree-3 chains vanish in length 2, so `MH_{2,2} = ker δ₂` -/


variable {V : Type*} {G : SimpleGraph V}






/-! ### Finiteness of the chain groups of a finite graph -/


variable {V : Type*} [Finite V] (G : SimpleGraph V) (ℓ : ℕ)





/-! ## 8. The rank of the `(2,ℓ)`-cycles of a finite graph -/


variable {V : Type*} {G : SimpleGraph V}




/-! ## 9. `MH_{2,2}` of the tope graph -/


variable {n : ℕ}





/-! ## 10. Transport along graph isomorphisms, and the Coxeter Cayley graph -/


variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem MagnitudeTope.ker_delta2_equiv(e : G ≃g H) (hG : G.Connected) (hH : H.Connected) (ℓ : ℕ) :
    Nonempty (LinearMap.ker (delta2 hG ℓ) ≃ₗ[ℤ] LinearMap.ker (delta2 hH ℓ)) := by sorry
