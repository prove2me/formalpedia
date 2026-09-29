-- Prove2me | solution 1 for MagnitudeTope.ker_delta2_equiv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:34:40.323125+00:00
-- url     : https://prove2.me/submissions/6a2760f3-3899-4c2f-aac9-0edfbbc65294

-- Sol generated from Geometry/MagnitudeTopeGraphsDiagonal.lean
import Mathlib
import Definitions.Def_Geometry_MagnitudeTopeGraphs
import Definitions.Def_Geometry_MagnitudeTopeGraphsDiagonal
import Theorems.Thm_MagnitudeTope_delta2_naturality
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








open MagnitudeTope in
theorem solution(e : G ≃g H) (hG : G.Connected) (hH : H.Connected) (ℓ : ℕ) :
    Nonempty (LinearMap.ker (delta2 hG ℓ) ≃ₗ[ℤ] LinearMap.ker (delta2 hH ℓ)) := by
  set E1 : (Gen1 G ℓ →₀ ℤ) ≃ₗ[ℤ] (Gen1 H ℓ →₀ ℤ) := Finsupp.domLCongr (genEquiv1 e ℓ) with hE1
  set E2 : (Gen2 G ℓ →₀ ℤ) ≃ₗ[ℤ] (Gen2 H ℓ →₀ ℤ) := Finsupp.domLCongr (genEquiv2 e ℓ) with hE2
  have hnat : ∀ v, E1 (delta2 hG ℓ v) = delta2 hH ℓ (E2 v) := by
    intro v
    have := congrArg (fun (f : (Gen2 G ℓ →₀ ℤ) →ₗ[ℤ] (Gen1 H ℓ →₀ ℤ)) => f v)
      (delta2_naturality e hG hH ℓ)
    simpa [hE1, hE2, Finsupp.domLCongr_apply, Finsupp.lmapDomain_apply,
      Finsupp.equivMapDomain_eq_mapDomain] using this
  have hmap : Submodule.map (E2 : (Gen2 G ℓ →₀ ℤ) →ₗ[ℤ] _) (LinearMap.ker (delta2 hG ℓ))
      = LinearMap.ker (delta2 hH ℓ) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      simp only [LinearMap.mem_ker, LinearEquiv.coe_coe] at hv ⊢
      rw [← hnat v, hv, map_zero]
    · intro hw
      refine ⟨E2.symm w, ?_, by simp⟩
      simp only [LinearMap.mem_ker] at hw ⊢
      apply E1.injective
      rw [hnat, E2.apply_symm_apply, hw, map_zero]
  exact ⟨(E2.submoduleMap (LinearMap.ker (delta2 hG ℓ))).trans (LinearEquiv.ofEq _ _ hmap)⟩
