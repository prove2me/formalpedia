-- Prove2me | solution 1 for MarkovMixing.stationary_unique
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:16:51.738852+00:00
-- url     : https://prove2.me/submissions/f4f75bf4-361e-4f12-b572-fafa61e84e6e

import Theorems.Thm_MarkovMixing_harmonic_eq_const
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π π' : V → ℝ) (hπ : IsStationary P π) (hπ' : IsStationary P π') :
    π = π' := by
  rcases isEmpty_or_nonempty V with hV | hV
  · funext x; exact (IsEmpty.false x).elim
  classical
  set W : Matrix V V ℝ := P - 1 with hWdef
  set e : V → ℝ := fun _ => (1 : ℝ) with hedef
  have hene : e ≠ 0 := by
    intro hc
    have h0 := congrFun hc (Classical.arbitrary V)
    simp [hedef] at h0
  have hmem_iff : ∀ h : V → ℝ, h ∈ LinearMap.ker W.mulVecLin ↔ Harmonic P h := by
    intro h
    constructor
    · intro hh
      have hh' : W *ᵥ h = 0 := hh
      intro x
      have hx := congrFun hh' x
      simp only [hWdef, Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, Pi.zero_apply,
        sub_eq_zero] at hx
      exact hx.symm
    · intro hh
      have hz : W *ᵥ h = 0 := by
        funext x
        simp only [hWdef, Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, Pi.zero_apply,
          sub_eq_zero]
        exact (hh x).symm
      exact hz
  have hker_right : LinearMap.ker W.mulVecLin = Submodule.span ℝ {e} := by
    apply le_antisymm
    · intro h hh
      have hconst := (hmem_iff h).mp hh
      have hall : ∀ z : V, h z = h (Classical.arbitrary V) := fun z =>
        MarkovMixing.harmonic_eq_const P hP hirr h hconst z (Classical.arbitrary V)
      have hrep : h = h (Classical.arbitrary V) • e := by
        funext z; simp [hedef, hall z]
      rw [hrep]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine (hmem_iff e).mpr ?_
      intro x
      simp [hedef, hP.2 x]
  have hfr1 : Module.finrank ℝ (LinearMap.ker W.mulVecLin) = 1 := by
    rw [hker_right]
    exact finrank_span_singleton hene
  have hcard : Module.finrank ℝ (V → ℝ) = Fintype.card V :=
    Module.finrank_fintype_fun_eq_card ℝ
  have hrn : ∀ A : Matrix V V ℝ,
      A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = Fintype.card V := by
    intro A
    have hh := LinearMap.finrank_range_add_finrank_ker (K := ℝ) A.mulVecLin
    rw [hcard] at hh
    exact hh
  have hrt : Wᵀ.rank = W.rank := Matrix.rank_transpose W
  have hfr2 : Module.finrank ℝ (LinearMap.ker Wᵀ.mulVecLin) = 1 := by
    have h1 := hrn W
    have h2 := hrn Wᵀ
    rw [hrt] at h2
    omega
  have hleft : ∀ ρ : V → ℝ, IsStationary P ρ → ρ ∈ LinearMap.ker Wᵀ.mulVecLin := by
    intro ρ hρ
    have hz : Wᵀ *ᵥ ρ = 0 := by
      rw [Matrix.mulVec_transpose, hWdef, Matrix.vecMul_sub, Matrix.vecMul_one, hρ.2, sub_self]
    exact hz
  have hπmem := hleft π hπ
  have hπ'mem := hleft π' hπ'
  have hπne : π ≠ 0 := by
    intro hc
    have hs := hπ.1.2
    rw [hc] at hs
    simp at hs
  have hvne : (⟨π, hπmem⟩ : LinearMap.ker Wᵀ.mulVecLin) ≠ 0 := by
    intro hc
    exact hπne (congrArg Subtype.val hc)
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (K := ℝ) ⟨π, hπmem⟩ hvne).mp hfr2 ⟨π', hπ'mem⟩
  have hcv : c • π = π' := congrArg Subtype.val hc
  have hsum : c * (∑ x, π x) = ∑ x, π' x := by
    rw [← hcv, Finset.mul_sum]
    rfl
  rw [hπ.1.2, hπ'.1.2, mul_one] at hsum
  rw [← hcv, hsum, one_smul]
