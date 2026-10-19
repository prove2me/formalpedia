-- Prove2me | solution 1 for PalisConjecture.identity_not_finitely_many_attractors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:10:52.868977+00:00
-- url     : https://prove2.me/submissions/70040e2d-6f67-4a06-b37b-96e2cb2100aa

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor

open Filter

namespace PalisID

lemma omega_id {M : Type*} [TopologicalSpace M] [T2Space M] (p : M) :
    PalisConjecture.omegaLimitMap (id : M → M) p = {p} := by
  unfold PalisConjecture.omegaLimitMap
  have himg : ∀ u : Set ℕ, u.Nonempty → Set.image2 (fun (k : ℕ) (x : M) => (id : M → M)^[k] x) u {p} = {p} := by
    intro u hu
    ext y
    simp only [Set.mem_image2, Set.mem_singleton_iff, Function.iterate_id, id_eq]
    constructor
    · rintro ⟨k, _, x, rfl, rfl⟩; rfl
    · intro hy; obtain ⟨k, hk⟩ := hu; exact ⟨k, hk, p, rfl, hy.symm⟩
  rw [omegaLimit_def]
  apply Set.Subset.antisymm
  · intro y hy
    have := Set.mem_iInter₂.1 hy Set.univ univ_mem
    rw [himg _ Set.univ_nonempty, closure_singleton] at this
    exact this
  · intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    refine Set.mem_iInter₂.2 (fun u hu => ?_)
    rw [himg u (Filter.nonempty_of_mem hu), closure_singleton]
    rfl

lemma basin_id {M : Type*} [TopologicalSpace M] [T2Space M] (Λ : Set M) :
    PalisConjecture.basin (id : M → M) Λ = Λ := by
  ext p
  simp [PalisConjecture.basin, omega_id]

lemma attractor_singleton {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (Λ : Set M)
    (h : PalisConjecture.IsAttractor n (id : M → M) Λ) : ∃ x, Λ = {x} := by
  obtain ⟨_, ⟨x, _, hx⟩, _⟩ := h
  refine ⟨x, ?_⟩
  rw [← hx]
  have : {y | ∃ k : ℕ, (id : M → M)^[k] x = y} = {x} := by
    ext y; simp [eq_comm]
  rw [this, closure_singleton]

end PalisID

open PalisID in
theorem solution (n : ℕ) (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ¬ PalisConjecture.HasFiniteAttractorsCoveringAE n (id : M → M) := by
  rintro ⟨A, hA, hnull⟩
  have hfin : (⋃ Λ ∈ A, PalisConjecture.basin (id : M → M) Λ).Finite := by
    refine Set.Finite.biUnion A.finite_toSet (fun Λ hΛ => ?_)
    rw [basin_id]
    obtain ⟨x, rfl⟩ := attractor_singleton n Λ (hA Λ hΛ)
    exact Set.finite_singleton x
  set F := ⋃ Λ ∈ A, PalisConjecture.basin (id : M → M) Λ with hF
  obtain ⟨p⟩ := ‹Nonempty M›
  set e := chartAt (EuclideanSpace ℝ (Fin n)) p
  have he := hnull e (chart_mem_atlas _ p)
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp; omega
    exact Module.nontrivial_of_finrank_pos this
  have htarget : e.target ⊆ e '' (Fᶜ ∩ e.source) ∪ e '' F := by
    intro y hy
    have hs := e.map_target hy
    by_cases hyF : e.symm y ∈ F
    · right; exact ⟨e.symm y, hyF, e.right_inv hy⟩
    · left; exact ⟨e.symm y, ⟨hyF, hs⟩, e.right_inv hy⟩
  have hpos : 0 < MeasureTheory.volume e.target :=
    e.open_target.measure_pos _ ⟨e p, e.map_source (mem_chart_source _ p)⟩
  have hzero : MeasureTheory.volume (e '' F) = 0 := (hfin.image _).measure_zero _
  have := MeasureTheory.measure_mono (μ := MeasureTheory.volume) htarget
  have h2 := MeasureTheory.measure_union_le (μ := MeasureTheory.volume) (e '' (Fᶜ ∩ e.source)) (e '' F)
  rw [he, hzero, add_zero] at h2
  exact absurd (lt_of_lt_of_le hpos (this.trans h2)) (lt_irrefl _)
