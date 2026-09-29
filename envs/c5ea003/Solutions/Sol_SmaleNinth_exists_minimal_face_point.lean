-- Prove2me | solution 1 for SmaleNinth.exists_minimal_face_point
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T04:55:18.210696+00:00
-- url     : https://prove2.me/submissions/64d564a2-ba5d-49c3-9ed1-51301737a8d3

import Mathlib
import Definitions.Def_Polyhedron

open Matrix LinearOptimization
open scoped Classical

namespace MinFace

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

/-- The constraints that are tight at `x`. -/
noncomputable def tight (x : Fin n → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => A.mulVec x i = b i)

lemma mem_tight {x : Fin n → ℝ} {i : Fin m} :
    i ∈ tight A b x ↔ A.mulVec x i = b i := by
  simp [tight]

/-- On the segment from `x` to `y`, the constraint values interpolate affinely. -/
lemma mulVec_seg (x y : Fin n → ℝ) (t : ℝ) (i : Fin m) :
    A.mulVec (x + t • (y - x)) i =
      A.mulVec x i + t * (A.mulVec y i - A.mulVec x i) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub]
  simp

lemma mem_poly_iff {x : Fin n → ℝ} :
    x ∈ polyhedron A b ↔ ∀ i, b i ≤ A.mulVec x i := by
  simp [polyhedron, Pi.le_def]

end MinFace

open MinFace

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (polyhedron A b).Nonempty) :
    ∃ (x : Fin n → ℝ) (I : Finset (Fin m)),
      x ∈ polyhedron A b ∧
      (∀ i ∈ I, A.mulVec x i = b i) ∧
      (∀ y : Fin n → ℝ, (∀ i ∈ I, A.mulVec y i = b i) → y ∈ polyhedron A b) := by
  classical
  set S : Set ℕ := {k | ∃ x ∈ polyhedron A b, (tight A b x).card = k} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨x0, hx0⟩ := hne
    exact ⟨_, x0, hx0, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨m, ?_⟩
    rintro k ⟨z, -, rfl⟩
    simpa using (tight A b z).card_le_univ
  obtain ⟨x, hxP, hxcard⟩ := Nat.sSup_mem hSne hSbdd
  have hmax : ∀ z ∈ polyhedron A b, (tight A b z).card ≤ sSup S :=
    fun z hz => le_csSup hSbdd ⟨z, hz, rfl⟩
  refine ⟨x, tight A b x, hxP, fun i hi => (mem_tight A b).1 hi, ?_⟩
  intro y hy
  by_contra hyP
  obtain ⟨j, hj⟩ : ∃ j, A.mulVec y j < b j := by
    by_contra hcon
    push Not at hcon
    exact hyP ((mem_poly_iff A b).2 hcon)
  set T : Finset (Fin m) := Finset.univ.filter (fun i => A.mulVec y i < b i)
    with hTdef
  have hTne : T.Nonempty := ⟨j, by simp [hTdef, hj]⟩
  have hxge : ∀ i, b i ≤ A.mulVec x i := (mem_poly_iff A b).1 hxP
  have hxgt : ∀ i ∈ T, b i < A.mulVec x i := by
    intro i hi
    have hyi : A.mulVec y i < b i := by simpa [hTdef] using hi
    rcases lt_or_eq_of_le (hxge i) with h | h
    · exact h
    · exact absurd (hy i ((mem_tight A b).2 h.symm)) (by linarith)
  set r : Fin m → ℝ :=
    fun i => (A.mulVec x i - b i) / (A.mulVec x i - A.mulVec y i) with hrdef
  have hden : ∀ i ∈ T, 0 < A.mulVec x i - A.mulVec y i := by
    intro i hi
    have hyi : A.mulVec y i < b i := by simpa [hTdef] using hi
    have := hxgt i hi
    linarith
  have hr_pos : ∀ i ∈ T, 0 < r i :=
    fun i hi => div_pos (by linarith [hxgt i hi]) (hden i hi)
  have hr_lt : ∀ i ∈ T, r i < 1 := by
    intro i hi
    have hyi : A.mulVec y i < b i := by simpa [hTdef] using hi
    rw [hrdef, div_lt_one (hden i hi)]
    linarith
  have hr_eq :
      ∀ i ∈ T,
        A.mulVec x i + r i * (A.mulVec y i - A.mulVec x i) = b i := by
    intro i hi
    have hd : A.mulVec x i - A.mulVec y i ≠ 0 := (hden i hi).ne'
    have hri :
        r i = (A.mulVec x i - b i) / (A.mulVec x i - A.mulVec y i) := by
      rw [hrdef]
    rw [hri]
    field_simp
    ring
  obtain ⟨istar, histar, hmin⟩ := T.exists_mem_eq_inf' hTne r
  set t : ℝ := r istar with htdef
  have ht0 : 0 < t := hr_pos istar histar
  have ht1 : t < 1 := hr_lt istar histar
  have hle : ∀ i ∈ T, t ≤ r i := by
    intro i hi
    have hh := Finset.inf'_le (s := T) r hi
    rwa [hmin] at hh
  set z : Fin n → ℝ := x + t • (y - x) with hzdef
  have hzval :
      ∀ i,
        A.mulVec z i =
          A.mulVec x i + t * (A.mulVec y i - A.mulVec x i) :=
    fun i => mulVec_seg A x y t i
  have hzP : z ∈ polyhedron A b := by
    refine (mem_poly_iff A b).2 fun i => ?_
    rw [hzval i]
    by_cases hi : i ∈ T
    · have hri := hr_eq i hi
      have hneg : A.mulVec y i - A.mulVec x i < 0 := by
        linarith [hden i hi]
      nlinarith [hle i hi]
    · have hyi : b i ≤ A.mulVec y i := by
        by_contra hc
        exact hi (by simp [hTdef]; linarith [not_le.1 hc])
      nlinarith [hxge i, ht0.le, ht1.le]
  have hsub : tight A b x ⊆ tight A b z := by
    intro i hi
    have hxi : A.mulVec x i = b i := (mem_tight A b).1 hi
    have hyi : A.mulVec y i = b i := hy i hi
    exact (mem_tight A b).2 (by rw [hzval i, hxi, hyi]; ring)
  have hnew : istar ∈ tight A b z :=
    (mem_tight A b).2 (by rw [hzval istar]; exact hr_eq istar histar)
  have hnotold : istar ∉ tight A b x := by
    intro hc
    have : A.mulVec y istar = b istar := hy istar hc
    have hyi : A.mulVec y istar < b istar := by simpa [hTdef] using histar
    linarith
  have hlt : (tight A b x).card < (tight A b z).card :=
    Finset.card_lt_card ⟨hsub, fun hc => hnotold (hc hnew)⟩
  have := hmax z hzP
  omega
