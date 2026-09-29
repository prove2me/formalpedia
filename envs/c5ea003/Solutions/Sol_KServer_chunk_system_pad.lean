-- Prove2me | solution 1 for KServer.chunk_system_pad
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-04T23:07:41.031359+00:00
-- url     : https://prove2.me/submissions/0bcd0d66-ab9f-480c-8038-623eda89b8fb

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Theorems.Thm_KServer_chunk_system_mapped

namespace Pad

open KServer

variable {X : Type*} [MetricSpace X] [Fintype X] (x₀ : X) (k : ℕ)
  (hcard : Fintype.card X ≤ k + 1)

/-- A bound on all distances of the finite space. -/
noncomputable def rad : ℝ :=
  (Finset.univ.sup' ⟨(x₀, x₀), Finset.mem_univ _⟩ fun p : X × X => dist p.1 p.2) + 1

theorem rad_pos : 0 < rad x₀ := by
  have h : (0 : ℝ) ≤ Finset.univ.sup' ⟨(x₀, x₀), Finset.mem_univ _⟩
      fun p : X × X => dist p.1 p.2 := by
    refine le_trans (le_of_eq (dist_self x₀).symm) ?_
    exact Finset.le_sup' (f := fun p : X × X => dist p.1 p.2) (Finset.mem_univ (x₀, x₀))
  simp only [rad]
  linarith

theorem dist_le_rad (y z : X) : dist y z ≤ rad x₀ := by
  have h : dist y z ≤ Finset.univ.sup' ⟨(x₀, x₀), Finset.mem_univ _⟩
      fun p : X × X => dist p.1 p.2 :=
    Finset.le_sup' (f := fun p : X × X => dist p.1 p.2) (Finset.mem_univ (y, z))
  simp only [rad]
  linarith

/-- The projection of the padded index set onto the original space: the first
`card X` indices enumerate `X`, the remaining ones are sent to `x₀`. -/
noncomputable def proj (i : Fin (k + 1)) : X :=
  if h : (i : ℕ) < Fintype.card X then (Fintype.equivFin X).symm ⟨(i : ℕ), h⟩ else x₀

/-- The section: the copy of `x` inside the padded index set. -/
noncomputable def incl (x : X) : Fin (k + 1) :=
  ⟨((Fintype.equivFin X) x : ℕ), lt_of_lt_of_le (Fintype.equivFin X x).isLt hcard⟩

omit [MetricSpace X] in
theorem proj_incl (x : X) : proj x₀ k (incl k hcard x) = x := by
  simp only [proj, incl]
  simp

omit [MetricSpace X] in
theorem incl_injective : Function.Injective (incl k hcard (X := X)) := by
  intro x y hxy
  have := congrArg Fin.val hxy
  simp only [incl] at this
  have h2 : (Fintype.equivFin X) x = (Fintype.equivFin X) y := Fin.ext this
  exact (Fintype.equivFin X).injective h2

/-- The padded distance. -/
noncomputable def padDist (i j : Fin (k + 1)) : ℝ :=
  if i = j then 0
  else if (i : ℕ) < Fintype.card X ∧ (j : ℕ) < Fintype.card X then
    dist (proj x₀ k i) (proj x₀ k j)
  else rad x₀

theorem padDist_comm (i j : Fin (k + 1)) : padDist x₀ k i j = padDist x₀ k j i := by
  by_cases h : i = j
  · subst h; rfl
  · simp only [padDist, if_neg h, if_neg (Ne.symm h)]
    by_cases h2 : (i : ℕ) < Fintype.card X ∧ (j : ℕ) < Fintype.card X
    · rw [if_pos h2, if_pos ⟨h2.2, h2.1⟩, dist_comm]
    · rw [if_neg h2, if_neg (fun h3 : (j : ℕ) < Fintype.card X ∧ (i : ℕ) < Fintype.card X =>
        h2 ⟨h3.2, h3.1⟩)]

theorem padDist_nonneg (i j : Fin (k + 1)) : 0 ≤ padDist x₀ k i j := by
  simp only [padDist]
  split
  · exact le_rfl
  · split
    · exact dist_nonneg
    · exact le_of_lt (rad_pos x₀)

theorem padDist_le_rad (i j : Fin (k + 1)) : padDist x₀ k i j ≤ rad x₀ := by
  simp only [padDist]
  split
  · exact le_of_lt (rad_pos x₀)
  · split
    · exact dist_le_rad x₀ _ _
    · exact le_rfl

theorem padDist_eq_of_lt {i j : Fin (k + 1)} (hi : (i : ℕ) < Fintype.card X)
    (hj : (j : ℕ) < Fintype.card X) :
    padDist x₀ k i j = dist (proj x₀ k i) (proj x₀ k j) := by
  by_cases h : i = j
  · subst h; simp [padDist]
  · simp [padDist, h, hi, hj]

theorem padDist_triangle (i j l : Fin (k + 1)) :
    padDist x₀ k i l ≤ padDist x₀ k i j + padDist x₀ k j l := by
  by_cases hil : i = l
  · subst hil
    have h1 := padDist_nonneg x₀ k i j
    have h2 := padDist_nonneg x₀ k j i
    have h0 : padDist x₀ k i i = 0 := by simp [padDist]
    rw [h0]
    linarith
  by_cases hij : i = j
  · subst hij; simp [padDist]
  by_cases hjl : j = l
  · subst hjl; simp [padDist]
  by_cases hi : (i : ℕ) < Fintype.card X
  · by_cases hl : (l : ℕ) < Fintype.card X
    · by_cases hj : (j : ℕ) < Fintype.card X
      · rw [padDist_eq_of_lt x₀ k hi hl, padDist_eq_of_lt x₀ k hi hj,
          padDist_eq_of_lt x₀ k hj hl]
        exact dist_triangle _ _ _
      · have e1 : padDist x₀ k i j = rad x₀ := by
          simp [padDist, hij, hj]
        have e2 : padDist x₀ k j l = rad x₀ := by
          simp [padDist, hjl, hj]
        have := padDist_le_rad x₀ k i l
        have := le_of_lt (rad_pos x₀)
        linarith
    · have e1 : padDist x₀ k i l = rad x₀ := by
        simp [padDist, hil, hl]
      by_cases hj : (j : ℕ) < Fintype.card X
      · have e2 : padDist x₀ k j l = rad x₀ := by
          simp [padDist, hjl, hl]
        have := padDist_nonneg x₀ k i j
        linarith
      · have e2 : padDist x₀ k i j = rad x₀ := by
          simp [padDist, hij, hj]
        have := padDist_nonneg x₀ k j l
        linarith
  · have e1 : padDist x₀ k i l = rad x₀ := by
      simp [padDist, hil, hi]
    have e2 : padDist x₀ k i j = rad x₀ := by
      simp [padDist, hij, hi]
    have := padDist_nonneg x₀ k j l
    linarith

theorem padDist_eq_zero {i j : Fin (k + 1)} (h : padDist x₀ k i j = 0) : i = j := by
  by_contra hij
  simp only [padDist, if_neg hij] at h
  by_cases hc : (i : ℕ) < Fintype.card X ∧ (j : ℕ) < Fintype.card X
  · rw [if_pos hc] at h
    have h2 : proj x₀ k i = proj x₀ k j := by
      have := dist_eq_zero.mp h
      exact this
    simp only [proj, dif_pos hc.1, dif_pos hc.2] at h2
    have h3 : (⟨(i : ℕ), hc.1⟩ : Fin (Fintype.card X)) = ⟨(j : ℕ), hc.2⟩ :=
      (Fintype.equivFin X).symm.injective h2
    have h4 : (i : ℕ) = (j : ℕ) := by simpa using h3
    exact hij (Fin.ext h4)
  · rw [if_neg hc] at h
    exact absurd h (ne_of_gt (rad_pos x₀))

/-- The padded metric space on exactly `k + 1` points. -/
@[reducible] noncomputable def padMetric : MetricSpace (Fin (k + 1)) where
  dist := padDist x₀ k
  dist_self i := by simp [padDist]
  dist_comm := padDist_comm x₀ k
  dist_triangle := padDist_triangle x₀ k
  eq_of_dist_eq_zero := padDist_eq_zero x₀ k

theorem padDist_incl (x y : X) :
    padDist x₀ k (incl k hcard x) (incl k hcard y) = dist x y := by
  by_cases h : x = y
  · subst h; simp [padDist]
  · have hne : incl k hcard x ≠ incl k hcard y := fun hh => h (incl_injective k hcard hh)
    have hi : ((incl k hcard x : Fin (k + 1)) : ℕ) < Fintype.card X :=
      (Fintype.equivFin X x).isLt
    have hj : ((incl k hcard y : Fin (k + 1)) : ℕ) < Fintype.card X :=
      (Fintype.equivFin X y).isLt
    rw [padDist_eq_of_lt x₀ k hi hj, proj_incl, proj_incl]

theorem padDist_proj (i j : Fin (k + 1)) :
    dist (proj x₀ k i) (proj x₀ k j) ≤ padDist x₀ k i j := by
  by_cases h : i = j
  · subst h; simp [padDist]
  by_cases hc : (i : ℕ) < Fintype.card X ∧ (j : ℕ) < Fintype.card X
  · rw [padDist_eq_of_lt x₀ k hc.1 hc.2]
  · have : padDist x₀ k i j = rad x₀ := by simp [padDist, h, hc]
    rw [this]
    exact dist_le_rad x₀ _ _

end Pad

theorem solution {X : Type*} [MetricSpace X] [Fintype X]
    {s t : X} {cHi T price : ℝ} {M : ℕ} (k : ℕ) (hcard : Fintype.card X ≤ k + 1)
    (C : KServer.ChunkSystemB X s t 0 cHi T price M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    {V : ℝ}
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V) :
    ∃ (m : MetricSpace (Fin (k + 1))) (a b : Fin (k + 1)),
      @dist (Fin (k + 1)) m.toDist a b = dist s t ∧
      ∃ C' : @KServer.ChunkSystemB (Fin (k + 1)) m a b 0 cHi T price M,
        (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
        (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) := by
  classical
  letI m : MetricSpace (Fin (k + 1)) := Pad.padMetric s k
  refine ⟨m, Pad.incl k hcard s, Pad.incl k hcard t, ?_, ?_⟩
  · show Pad.padDist s k _ _ = dist s t
    exact Pad.padDist_incl s k hcard s t
  · have hmap := KServer.chunk_system_mapped (Y := Fin (k + 1)) C
      (fun S => Pad.incl k hcard '' S) (Pad.proj s k) (Pad.incl k hcard)
      (fun y z => Pad.padDist_proj s k y z)
      (by
        rintro S y ⟨x, hx, rfl⟩
        rw [Pad.proj_incl]
        exact hx)
      (fun S hS => hS.image _)
      (fun S hS => by
        obtain ⟨y, x, hx, -⟩ := hS
        exact ⟨x, hx⟩)
      (fun x x' => Pad.padDist_incl s k hcard x x')
      (fun S => le_rfl)
      rfl
      (le_of_eq (Pad.padDist_incl s k hcard s t).symm)
      (by simp)
      (le_rfl)
      h0triv hVar
    obtain ⟨C', hC'0, hC'V⟩ := hmap
    exact ⟨C', hC'0, hC'V⟩
