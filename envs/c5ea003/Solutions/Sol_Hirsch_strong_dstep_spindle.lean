-- Prove2me | solution 1 for Hirsch.strong_dstep_spindle
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T14:22:44.413033+00:00
-- url     : https://prove2.me/submissions/86969885-7ff7-4d0e-aa2d-069ed4741e85

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_spindle_one_step
import Theorems.Thm_Hirsch_spindle_n_ge_two_d

open scoped RealInnerProductSpace
open Set Hirsch

lemma hpoly_reindex {d n m : ℕ} (h : n = m)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Hpoly (fun i : Fin m => a (i.cast h.symm)) (fun i => b (i.cast h.symm)) =
      Hpoly a b := by
  ext x
  simp only [Hpoly, mem_setOf_eq]
  constructor
  · intro hx i
    simpa using hx (i.cast h)
  · intro hx i
    simpa using hx (i.cast h.symm)

lemma not_diamLE_of_no_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (B : ℕ) {u v : E}
    (hu : u ∈ extremePoints ℝ P) (hv : v ∈ extremePoints ℝ P)
    (h : ∀ w : ℕ → E,
      ¬ (w 0 = u ∧ w B = v ∧
          ∀ i < B, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1)))) :
    ¬ DiamLE P B := by
  intro hD
  obtain ⟨w, hw0, hwB, hs⟩ := hD u hu v hv
  exact h w ⟨hw0, hwB, hs⟩

/-- Inductive form of the strong $d$-step theorem, on the excess $n-2d$. -/
lemma strong_dstep_aux (k d n : ℕ) (hd : 0 < d) (heq : n = 2 * d + k)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (D : ℕ) (a' : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (b' : Fin (2 * D) → ℝ),
      D = n - d ∧
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      ¬ DiamLE (Hpoly a' b') D := by
  induction k generalizing d n a b u v with
  | zero =>
    have hn : n = 2 * d := by simpa using heq
    let a' : Fin (2 * d) → EuclideanSpace ℝ (Fin d) := fun i => a (i.cast hn.symm)
    let b' : Fin (2 * d) → ℝ := fun i => b (i.cast hn.symm)
    have hP : Hpoly a' b' = Hpoly a b := hpoly_reindex hn a b
    refine ⟨d, a', b', ?_, ?_, ?_, ?_⟩
    · omega
    · simpa [hP] using hne
    · simpa [hP] using hbd
    · rw [hP]
      exact not_diamLE_of_no_walk (Hpoly a b) d hu hv hlong
  | succ k ih =>
    have hnlt : 2 * d < n := by omega
    obtain ⟨a1, b1, u1, v1, hne1, hbd1, hu1, hv1, hsp1, hlong1⟩ :=
      spindle_one_step d n hd hnlt a b u v hne hbd hu hv hspindle hlong
    have heq' : n + 1 = 2 * (d + 1) + k := by omega
    obtain ⟨D, a', b', hD, hne', hbd', hfail⟩ :=
      ih (d + 1) (n + 1) (Nat.succ_pos d) heq' a1 b1 u1 v1 hne1 hbd1 hu1 hv1 hsp1
        hlong1
    refine ⟨D, a', b', ?_, hne', hbd', hfail⟩
    omega

theorem solution (d n : ℕ) (hd : 0 < d) (hdn : d ≤ n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (D : ℕ) (a' : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (b' : Fin (2 * D) → ℝ),
      D = n - d ∧
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      ¬ DiamLE (Hpoly a' b') D := by
  have hn2 : 2 * d ≤ n := spindle_n_ge_two_d d n hd a b u v hu hv hspindle
  have := hdn
  exact strong_dstep_aux (n - 2 * d) d n hd (by omega) a b u v hne hbd hu hv
    hspindle hlong
