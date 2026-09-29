-- Prove2me | solution 1 for LinearOptimization.simplex_lexicographic_anticycling
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T03:25:50.595738+00:00
-- url     : https://prove2.me/submissions/2f32130d-e95a-4415-b157-e89367fa84a5

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot
import Theorems.Thm_LinearOptimization_simplex_lexicographic_pivot_step

open Matrix

private lemma lexLt_trans {k : ℕ} {u v w : Fin k → ℝ}
    (huv : LinearOptimization.LexLt u v)
    (hvw : LinearOptimization.LexLt v w) :
    LinearOptimization.LexLt u w := by
  rcases huv with ⟨i, hi, hprei⟩
  rcases hvw with ⟨j, hj, hprej⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · refine ⟨i, ?_, ?_⟩
    · rw [← hprej i hij]
      exact hi
    · intro q hqi
      rw [hprei q hqi, hprej q (lt_trans hqi hij)]
  · subst j
    refine ⟨i, lt_trans hi hj, ?_⟩
    intro q hqi
    rw [hprei q hqi, hprej q hqi]
  · refine ⟨j, ?_, ?_⟩
    · rw [hprei j hij]
      exact hj
    · intro q hqj
      rw [hprei q (lt_trans hqj hij), hprej q hqj]

private lemma lexLt_irrefl {k : ℕ} (u : Fin k → ℝ) :
    ¬LinearOptimization.LexLt u u := by
  rintro ⟨i, hi, _⟩
  exact (lt_irrefl (u i)) hi

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i)) :
    (∀ (B B' : Fin m ↪ Fin n) (x x' : Fin n → ℝ),
      LinearOptimization.IsSimplexState A b B x →
      (∀ i, LinearOptimization.LexPos (LinearOptimization.tableauRow A b B i)) →
      LinearOptimization.IsLexicographicPivot A b c B x B' x' →
      (∀ i, LinearOptimization.LexPos (LinearOptimization.tableauRow A b B' i)) ∧
      LinearOptimization.LexLt (LinearOptimization.tableauZerothRow A b c B)
        (LinearOptimization.tableauZerothRow A b c B')) ∧
    ¬∃ f : ℕ → (Fin m ↪ Fin n) × (Fin n → ℝ),
      (∀ k, LinearOptimization.IsSimplexState A b (f k).1 (f k).2) ∧
      (∀ i, LinearOptimization.LexPos
        (LinearOptimization.tableauRow A b (f 0).1 i)) ∧
      ∀ k, LinearOptimization.IsLexicographicPivot A b c
        (f k).1 (f k).2 (f (k + 1)).1 (f (k + 1)).2 := by
  constructor
  · intro B B' x x' hstate hpos hpivot
    exact LinearOptimization.simplex_lexicographic_pivot_step
      A b c hA B B' x x' hstate hpos hpivot
  · rintro ⟨f, hstates, hpos0, hpivots⟩
    let z : ℕ → Fin (n + 1) → ℝ := fun k =>
      LinearOptimization.tableauZerothRow A b c (f k).1
    have hpos : ∀ k i,
        LinearOptimization.LexPos (LinearOptimization.tableauRow A b (f k).1 i) := by
      intro k
      induction k with
      | zero => exact hpos0
      | succ k ih =>
          exact (LinearOptimization.simplex_lexicographic_pivot_step
            A b c hA (f k).1 (f (k + 1)).1 (f k).2 (f (k + 1)).2
            (hstates k) ih (hpivots k)).1
    have hstep : ∀ k, LinearOptimization.LexLt (z k) (z (k + 1)) := by
      intro k
      exact (LinearOptimization.simplex_lexicographic_pivot_step
        A b c hA (f k).1 (f (k + 1)).1 (f k).2 (f (k + 1)).2
        (hstates k) (hpos k) (hpivots k)).2
    have hchain : ∀ p q, p < q → LinearOptimization.LexLt (z p) (z q) := by
      intro p q hpq
      induction q with
      | zero => omega
      | succ q ih =>
          by_cases hp : p = q
          · subst p
            exact hstep q
          · exact lexLt_trans (ih (by omega)) (hstep q)
    let N := Fintype.card (Fin m ↪ Fin n)
    let g : Fin (N + 1) → (Fin m ↪ Fin n) := fun i => (f i).1
    have hgnot : ¬Function.Injective g := by
      intro hginj
      have hc := Fintype.card_le_of_injective g hginj
      simp [N] at hc
    obtain ⟨p, q, hpqeq, hpqne⟩ := Function.not_injective_iff.mp hgnot
    have hbasis : (f (p : ℕ)).1 = (f (q : ℕ)).1 := by
      simpa [g] using hpqeq
    rcases lt_or_gt_of_ne hpqne with hpq | hqp
    · have hz := hchain p q hpq
      apply lexLt_irrefl (z p)
      simpa [z, hbasis] using hz
    · have hz := hchain q p hqp
      apply lexLt_irrefl (z q)
      simpa [z, hbasis] using hz
