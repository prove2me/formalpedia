-- Prove2me | solution 1 for LinearOptimization.simplex_termination_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T03:51:18.811049+00:00
-- url     : https://prove2.me/submissions/d4296e94-f327-439b-83d8-178595cc13df

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot
import Definitions.Def_LinearOptimization_OptimalBasis
import Theorems.Thm_LinearOptimization_simplex_pivot_state_cost_decrease
import Theorems.Thm_LinearOptimization_simplex_terminal_classification

open Matrix

private lemma eq_zero_of_kernel_of_eq_zero_off_basis {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n)
    (hB : LinearOptimization.IsStdBasis A B) (d : Fin n → ℝ)
    (hAd : A.mulVec d = 0) (hd : ∀ j ∉ Set.range B, d j = 0) : d = 0 := by
  classical
  have hcols : LinearIndependent ℝ (LinearOptimization.basisMatrix A B).col := by
    simpa [Matrix.col, LinearOptimization.basisMatrix] using hB
  have hunit : IsUnit (LinearOptimization.basisMatrix A B) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  let alpha : Fin m → ℝ := fun i => d (B i)
  have hBM : (LinearOptimization.basisMatrix A B).mulVec alpha = 0 := by
    funext i
    change (∑ k : Fin m, A i (B k) * d (B k)) = 0
    have himage : (∑ k : Fin m, A i (B k) * d (B k)) =
        ∑ j ∈ Finset.univ.image B, A i j * d j := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => B.injective h
    rw [himage]
    have hall : (∑ j ∈ Finset.univ.image B, A i j * d j) =
        ∑ j : Fin n, A i j * d j := by
      apply Finset.sum_subset (by intro j hj; simp)
      intro j _ hj
      have hjrange : j ∉ Set.range B := by
        intro hr
        obtain ⟨k, rfl⟩ := hr
        exact hj (by simp)
      rw [hd j hjrange, mul_zero]
    rw [hall]
    simpa [Matrix.mulVec, dotProduct] using congrFun hAd i
  have halpha : alpha = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (by simpa using hBM)
  funext j
  by_cases hj : j ∈ Set.range B
  · obtain ⟨i, rfl⟩ := hj
    exact congrFun halpha i
  · exact hd j hj

private lemma simplex_state_unique {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (B : Fin m ↪ Fin n) (x y : Fin n → ℝ)
    (hx : LinearOptimization.IsSimplexState A b B x)
    (hy : LinearOptimization.IsSimplexState A b B y) : x = y := by
  have hker : A.mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hx.2.1.1, hy.2.1.1, sub_self]
  have hoff : ∀ j ∉ Set.range B, (x - y) j = 0 := by
    intro j hj
    simp [hx.2.2 j hj, hy.2.2 j hj]
  exact sub_eq_zero.mp
    (eq_zero_of_kernel_of_eq_zero_off_basis A B hx.1 (x - y) hker hoff)

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (hne : (LinearOptimization.stdPolyhedron A b).Nonempty)
    (hnd : ∀ x, LinearOptimization.IsBasicFeasibleSolution
      (LinearOptimization.stdFormSystem A b) x →
      ¬LinearOptimization.IsStdDegenerateBasicSolution A b x) :
    (¬∃ f : ℕ → (Fin m ↪ Fin n) × (Fin n → ℝ),
      (∀ k, LinearOptimization.IsSimplexState A b (f k).1 (f k).2) ∧
      ∀ k, LinearOptimization.IsSimplexPivot A c (f k).1 (f k).2
        (f (k + 1)).1 (f (k + 1)).2) ∧
    ∀ (B : Fin m ↪ Fin n) (x : Fin n → ℝ),
      LinearOptimization.IsSimplexState A b B x →
      (¬∃ (B' : Fin m ↪ Fin n) (x' : Fin n → ℝ),
        LinearOptimization.IsSimplexPivot A c B x B' x') →
      (LinearOptimization.IsOptimalBasis A b c B ∧
        LinearOptimization.IsLpOptimal c (LinearOptimization.stdPolyhedron A b) x) ∨
      ∃ d : Fin n → ℝ, A.mulVec d = 0 ∧ 0 ≤ d ∧ c ⬝ᵥ d < 0 ∧
        LinearOptimization.lpValue c (LinearOptimization.stdPolyhedron A b) = ⊥ := by
  constructor
  · rintro ⟨f, hstates, hpivots⟩
    let cost : ℕ → ℝ := fun k => c ⬝ᵥ (f k).2
    have hstep : ∀ k, cost (k + 1) < cost k := by
      intro k
      exact (LinearOptimization.simplex_pivot_state_cost_decrease
        A b c hA (f k).1 (f (k + 1)).1 (f k).2 (f (k + 1)).2
        (hstates k) hnd (hpivots k)).2
    have hchain : ∀ p q, p < q → cost q < cost p := by
      intro p q hpq
      induction q with
      | zero => omega
      | succ q ih =>
          by_cases hp : p = q
          · subst p
            exact hstep q
          · exact lt_trans (hstep q) (ih (by omega))
    let N := Fintype.card (Fin m ↪ Fin n)
    let g : Fin (N + 1) → (Fin m ↪ Fin n) := fun i => (f i).1
    have hgnot : ¬Function.Injective g := by
      intro hginj
      have hc := Fintype.card_le_of_injective g hginj
      simp [N] at hc
    obtain ⟨p, q, hpqeq, hpqne⟩ := Function.not_injective_iff.mp hgnot
    have hbasis : (f (p : ℕ)).1 = (f (q : ℕ)).1 := by
      simpa [g] using hpqeq
    have hpoint : (f (p : ℕ)).2 = (f (q : ℕ)).2 := by
      apply simplex_state_unique A b (f (p : ℕ)).1
      · exact hstates p
      · simpa [hbasis] using hstates q
    rcases lt_or_gt_of_ne hpqne with hpq | hqp
    · have hlt := hchain p q hpq
      have heq : cost p = cost q := by simp [cost, hpoint]
      exact (lt_irrefl (cost p)) (heq ▸ hlt)
    · have hlt := hchain q p hqp
      have heq : cost q = cost p := by simp [cost, hpoint]
      exact (lt_irrefl (cost q)) (heq ▸ hlt)
  · intro B x hstate hterminal
    exact LinearOptimization.simplex_terminal_classification
      A b c hA B x hstate hterminal
