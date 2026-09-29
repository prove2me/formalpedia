-- Prove2me | solution 1 for LinearOptimization.fourier_motzkin_eliminate_is_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T16:24:24.564668+00:00
-- url     : https://prove2.me/submissions/33146bbe-1b5c-4f98-86be-0160fa34a615

import Definitions.Def_FourierMotzkinStep
import Mathlib.Algebra.BigOperators.Field

open Matrix Finset

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (b : Fin m → ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      LinearOptimization.fourierMotzkinEliminate A b =
        LinearOptimization.polyhedron A' b' := by
  classical
  let Z := {i : Fin m // A i (Fin.last n) = 0}
  let P := {i : Fin m // 0 < A i (Fin.last n)}
  let N := {i : Fin m // A i (Fin.last n) < 0}
  let I := Z ⊕ (P × N)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let A' : Matrix (Fin (Fintype.card I)) (Fin n) ℝ := fun r l =>
    match e r with
    | Sum.inl k => A k.1 l.castSucc
    | Sum.inr ij =>
        A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n) -
          A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)
  let b' : Fin (Fintype.card I) → ℝ := fun r =>
    match e r with
    | Sum.inl k => b k.1
    | Sum.inr ij =>
        b ij.1.1 / A ij.1.1 (Fin.last n) -
          b ij.2.1 / A ij.2.1 (Fin.last n)
  refine ⟨Fintype.card I, A', b', ?_⟩
  ext y
  constructor
  · intro hy r
    change b' r ≤ ∑ l, A' r l * y l
    cases her : e r with
    | inl k =>
        have hk := k.2
        simpa [A', b', her] using hy.1 k.1 hk
    | inr ij =>
        have hi : 0 < A ij.1.1 (Fin.last n) := ij.1.2
        have hj : A ij.2.1 (Fin.last n) < 0 := ij.2.2
        have hbound := hy.2 ij.1.1 ij.2.1 hi hj
        simp only [LinearOptimization.fourierMotzkinBound] at hbound
        simp only [A', b', her]
        change
          b ij.1.1 / A ij.1.1 (Fin.last n) -
              b ij.2.1 / A ij.2.1 (Fin.last n) ≤
            ∑ l, (A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n) -
              A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)) * y l
        have hsum_i :
            (∑ l, A ij.1.1 l.castSucc * y l) / A ij.1.1 (Fin.last n) =
              ∑ l, (A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n)) * y l := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro l _
          ring
        have hsum_j :
            (∑ l, A ij.2.1 l.castSucc * y l) / A ij.2.1 (Fin.last n) =
              ∑ l, (A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)) * y l := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro l _
          ring
        rw [sub_div, hsum_i, sub_div, hsum_j] at hbound
        calc
          b ij.1.1 / A ij.1.1 (Fin.last n) -
                b ij.2.1 / A ij.2.1 (Fin.last n) ≤
              (∑ l, (A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n)) * y l) -
                ∑ l, (A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)) * y l := by
            linarith
          _ = ∑ l, (A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n) -
                A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)) * y l := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro l _
            ring
  · intro hy
    change b' ≤ A'.mulVec y at hy
    constructor
    · intro k hk
      let z : Z := ⟨k, hk⟩
      let r : Fin (Fintype.card I) := e.symm (Sum.inl z)
      have hr := hy r
      change b' r ≤ ∑ l, A' r l * y l at hr
      simpa [A', b', r, z] using hr
    · intro i j hi hj
      let p : P := ⟨i, hi⟩
      let q : N := ⟨j, hj⟩
      let r : Fin (Fintype.card I) := e.symm (Sum.inr (p, q))
      have hr := hy r
      change b' r ≤ ∑ l, A' r l * y l at hr
      simp only [A', b', r, p, q, e, Equiv.apply_symm_apply] at hr
      simp only [LinearOptimization.fourierMotzkinBound]
      have hsum_i :
          (∑ l, A i l.castSucc * y l) / A i (Fin.last n) =
            ∑ l, (A i l.castSucc / A i (Fin.last n)) * y l := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l _
        ring
      have hsum_j :
          (∑ l, A j l.castSucc * y l) / A j (Fin.last n) =
            ∑ l, (A j l.castSucc / A j (Fin.last n)) * y l := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [sub_div, hsum_i, sub_div, hsum_j]
      have hdiff :
          (∑ l, (A i l.castSucc / A i (Fin.last n)) * y l) -
              ∑ l, (A j l.castSucc / A j (Fin.last n)) * y l =
            ∑ l, (A i l.castSucc / A i (Fin.last n) -
              A j l.castSucc / A j (Fin.last n)) * y l := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [← hdiff] at hr
      linarith
