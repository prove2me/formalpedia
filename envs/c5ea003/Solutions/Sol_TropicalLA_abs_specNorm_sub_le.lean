-- Prove2me | solution 1 for TropicalLA.abs_specNorm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:37:06.261305+00:00
-- url     : https://prove2.me/submissions/0fcff517-c7c6-4c77-bc65-4d89b7c1f3c7

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}
    (h : IsTropEigen A lam v) (m : ℕ) :
    |specNorm A m - (m + 1) * lam| ≤
      Finset.univ.sup' (Finset.univ_nonempty (α := ι)) v
        - Finset.univ.inf' (Finset.univ_nonempty (α := ι)) v := by
  classical
  have hstep : ∀ m i t, tpow A (m + 1) i t
      = univ.sup' univ_nonempty (fun l => tpow A m i l + A l t) := fun _ _ _ => rfl
  have hup : ∀ (lam : ℝ) (v : ι → ℝ), IsTropEigen A lam v →
      ∀ m i j, tpow A m i j + v j ≤ ((m : ℝ) + 1) * lam + v i := by
    intro lam v hv m
    induction m with
    | zero =>
      intro i j
      have h1 := Finset.le_sup' (fun j => A i j + v j) (mem_univ j)
      have h2 : univ.sup' univ_nonempty (fun j => A i j + v j) = lam + v i := hv i
      simp only [tpow]
      push_cast
      linarith
    | succ m ih =>
      intro i j
      rw [hstep m i j]
      have h2 : univ.sup' univ_nonempty (fun l => tpow A m i l + A l j)
          ≤ ((m : ℝ) + 1) * lam + v i + lam - v j := by
        apply Finset.sup'_le
        intro l _
        have h3 := ih i l
        have h4 := Finset.le_sup' (fun j' => A l j' + v j') (mem_univ j)
        have h5 : univ.sup' univ_nonempty (fun j' => A l j' + v j') = lam + v l := hv l
        linarith
      push_cast
      linarith
  choose f hf using fun i => h.exists_tight i
  have hlow : ∀ (m : ℕ) (i : ι), ∃ e, ((m : ℝ) + 1) * lam + v i - v e ≤ tpow A m i e := by
    intro m
    induction m with
    | zero =>
      intro i
      refine ⟨f i, ?_⟩
      simp only [tpow]
      have := hf i
      push_cast
      linarith
    | succ m ih =>
      intro i
      obtain ⟨e, he⟩ := ih i
      refine ⟨f e, ?_⟩
      rw [hstep m i (f e)]
      have h1 := Finset.le_sup' (fun l => tpow A m i l + A l (f e)) (mem_univ e)
      have h2 := hf e
      push_cast
      linarith
  have hSv : ∀ i, v i ≤ univ.sup' (univ_nonempty (α := ι)) v := fun i => Finset.le_sup' v (mem_univ i)
  have hIv : ∀ i, univ.inf' (univ_nonempty (α := ι)) v ≤ v i := fun i => Finset.inf'_le v (mem_univ i)
  rw [abs_le]
  constructor
  · obtain ⟨i0⟩ := ‹Nonempty ι›
    obtain ⟨e, he⟩ := hlow m i0
    have h1 : tpow A m i0 e ≤ specNorm A m := by
      unfold specNorm
      exact le_trans (Finset.le_sup' (fun j => tpow A m i0 j) (mem_univ e))
        (Finset.le_sup' (fun i => univ.sup' univ_nonempty (fun j => tpow A m i j)) (mem_univ i0))
    have h2 := hSv e
    have h3 := hIv i0
    linarith
  · have h1 : specNorm A m ≤ ((m : ℝ) + 1) * lam
        + (univ.sup' (univ_nonempty (α := ι)) v - univ.inf' (univ_nonempty (α := ι)) v) := by
      unfold specNorm
      apply Finset.sup'_le
      intro i _
      apply Finset.sup'_le
      intro j _
      have h2 := hup lam v h m i j
      have h3 := hSv i
      have h4 := hIv j
      linarith
    linarith
