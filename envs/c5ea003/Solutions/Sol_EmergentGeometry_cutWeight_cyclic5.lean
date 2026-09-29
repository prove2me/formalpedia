-- Prove2me | solution 1 for EmergentGeometry.cutWeight_cyclic5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:33:01.009927+00:00
-- url     : https://prove2.me/submissions/ad51af76-d430-4aeb-bbed-2b2ecad17850

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicCyclicInequality
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] (G : BulkGraph V)
    (f₀ f₁ f₂ f₃ f₄ : Region V) :
    cutWeight G (fun v => cyc (f₀ v) (f₁ v) (f₂ v) (f₃ v) (f₄ v))
      + cutWeight G (fun v => cyc (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₀ v))
      + cutWeight G (fun v => cyc (f₂ v) (f₃ v) (f₄ v) (f₀ v) (f₁ v))
      + cutWeight G (fun v => cyc (f₃ v) (f₄ v) (f₀ v) (f₁ v) (f₂ v))
      + cutWeight G (fun v => cyc (f₄ v) (f₀ v) (f₁ v) (f₂ v) (f₃ v))
      + cutWeight G (fun v => f₀ v || f₁ v || f₂ v || f₃ v || f₄ v)
      ≤ cutWeight G f₀ + cutWeight G f₁ + cutWeight G f₂ + cutWeight G f₃
        + cutWeight G f₄ := by
  have hcomb : ∀ {m n : ℕ} (F : Fin m → Region V) (H : Fin n → Region V),
      (∀ u v : V, G.weight u v ≠ 0 →
        ∑ i, sepBit (H i u) (H i v) ≤ ∑ j, sepBit (F j u) (F j v)) →
      ∑ i, cutWeight G (H i) ≤ ∑ j, cutWeight G (F j) := by
    intro m n F H h
    -- pointwise comparison of the weighted separation counts
    have hpt : ∀ u v : V,
        ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * G.weight u v
          ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * G.weight u v := by
      intro u v
      by_cases hw : G.weight u v = 0
      · simp [hw]
      · have hle : ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ)
            ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) := by
          exact_mod_cast h u v hw
        exact mul_le_mul_of_nonneg_right hle (G.weight_nonneg u v)
    -- collect each family into a single double sum
    have hcollect : ∀ {k : ℕ} (K : Fin k → Region V),
        (∑ i, cutWeight G (K i))
          = (∑ u : V, ∑ v : V, ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * G.weight u v) / 2 := by
      intro k K
      simp only [cutWeight]
      rw [← Finset.sum_div]
      congr 1
      calc (∑ i, ∑ u : V, ∑ v : V, (sepBit (K i u) (K i v) : ℝ) * G.weight u v)
          = ∑ u : V, ∑ i, ∑ v : V, (sepBit (K i u) (K i v) : ℝ) * G.weight u v :=
            Finset.sum_comm
        _ = ∑ u : V, ∑ v : V, ∑ i, (sepBit (K i u) (K i v) : ℝ) * G.weight u v :=
            Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
        _ = ∑ u : V, ∑ v : V, ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * G.weight u v := by
            refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
            push_cast
            rw [Finset.sum_mul]
    rw [hcollect H, hcollect F]
    have hsum : (∑ u : V, ∑ v : V, ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * G.weight u v)
        ≤ ∑ u : V, ∑ v : V, ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * G.weight u v :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hpt u v))
    linarith
  have hbool : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
      sepBit (cyc a0 a1 a2 a3 a4) (cyc b0 b1 b2 b3 b4)
        + sepBit (cyc a1 a2 a3 a4 a0) (cyc b1 b2 b3 b4 b0)
        + sepBit (cyc a2 a3 a4 a0 a1) (cyc b2 b3 b4 b0 b1)
        + sepBit (cyc a3 a4 a0 a1 a2) (cyc b3 b4 b0 b1 b2)
        + sepBit (cyc a4 a0 a1 a2 a3) (cyc b4 b0 b1 b2 b3)
        + sepBit (a0 || a1 || a2 || a3 || a4) (b0 || b1 || b2 || b3 || b4)
      ≤ sepBit a0 b0 + sepBit a1 b1 + sepBit a2 b2 + sepBit a3 b3 + sepBit a4 b4 := by
    decide
  have key := hcomb ![f₀, f₁, f₂, f₃, f₄]
    ![fun v => cyc (f₀ v) (f₁ v) (f₂ v) (f₃ v) (f₄ v),
      fun v => cyc (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₀ v),
      fun v => cyc (f₂ v) (f₃ v) (f₄ v) (f₀ v) (f₁ v),
      fun v => cyc (f₃ v) (f₄ v) (f₀ v) (f₁ v) (f₂ v),
      fun v => cyc (f₄ v) (f₀ v) (f₁ v) (f₂ v) (f₃ v),
      fun v => f₀ v || f₁ v || f₂ v || f₃ v || f₄ v]
    (by
      intro u v _
      simp only [Fin.sum_univ_six, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.tail_cons, Matrix.cons_val_fin_one, Matrix.cons_val_succ]
      exact hbool (f₀ u) (f₁ u) (f₂ u) (f₃ u) (f₄ u) (f₀ v) (f₁ v) (f₂ v) (f₃ v) (f₄ v))
  simpa [Fin.sum_univ_six, Fin.sum_univ_five, add_assoc] using key
