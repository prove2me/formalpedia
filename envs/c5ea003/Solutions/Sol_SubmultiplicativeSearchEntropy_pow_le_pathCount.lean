-- Prove2me | solution 1 for SubmultiplicativeSearchEntropy.pow_le_pathCount
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:51:20.336981+00:00
-- url     : https://prove2.me/submissions/4a78505e-6ffb-4e5d-9d5b-47756a11ff0d

import Mathlib
import Definitions.Def_Bridges_SubmultiplicativeSearchEntropy

open SubmultiplicativeSearchEntropy Filter in
theorem solution {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} {r : ℝ} (hk : 0 < k)
    (hA : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ n, 1 ≤ pathCount A n) {v : Fin k → ℝ} {c C : ℝ}
    (hc : 0 < c) (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v)
    (hr : 0 < r) (n : ℕ) :
    r ^ n ≤ pathCount A n := by
  have hpow : ∀ m : ℕ, (A ^ m).mulVec v = r ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
  have hnn : ∀ m i j, 0 ≤ (A ^ m) i j := by
    intro m
    induction m with
    | zero =>
      intro i j
      rw [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
    | succ m ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)
  -- the Perron vector gives `r^m ≤ (C / (k c)) · pathCount m`
  have hbound : ∀ m : ℕ, r ^ m * (k * c) ≤ C * pathCount A m := by
    intro m
    have e : ∀ i, r ^ m * v i = ∑ j, (A ^ m) i j * v j := by
      intro i
      have h := congrFun (hpow m) i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
      exact h.symm
    calc r ^ m * (k * c) = ∑ i : Fin k, r ^ m * c := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ∑ i : Fin k, r ^ m * v i := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hcv i) (pow_nonneg hr.le m)
      _ = ∑ i, ∑ j, (A ^ m) i j * v j := Finset.sum_congr rfl fun i _ => e i
      _ ≤ ∑ i, ∑ j, (A ^ m) i j * C := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hvC j) (hnn m i j)
      _ = C * pathCount A m := by
          simp only [pathCount, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- path counts are submultiplicative
  have hsub : ∀ a b : ℕ, pathCount A (a + b) ≤ pathCount A a * pathCount A b := by
    intro a b
    have hrow : ∀ l, ∑ j, (A ^ b) l j ≤ pathCount A b := fun l =>
      Finset.single_le_sum (f := fun l => ∑ j, (A ^ b) l j)
        (fun l _ => Finset.sum_nonneg fun j _ => hnn b l j) (Finset.mem_univ l)
    calc pathCount A (a + b) = ∑ i, ∑ l, (A ^ a) i l * ∑ j, (A ^ b) l j := by
          simp only [pathCount, pow_add, Matrix.mul_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ ≤ ∑ i, ∑ l, (A ^ a) i l * pathCount A b :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (hrow l) (hnn a i l)
      _ = pathCount A a * pathCount A b := by
          simp only [pathCount, Finset.sum_mul]
  have hP : 0 < pathCount A n := lt_of_lt_of_le one_pos (h1 n)
  have hmul : ∀ m, 1 ≤ m → pathCount A (n * m) ≤ pathCount A n ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [mul_add_one, pow_succ]
      exact (hsub _ _).trans (mul_le_mul_of_nonneg_right ih hP.le)
  -- if `r^n > pathCount n`, the ratio's powers would stay bounded
  by_contra hlt
  have hx : 1 < r ^ n / pathCount A n := (one_lt_div hP).2 (not_le.1 hlt)
  have hkc : 0 < (k : ℝ) * c := mul_pos (by exact_mod_cast hk) hc
  have hC : 0 ≤ C := (hc.le.trans (hcv ⟨0, hk⟩)).trans (hvC ⟨0, hk⟩)
  obtain ⟨m, hm, hm1⟩ := (((tendsto_pow_atTop_atTop_of_one_lt hx).eventually_gt_atTop
    (C / (k * c))).and (eventually_ge_atTop 1)).exists
  have h2 : r ^ (n * m) * (k * c) ≤ C * pathCount A n ^ m :=
    (hbound (n * m)).trans (mul_le_mul_of_nonneg_left (hmul m hm1) hC)
  have h3 : (r ^ n / pathCount A n) ^ m * (k * c) ≤ C := by
    rw [div_pow, ← pow_mul, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hP m)]
    exact h2
  have h4 := (div_lt_iff₀ hkc).1 hm
  linarith
