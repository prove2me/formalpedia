-- Prove2me | solution 1 for RademacherSymmetrization.radS_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:20:03.526915+00:00
-- url     : https://prove2.me/submissions/a02b4a1b-d947-4847-9cc2-02462002ab46

-- Sol generated from Logic/Rademacher/Symmetrization.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Symmetrization
import Theorems.Thm_RademacherSymmetrization_exp_avg_le
import Theorems.Thm_RademacherSymmetrization_prod_exp_le
import Theorems.Thm_RademacherSymmetrization_sum_exp_signed
/-
# The generalization bound: symmetrization

For a finite hypothesis class `F` of real valued functions on a finite domain `X`,
an arbitrary probability vector `p` on `X`, and i.i.d. samples `S ∈ Xⁿ`, the expected
uniform deviation between the true mean and the empirical mean is at most twice the
expected empirical Rademacher complexity:

  `𝔼_S sup_{f ∈ F} (𝔼_p f − Ê_S f) ≤ 2 · 𝔼_S R̂_S(F)`.

This is the classical *symmetrization* inequality, the reason Rademacher complexity
controls generalization.  Everything is finite here: expectations are explicit weighted
sums over `Xⁿ`, so no measure theory is required and the argument is completely
elementary — but not trivial: the heart of the proof is that for each sign pattern `ε`
the map exchanging the `i`-th points of the sample and of the ghost sample whenever
`ε i = false` is a weight preserving involution of `Xⁿ × Xⁿ`.

This file is self-contained.
-/

open RademacherSymmetrization

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}











/-! ### The product measure -/





/-! ### Step 1: introducing the ghost sample -/



/-! ### Step 2: the swapping involution -/





/-! ### Step 3: the symmetrized quantity is bounded by two Rademacher terms -/


/-! ### The generalization bound -/


/-! ### A Massart bound for the empirical Rademacher complexity of a finite class

To turn the symmetrization inequality into a concrete generalization bound we bound the
empirical Rademacher complexity of a finite class of uniformly bounded functions by the
Chernoff/moment generating function argument, exactly as in Massart's finite class
lemma.
-/









open RademacherSymmetrization in
omit [Fintype X] [DecidableEq X] in
theorem solution(hn : 0 < n) (F : Finset (X → ℝ)) (hne : F.Nonempty) (S : Fin n → X)
    {B l : ℝ} (hl : 0 < l) (hbd : ∀ f ∈ F, ∀ x, |f x| ≤ B) :
    radS F hne S ≤ Real.log F.card / l + l * (B ^ 2 / n) / 2 := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have hBnn : 0 ≤ B := by
    obtain ⟨f, hf⟩ := hne
    obtain ⟨x⟩ : Nonempty X := ⟨S ⟨0, hn⟩⟩
    exact le_trans (abs_nonneg (f x)) (hbd f hf x)
  set A := radS F hne S with hA
  have hstep1 : Real.exp (l * A)
      ≤ (∑ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε S)) / 2 ^ n := by
    have hrw : l * A = (∑ ε : Fin n → Bool, l * maxCorr F hne ε S) / 2 ^ n := by
      rw [← Finset.mul_sum, hA]
      unfold radS
      ring
    rw [hrw]
    exact exp_avg_le _
  have hstep2 : ∀ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε S)
      ≤ ∑ f ∈ F, Real.exp ((l / n) * ∑ i, sgn ε i * f (S i)) := by
    intro ε
    obtain ⟨f₀, hf₀, hval⟩ := Finset.exists_mem_eq_sup' hne (corr ε S)
    have he : Real.exp (l * maxCorr F hne ε S)
        = Real.exp ((l / n) * ∑ i, sgn ε i * f₀ (S i)) := by
      unfold maxCorr
      rw [hval]
      congr 1
      unfold corr
      field_simp
    rw [he]
    exact Finset.single_le_sum
      (f := fun f => Real.exp ((l / n) * ∑ i, sgn ε i * f (S i)))
      (fun f _ => (Real.exp_pos _).le) hf₀
  have hstep3 : ∑ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε S)
      ≤ 2 ^ n * (F.card * Real.exp (l ^ 2 * (B ^ 2 / n) / 2)) := by
    calc ∑ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε S)
        ≤ ∑ ε : Fin n → Bool, ∑ f ∈ F, Real.exp ((l / n) * ∑ i, sgn ε i * f (S i)) :=
          Finset.sum_le_sum fun ε _ => hstep2 ε
      _ = ∑ f ∈ F, ∑ ε : Fin n → Bool, Real.exp ((l / n) * ∑ i, sgn ε i * f (S i)) :=
          Finset.sum_comm
      _ ≤ ∑ _f ∈ F, 2 ^ n * Real.exp (l ^ 2 * (B ^ 2 / n) / 2) := by
          refine Finset.sum_le_sum fun f hf => ?_
          rw [sum_exp_signed (fun i => f (S i)) (l / n)]
          have hnorm : ∑ i, (f (S i)) ^ 2 ≤ (n:ℝ) * B ^ 2 := by
            calc ∑ i, (f (S i)) ^ 2 ≤ ∑ _i : Fin n, B ^ 2 := by
                  refine Finset.sum_le_sum fun i _ => ?_
                  have := hbd f hf (S i)
                  nlinarith [abs_nonneg (f (S i)), sq_abs (f (S i))]
              _ = (n:ℝ) * B ^ 2 := by simp [Finset.sum_const]
          calc ∏ i, (Real.exp ((l / n) * f (S i)) + Real.exp (-((l / n) * f (S i))))
              ≤ 2 ^ n * Real.exp ((l / n) ^ 2 * (∑ i, (f (S i)) ^ 2) / 2) :=
                prod_exp_le (fun i => f (S i)) (l / n)
            _ ≤ 2 ^ n * Real.exp (l ^ 2 * (B ^ 2 / n) / 2) := by
                have hmono : (l / n) ^ 2 * (∑ i, (f (S i)) ^ 2) / 2
                    ≤ l ^ 2 * (B ^ 2 / n) / 2 := by
                  have hexp1 : (l / (n:ℝ)) ^ 2 * (∑ i, (f (S i)) ^ 2) / 2
                      = l ^ 2 * (∑ i, (f (S i)) ^ 2) / (2 * (n:ℝ) ^ 2) := by
                    field_simp
                  have hexp2 : l ^ 2 * (B ^ 2 / (n:ℝ)) / 2
                      = l ^ 2 * ((n:ℝ) * B ^ 2) / (2 * (n:ℝ) ^ 2) := by
                    field_simp
                  rw [hexp1, hexp2]
                  exact div_le_div_of_nonneg_right
                    (by nlinarith [hnorm, sq_nonneg l]) (by positivity)
                have := Real.exp_le_exp.mpr hmono
                nlinarith [Real.exp_pos ((l / n) ^ 2 * (∑ i, (f (S i)) ^ 2) / 2), hpow]
      _ = 2 ^ n * (F.card * Real.exp (l ^ 2 * (B ^ 2 / n) / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : (0:ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hexp : Real.exp (l * A) ≤ F.card * Real.exp (l ^ 2 * (B ^ 2 / n) / 2) := by
    calc Real.exp (l * A)
        ≤ (∑ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε S)) / 2 ^ n := hstep1
      _ ≤ (2 ^ n * (F.card * Real.exp (l ^ 2 * (B ^ 2 / n) / 2))) / 2 ^ n :=
          div_le_div_of_nonneg_right hstep3 hpow.le
      _ = F.card * Real.exp (l ^ 2 * (B ^ 2 / n) / 2) := by field_simp
  have hlog : l * A ≤ Real.log F.card + l ^ 2 * (B ^ 2 / n) / 2 := by
    have hrhs : (F.card : ℝ) * Real.exp (l ^ 2 * (B ^ 2 / n) / 2)
        = Real.exp (Real.log F.card + l ^ 2 * (B ^ 2 / n) / 2) := by
      rw [Real.exp_add, Real.exp_log hcard]
    rw [hrhs] at hexp
    exact Real.exp_le_exp.mp hexp
  rw [div_add' _ _ _ hl.ne', le_div_iff₀ hl]
  nlinarith [hlog]
