-- Prove2me | solution 1 for ExtendedSmale9.proposition_10_5_ii_strong
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:33:14.38638+00:00
-- url     : https://prove2.me/submissions/c06ac8c3-685a-4d1e-a261-41f0da50eec2

import Definitions.Def_ExtendedSmale9_GeneralAlgorithm
import Definitions.Def_ExtendedSmale9_Delta1
import Definitions.Def_ExtendedSmale9_LinearProgram
import Mathlib

open scoped ENNReal

namespace SmaleAux
open ExtendedSmale9

/-- Nearest dyadic point of level `m` (coordinatewise rounding). -/
noncomputable def dy (m : ℕ) (z : ℂ) : ℂ :=
  ⟨(round (z.re * 2 ^ m) : ℝ) / 2 ^ m, (round (z.im * 2 ^ m) : ℝ) / 2 ^ m⟩

lemma dy_dyadic (m : ℕ) (z : ℂ) : IsDyadic m (dy m z) :=
  ⟨⟨round (z.re * 2 ^ m), rfl⟩, ⟨round (z.im * 2 ^ m), rfl⟩⟩

lemma coord_bound (m : ℕ) (a : ℝ) : |(round (a * 2 ^ m) : ℝ) / 2 ^ m - a| ≤ 1 / 2 / 2 ^ m := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have h := abs_sub_round (a * 2 ^ m)
  have e : (round (a * 2 ^ m) : ℝ) / 2 ^ m - a = -((a * 2 ^ m - round (a * 2 ^ m)) / 2 ^ m) := by
    field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right h hp.le

lemma dy_close (m : ℕ) (z : ℂ) : ‖dy m z - z‖ ≤ 3 / 4 * (1 / 2 ^ m) := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have h1 := coord_bound m z.re
  have h2 := coord_bound m z.im
  have hre : (dy m z - z).re = (round (z.re * 2 ^ m) : ℝ) / 2 ^ m - z.re := by simp [dy]
  have him : (dy m z - z).im = (round (z.im * 2 ^ m) : ℝ) / 2 ^ m - z.im := by simp [dy]
  set w := dy m z - z
  have hsq : ‖w‖ ^ 2 ≤ (3 / 4 * (1 / 2 ^ m)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have a1 := abs_le.mp h1
    have a2 := abs_le.mp h2
    set e := 1 / (2 : ℝ) ^ m with he
    have : 1 / 2 / (2 : ℝ) ^ m = e / 2 := by rw [he]; ring
    rw [this] at a1 a2
    nlinarith [a1.1, a1.2, a2.1, a2.2]
  exact le_of_sq_le_sq (by simpa using hsq) (by positivity) |>.trans le_rfl

end SmaleAux

open ExtendedSmale9 SmaleAux in
theorem solution {Ω Idx M : Type*} [Countable Idx] [MetricSpace M]
    (Λ : Idx → Ω → ℂ) (Ξ : Ω → Set M) (ι₁ ι₂ : ℕ+ → Ω)
    (S₁ S₂ : Set M) (κ : ℝ) (hκ : 0 < κ)
    (hsep : ∀ x₁ ∈ S₁, ∀ x₂ ∈ S₂, κ ≤ dist x₁ x₂)
    (hΞ₁ : ∀ n, Ξ (ι₁ n) ⊆ S₁) (hΞ₂ : ∀ n, Ξ (ι₂ n) ⊆ S₂)
    (ι₀ : Ω)
    (hc₁ : ∀ k n, ‖Λ k (ι₁ n) - Λ k ι₀‖ ≤ 1 / 4 ^ (n : ℕ))
    (hc₂ : ∀ k n, ‖Λ k (ι₂ n) - Λ k ι₀‖ ≤ 1 / 4 ^ (n : ℕ)) :
    ∃ fhat : Idx → ℕ+ → Ω → ℂ, IsDelta1Info Λ fhat ∧
      ENNReal.ofReal (κ / 2) ≤ strongBreakdownEps (delta1Eval fhat) Ξ := by
  classical
  let C : ℕ+ → Ω → Prop := fun m ι =>
    ι = ι₀ ∨ ∃ n : ℕ+, (m : ℕ) < n ∧ (ι = ι₁ n ∨ ι = ι₂ n)
  let fhat : Idx → ℕ+ → Ω → ℂ := fun j m ι =>
    if C m ι then dy m (Λ j ι₀) else dy m (Λ j ι)
  -- the perturbation estimate
  have hpert : ∀ (j : Idx) (m n : ℕ+), (m : ℕ) < n → ∀ ι, ‖Λ j ι - Λ j ι₀‖ ≤ 1 / 4 ^ (n : ℕ) →
      ‖dy m (Λ j ι₀) - Λ j ι‖ ≤ 1 / 2 ^ (m : ℕ) := by
    intro j m n hmn ι hι
    have h1 := dy_close m (Λ j ι₀)
    have h4 : (1 : ℝ) / 4 ^ (n : ℕ) ≤ 1 / 4 ^ ((m : ℕ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hmn)
    have h5 : (1 : ℝ) / 4 ^ ((m : ℕ) + 1) = (1 / 2 ^ (m : ℕ)) * (1 / 2 ^ (m : ℕ)) / 4 := by
      rw [pow_succ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      field_simp
      ring
    have h6 : (1 : ℝ) / 2 ^ (m : ℕ) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have h7 : 0 ≤ (1 : ℝ) / 2 ^ (m : ℕ) := by positivity
    calc ‖dy m (Λ j ι₀) - Λ j ι‖ ≤ ‖dy m (Λ j ι₀) - Λ j ι₀‖ + ‖Λ j ι - Λ j ι₀‖ := by
          rw [← norm_neg (Λ j ι - Λ j ι₀)]
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ ≤ 3 / 4 * (1 / 2 ^ (m : ℕ)) + (1 / 2 ^ (m : ℕ)) * (1 / 2 ^ (m : ℕ)) / 4 := by
          gcongr; rw [← h5]; exact hι.trans h4
      _ ≤ 1 / 2 ^ (m : ℕ) := by nlinarith
  have hinfo : IsDelta1Info Λ fhat := by
    intro j m ι
    simp only [fhat]
    split_ifs with hC
    · refine ⟨dy_dyadic _ _, ?_⟩
      rcases hC with h0 | ⟨n, hmn, h1 | h2⟩
      · subst h0
        exact (dy_close m (Λ j ι)).trans (by
          have : (0 : ℝ) ≤ 1 / 2 ^ (m : ℕ) := by positivity
          linarith)
      · subst h1; exact hpert j m n hmn _ (hc₁ j n)
      · subst h2; exact hpert j m n hmn _ (hc₂ j n)
    · refine ⟨dy_dyadic _ _, (dy_close m (Λ j ι)).trans ?_⟩
      have : (0 : ℝ) ≤ 1 / 2 ^ (m : ℕ) := by positivity
      linarith
  refine ⟨fhat, hinfo, ?_⟩
  -- every ε < κ/2 lies in the defining set
  have hmem : ∀ ε : ℝ≥0∞, ε < ENNReal.ofReal (κ / 2) →
      ∀ Γ : GeneralAlgorithm (delta1Eval fhat) M, ∃ ι : Ω, ε < errDist (Γ.run ι) (Ξ ι) := by
    intro ε hε Γ
    cases hrun : Γ.run ι₀ with
    | none =>
      refine ⟨ι₀, ?_⟩
      rw [hrun]
      exact lt_of_lt_of_le hε le_top
    | some x =>
      have hfin := Γ.queried_finite ι₀ (by rw [hrun]; simp)
      obtain ⟨L, hL⟩ := (hfin.image (fun q : Idx × ℕ+ => (q.2 : ℕ))).bddAbove
      let n : ℕ+ := ⟨L + 1, Nat.succ_pos L⟩
      have hagree : ∀ ι, (ι = ι₁ n ∨ ι = ι₂ n) →
          ∀ q ∈ Γ.queried ι₀, delta1Eval fhat q ι = delta1Eval fhat q ι₀ := by
        intro ι hι q hq
        have hqL : (q.2 : ℕ) ≤ L := hL ⟨q, hq, rfl⟩
        have hC1 : C q.2 ι := Or.inr ⟨n, by show (q.2 : ℕ) < L + 1; omega, hι⟩
        have hC0 : C q.2 ι₀ := Or.inl rfl
        simp only [delta1Eval, fhat, if_pos hC1, if_pos hC0]
      have hr1 : Γ.run (ι₁ n) = some x := by
        rw [Γ.run_eq_of_agree ι₀ (ι₁ n) (hagree _ (Or.inl rfl)), hrun]
      have hr2 : Γ.run (ι₂ n) = some x := by
        rw [Γ.run_eq_of_agree ι₀ (ι₂ n) (hagree _ (Or.inr rfl)), hrun]
      by_contra hcon
      push Not at hcon
      have e1 := hcon (ι₁ n)
      have e2 := hcon (ι₂ n)
      rw [hr1] at e1
      rw [hr2] at e2
      simp only [errDist] at e1 e2
      obtain ⟨ξ₁, hξ₁, d1⟩ : ∃ ξ ∈ Ξ (ι₁ n), edist x ξ < ENNReal.ofReal (κ / 2) := by
        have := lt_of_le_of_lt e1 hε
        simpa [iInf_lt_iff] using this
      obtain ⟨ξ₂, hξ₂, d2⟩ : ∃ ξ ∈ Ξ (ι₂ n), edist x ξ < ENNReal.ofReal (κ / 2) := by
        have := lt_of_le_of_lt e2 hε
        simpa [iInf_lt_iff] using this
      have hd := hsep ξ₁ (hΞ₁ n hξ₁) ξ₂ (hΞ₂ n hξ₂)
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith)] at d1 d2
      have := dist_triangle_left ξ₁ ξ₂ x
      linarith
  apply le_of_forall_lt
  intro c hc
  obtain ⟨ε, hcε, hε⟩ := exists_between hc
  exact lt_of_lt_of_le hcε (le_sSup (hmem ε hε))
