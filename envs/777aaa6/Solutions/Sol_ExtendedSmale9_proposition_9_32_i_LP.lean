-- Prove2me | solution 1 for ExtendedSmale9.proposition_9_32_i_LP
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:40:12.460979+00:00
-- url     : https://prove2.me/submissions/5fad5a4e-22be-403e-8b94-d768acb287cb

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
theorem SmaleAux.prop_10_5 {Ω Idx M : Type*} [Countable Idx] [MetricSpace M]
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

open scoped ENNReal

namespace SmaleLP
open ExtendedSmale9

variable {m N : ℕ}

lemma row0 (hm : 4 ≤ m) (hmN : m < N) (a b : ℝ) (x : Fin N → ℝ) :
    (lpMatrixA a b m N).mulVec x ⟨0, by omega⟩ =
      a * x ⟨0, by omega⟩ + b * x ⟨1, by omega⟩ - x ⟨2, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, lpMatrixA, if_true]
  have e : ∀ j : Fin N, (if (j : ℕ) = 0 then a else if (j : ℕ) = 1 then b else
      if (j : ℕ) = 2 then -1 else 0) * x j =
      (if j = ⟨0, by omega⟩ then a * x j else 0) + (if j = ⟨1, by omega⟩ then b * x j else 0)
        + (if j = ⟨2, by omega⟩ then -x j else 0) := by
    intro j
    rcases j with ⟨j, hj⟩
    simp only [Fin.mk.injEq]
    rcases Nat.lt_or_ge j 3 with h | h
    · interval_cases j <;> simp
    · have h0 : j ≠ 0 := by omega
      have h1 : j ≠ 1 := by omega
      have h2 : j ≠ 2 := by omega
      simp [h0, h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

lemma rows_single (hm : 4 ≤ m) (hmN : m < N) (a b v : ℝ) (j0 : Fin N) (hj0 : (j0 : ℕ) < 2)
    (i : Fin m) (hi : (i : ℕ) ≠ 0) : (lpMatrixA a b m N).mulVec (Pi.single j0 v) i = 0 := by
  simp only [Matrix.mulVec, dotProduct, lpMatrixA, hi, if_false]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : (j : ℕ) = (i : ℕ) + 2
  · have : j ≠ j0 := by intro h; subst h; omega
    simp [hj, Pi.single_apply, this]
  · simp [hj]

lemma feas_single (hm : 4 ≤ m) (hmN : m < N) (a b : ℝ) (j0 : Fin N) (hj0 : (j0 : ℕ) < 2)
    (v : ℝ) (hv : 0 ≤ v)
    (h0 : (lpMatrixA a b m N).mulVec (Pi.single j0 v) ⟨0, by omega⟩ = 1) :
    Pi.single j0 v ∈ lpFeasible (lpVectorA 1 m) (lpMatrixA a b m N) := by
  refine ⟨?_, fun i => ?_⟩
  · funext i
    by_cases hi : (i : ℕ) = 0
    · have : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [this, h0]; simp [lpVectorA]
    · rw [rows_single hm hmN a b v j0 hj0 i hi]; simp [lpVectorA, hi]
  · by_cases h : i = j0
    · subst h; simp [hv]
    · simp [Pi.single_apply, h]

lemma sum_ge (hm : 4 ≤ m) (hmN : m < N) (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) :
    x ⟨0, by omega⟩ + x ⟨1, by omega⟩ + x ⟨2, by omega⟩ ≤ (fun _ => (1 : ℝ)) ⬝ᵥ x := by
  simp only [dotProduct, one_mul]
  have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin N)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hx i)
  rw [Finset.sum_insert (by simp [Fin.ext_iff]), Finset.sum_insert (by simp [Fin.ext_iff]),
    Finset.sum_singleton] at this
  linarith

lemma sum_single (j0 : Fin N) (v : ℝ) : (fun _ => (1 : ℝ)) ⬝ᵥ Pi.single j0 v = v := by
  simp [dotProduct]

/-- For `a ≥ b > 0`, `v e₀` with `v = 1/a` is optimal. -/
lemma argmin0 (hm : 4 ≤ m) (hmN : m < N) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hab : b ≤ a) :
    Pi.single ⟨0, by omega⟩ (1 / a) ∈ lpArgmin (fun _ => 1) (lpVectorA 1 m) (lpMatrixA a b m N) := by
  refine ⟨feas_single hm hmN a b _ (by simp) _ (by positivity) ?_, fun x hx => ?_⟩
  · rw [row0 hm hmN]; simp [Pi.single_apply, Fin.ext_iff]; field_simp
  · rw [sum_single]
    have h1 := congrFun hx.1 ⟨0, by omega⟩
    rw [row0 hm hmN] at h1
    simp only [lpVectorA, if_true] at h1
    have hs := sum_ge hm hmN x hx.2
    have hx0 := hx.2 ⟨0, by omega⟩
    have hx1 := hx.2 ⟨1, by omega⟩
    have hx2 := hx.2 ⟨2, by omega⟩
    rw [div_le_iff₀ ha]
    nlinarith

lemma argmin1 (hm : 4 ≤ m) (hmN : m < N) (a b : ℝ) (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b) :
    Pi.single ⟨1, by omega⟩ (1 / b) ∈ lpArgmin (fun _ => 1) (lpVectorA 1 m) (lpMatrixA a b m N) := by
  refine ⟨feas_single hm hmN a b _ (by simp) _ (by positivity) ?_, fun x hx => ?_⟩
  · rw [row0 hm hmN]; simp [Pi.single_apply, Fin.ext_iff]; field_simp
  · rw [sum_single]
    have h1 := congrFun hx.1 ⟨0, by omega⟩
    rw [row0 hm hmN] at h1
    simp only [lpVectorA, if_true] at h1
    have hs := sum_ge hm hmN x hx.2
    have hx0 := hx.2 ⟨0, by omega⟩
    have hx1 := hx.2 ⟨1, by omega⟩
    have hx2 := hx.2 ⟨2, by omega⟩
    rw [div_le_iff₀ hb]
    nlinarith

lemma incl1 (hm : 4 ≤ m) (hmN : m < N) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) (z : Fin N → ℝ)
    (hz : z ∈ lpArgmin (fun _ => 1) (lpVectorA 1 m) (lpMatrixA (1 / 2 + ε) (1 / 2) m N)) :
    4 / 3 ≤ z ⟨0, by omega⟩ := by
  have hopt := hz.2 _ (argmin0 hm hmN (1 / 2 + ε) (1 / 2) (by linarith) (by norm_num) (by linarith)).1
  rw [sum_single] at hopt
  have h1 := congrFun hz.1.1 ⟨0, by omega⟩
  rw [row0 hm hmN] at h1
  simp only [lpVectorA, if_true] at h1
  have hs := sum_ge hm hmN z hz.1.2
  have hz1 := hz.1.2 ⟨1, by omega⟩
  have hz2 := hz.1.2 ⟨2, by omega⟩
  set t := 1 / (1 / 2 + ε) with ht
  have htα : t * (1 / 2 + ε) = 1 := by rw [ht]; field_simp
  set z0 := z ⟨0, by omega⟩
  set z1 := z ⟨1, by omega⟩
  set z2 := z ⟨2, by omega⟩
  -- z1 ≤ t - z0 - z2, so 1 + z2 ≤ (1/2+ε) z0 + (t - z0 - z2)/2
  have k1 : 1 ≤ ε * z0 + t / 2 := by nlinarith
  have k2 : t ≤ 2 / (1 + 2 * ε) := by rw [ht]; field_simp; linarith
  have k3 : 2 / (1 + 2 * ε) = t := by rw [ht]; field_simp
  -- ε z0 ≥ 1 - t/2 = ε t, so z0 ≥ t ≥ 4/3
  have k4 : ε * t = 1 - t / 2 := by nlinarith
  have k5 : t ≤ z0 := by nlinarith
  have k6 : 4 / 3 ≤ t := by
    rw [← k3, le_div_iff₀ (by linarith)]; linarith
  linarith

lemma incl2 (hm : 4 ≤ m) (hmN : m < N) (ε : ℝ) (hε : 0 < ε) (z : Fin N → ℝ)
    (hz : z ∈ lpArgmin (fun _ => 1) (lpVectorA 1 m) (lpMatrixA (1 / 2) (1 / 2 + ε) m N)) :
    z ⟨0, by omega⟩ ≤ 0 := by
  have hopt := hz.2 _ (argmin1 hm hmN (1 / 2) (1 / 2 + ε) (by linarith) (by norm_num) (by linarith)).1
  rw [sum_single] at hopt
  have h1 := congrFun hz.1.1 ⟨0, by omega⟩
  rw [row0 hm hmN] at h1
  simp only [lpVectorA, if_true] at h1
  have hs := sum_ge hm hmN z hz.1.2
  have hz0 := hz.1.2 ⟨0, by omega⟩
  have hz2 := hz.1.2 ⟨2, by omega⟩
  set t := 1 / (1 / 2 + ε) with ht
  have htβ : (1 / 2 + ε) * t = 1 := by rw [ht]; field_simp
  set z0 := z ⟨0, by omega⟩
  set z1 := z ⟨1, by omega⟩
  set z2 := z ⟨2, by omega⟩
  nlinarith

end SmaleLP

open ExtendedSmale9 SmaleLP in
theorem solution (K : ℕ) (hK : 1 ≤ K) (m N : ℕ) (hm : 4 ≤ m) (hmN : m < N)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ Ω : Set (LPInput m N), Ω.Nonempty ∧
      (∀ ι ∈ Ω, (lpArgmin (fun _ => 1) ι.1 ι.2).Nonempty ∧ (∀ i, |ι.1 i| ≤ 2) ∧
        (∀ i j, |ι.2 i j| ≤ 1) ∧ ∃ i j, |ι.2 i j| = 1) ∧
      ∃ fhat : (Fin m ⊕ (Fin m × Fin N)) → ℕ+ → Ω → ℂ,
        IsDelta1Info (fun k (ι : Ω) => lpEval k ι.1) fhat ∧
        ENNReal.ofReal (10 ^ (-(K : ℤ))) <
          strongBreakdownEps (delta1Eval fhat) (fun ι : Ω => lpSolution p ι.1) := by
  let inp : ℝ → ℝ → LPInput m N := fun a b => (lpVectorA 1 m, lpMatrixA a b m N)
  let δ : ℕ+ → ℝ := fun n => 1 / 4 ^ (n : ℕ)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  have hδ' : ∀ n, δ n ≤ 1 / 4 := fun n => by
    show 1 / (4 : ℝ) ^ (n : ℕ) ≤ 1 / 4
    apply one_div_le_one_div_of_le (by norm_num)
    exact le_self_pow₀ (by norm_num) (PNat.ne_zero n)
  let Ω : Set (LPInput m N) := {ι | ι = inp (1 / 2) (1 / 2) ∨ (∃ n, ι = inp (1 / 2 + δ n) (1 / 2)) ∨
    ∃ n, ι = inp (1 / 2) (1 / 2 + δ n)}
  have hentry : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → ∀ i j, |lpMatrixA a b m N i j| ≤ 1 := by
    intro a b ha ha' hb hb' i j
    simp only [lpMatrixA]
    split_ifs <;> simp [abs_le] <;> constructor <;> linarith
  have hgood : ∀ a b : ℝ, 0 < a → a ≤ 1 → 0 < b → b ≤ 1 →
      (lpArgmin (fun _ => 1) (inp a b).1 (inp a b).2).Nonempty ∧ (∀ i, |(inp a b).1 i| ≤ 2) ∧
        (∀ i j, |(inp a b).2 i j| ≤ 1) ∧ ∃ i j, |(inp a b).2 i j| = 1 := by
    intro a b ha ha' hb hb'
    refine ⟨?_, fun i => ?_, hentry a b ha.le ha' hb.le hb', ⟨0, by omega⟩, ⟨2, by omega⟩, ?_⟩
    · rcases le_total b a with h | h
      · exact ⟨_, argmin0 hm hmN a b ha hb.le h⟩
      · exact ⟨_, argmin1 hm hmN a b hb ha.le h⟩
    · simp only [inp, lpVectorA]; split_ifs <;> norm_num
    · simp [inp, lpMatrixA]
  have hΩ : ∀ ι ∈ Ω, (lpArgmin (fun _ => 1) ι.1 ι.2).Nonempty ∧ (∀ i, |ι.1 i| ≤ 2) ∧
      (∀ i j, |ι.2 i j| ≤ 1) ∧ ∃ i j, |ι.2 i j| = 1 := by
    rintro ι (h | ⟨n, h⟩ | ⟨n, h⟩) <;> subst h
    · exact hgood _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have := hδ n; have := hδ' n
      exact hgood _ _ (by linarith) (by linarith) (by norm_num) (by norm_num)
    · have := hδ n; have := hδ' n
      exact hgood _ _ (by norm_num) (by norm_num) (by linarith) (by linarith)
  let ι₀ : Ω := ⟨inp (1 / 2) (1 / 2), Or.inl rfl⟩
  let ι₁ : ℕ+ → Ω := fun n => ⟨inp (1 / 2 + δ n) (1 / 2), Or.inr (Or.inl ⟨n, rfl⟩)⟩
  let ι₂ : ℕ+ → Ω := fun n => ⟨inp (1 / 2) (1 / 2 + δ n), Or.inr (Or.inr ⟨n, rfl⟩)⟩
  let S₁ : Set (PiLp p (fun _ : Fin N => ℝ)) := {x | 4 / 3 ≤ x ⟨0, by omega⟩}
  let S₂ : Set (PiLp p (fun _ : Fin N => ℝ)) := {x | x ⟨0, by omega⟩ ≤ 0}
  have hsep : ∀ x₁ ∈ S₁, ∀ x₂ ∈ S₂, (1 : ℝ) ≤ dist x₁ x₂ := by
    intro x₁ h₁ x₂ h₂
    have := PiLp.dist_apply_le x₁ x₂ ⟨0, by omega⟩
    rw [Real.dist_eq] at this
    simp only [S₁, S₂, Set.mem_setOf_eq] at h₁ h₂
    have : x₁ ⟨0, by omega⟩ - x₂ ⟨0, by omega⟩ ≤ |x₁ ⟨0, by omega⟩ - x₂ ⟨0, by omega⟩| :=
      le_abs_self _
    linarith
  have hΞ₁ : ∀ n, lpSolution p (ι₁ n).1 ⊆ S₁ := by
    rintro n x ⟨z, hz, rfl⟩
    simp only [S₁, Set.mem_setOf_eq, PiLp.toLp_apply]
    exact incl1 hm hmN (δ n) (hδ n) (hδ' n) z hz
  have hΞ₂ : ∀ n, lpSolution p (ι₂ n).1 ⊆ S₂ := by
    rintro n x ⟨z, hz, rfl⟩
    simp only [S₂, Set.mem_setOf_eq, PiLp.toLp_apply]
    exact incl2 hm hmN (δ n) (hδ n) z hz
  have hclose : ∀ (a b : ℝ) (n : ℕ+), |a - 1 / 2| ≤ δ n → |b - 1 / 2| ≤ δ n →
      ∀ k, ‖lpEval k (inp a b) - lpEval k (inp (1 / 2) (1 / 2))‖ ≤ 1 / 4 ^ (n : ℕ) := by
    intro a b n ha hb k
    rcases k with i | ⟨i, j⟩
    · simp [lpEval, inp]
    · simp only [lpEval, inp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simp only [lpMatrixA]
      split_ifs <;> simp_all [δ] <;> positivity
  have hc₁ : ∀ k n, ‖lpEval k (ι₁ n).1 - lpEval k ι₀.1‖ ≤ 1 / 4 ^ (n : ℕ) := fun k n =>
    hclose _ _ n (by simp [abs_of_pos (hδ n)]) (by simp; exact (hδ n).le) k
  have hc₂ : ∀ k n, ‖lpEval k (ι₂ n).1 - lpEval k ι₀.1‖ ≤ 1 / 4 ^ (n : ℕ) := fun k n =>
    hclose _ _ n (by simp; exact (hδ n).le) (by simp [abs_of_pos (hδ n)]) k
  obtain ⟨fhat, hfhat, hbr⟩ := SmaleAux.prop_10_5 (fun k (ι : Ω) => lpEval k ι.1)
    (fun ι : Ω => lpSolution p ι.1) ι₁ ι₂ S₁ S₂ 1 one_pos hsep hΞ₁ hΞ₂ ι₀ hc₁ hc₂
  refine ⟨Ω, ⟨_, ι₀.2⟩, hΩ, fhat, hfhat, lt_of_lt_of_le ?_ hbr⟩
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  have h1 : (10 : ℝ) ^ (-(K : ℤ)) ≤ 10 ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (10 : ℝ) ^ (-1 : ℤ) = 1 / 10 := by norm_num
  calc (10 : ℝ) ^ (-(K : ℤ)) ≤ 10 ^ (-1 : ℤ) := h1
    _ = 1 / 10 := h2
    _ < 1 / 2 := by norm_num
