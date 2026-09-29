-- Prove2me | solution 1 for RademacherSymmetrization.radS_le_massart
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:23:35.196754+00:00
-- url     : https://prove2.me/submissions/b56f6fbb-a755-4b19-8d5c-8e1ca3cbfbca

-- Sol generated from Logic/Rademacher/Symmetrization.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Symmetrization
import Theorems.Thm_RademacherSymmetrization_radS_chernoff
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


lemma sgn_not (ε : Fin n → Bool) (i : Fin n) : sgn (fun j => !(ε j)) i = -sgn ε i := by
  simp only [sgn]
  rcases Bool.eq_false_or_eq_true (ε i) with h | h <;> simp [h]

lemma sum_sign_neg (g : (Fin n → Bool) → ℝ) :
    ∑ ε : Fin n → Bool, g (fun j => !(ε j)) = ∑ ε : Fin n → Bool, g ε := by
  refine Finset.sum_nbij' (fun ε => fun j => !(ε j)) (fun ε => fun j => !(ε j))
    ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp








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




omit [Fintype X] [DecidableEq X] in
/-- The optimal choice of the Chernoff parameter. -/
lemma optimal_lambda {c L s : ℝ} (hc : 0 < c) (hs : 0 < s) (hsq : s * s = 2 * L / c) :
    L / s + s * c / 2 = Real.sqrt (2 * L * c) := by
  have hL : L = s * s * c / 2 := by
    field_simp at hsq ⊢
    linarith [hsq]
  have hpos : 2 * L * c = (s * c) ^ 2 := by rw [hL]; ring
  rw [hpos, Real.sqrt_sq (by positivity)]
  rw [hL]
  field_simp
  ring





open RademacherSymmetrization in
omit [Fintype X] [DecidableEq X] in
theorem solution(hn : 0 < n) (F : Finset (X → ℝ)) (hne : F.Nonempty)
    (S : Fin n → X) {B : ℝ} (hbd : ∀ f ∈ F, ∀ x, |f x| ≤ B) :
    radS F hne S ≤ B * Real.sqrt (2 * Real.log F.card) / Real.sqrt n := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hBnn : 0 ≤ B := by
    obtain ⟨f, hf⟩ := hne
    exact le_trans (abs_nonneg (f (S ⟨0, hn⟩))) (hbd f hf (S ⟨0, hn⟩))
  by_cases hcard1 : F.card = 1
  · -- singleton class: the complexity vanishes
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard1
    have hzero : radS F hne S = 0 := by
      unfold radS
      have hmem : ∀ g ∈ F, g = f := by
        intro g hg
        rw [hf] at hg
        simpa using hg
      have hfF : f ∈ F := by rw [hf]; simp
      have hmax : ∀ ε : Fin n → Bool, maxCorr F hne ε S = corr ε S f := by
        intro ε
        unfold maxCorr
        refine le_antisymm (Finset.sup'_le _ _ fun g hg => ?_) (Finset.le_sup' (corr ε S) hfF)
        rw [hmem g hg]
      rw [Finset.sum_congr rfl fun ε _ => hmax ε]
      have : ∑ ε : Fin n → Bool, corr ε S f = 0 := by
        unfold corr
        rw [← Finset.mul_sum, Finset.sum_comm]
        have hz : ∀ i : Fin n, ∑ ε : Fin n → Bool, sgn ε i * f (S i) = 0 := by
          intro i
          rw [← Finset.sum_mul]
          have hsgn : ∑ ε : Fin n → Bool, sgn ε i = 0 := by
            have h := sum_sign_neg (fun ε => sgn ε i)
            simp only [sgn_not] at h
            rw [Finset.sum_neg_distrib] at h
            linarith
          rw [hsgn, zero_mul]
        simp [hz]
      rw [this]
      simp
    rw [hzero, hcard1]
    simp
  · have hcard2 : 2 ≤ F.card := by
      have := Finset.card_pos.mpr hne
      omega
    have hcardR : (2:ℝ) ≤ F.card := by exact_mod_cast hcard2
    have hlogpos : 0 < Real.log F.card := Real.log_pos (by linarith)
    rcases eq_or_lt_of_le hBnn with hB0 | hBpos
    · -- `B = 0` forces the class to be the single zero function
      exfalso
      have hzero : ∀ f ∈ F, f = 0 := by
        intro f hf
        funext x
        have := hbd f hf x
        rw [← hB0] at this
        simpa using abs_nonpos_iff.mp this
      have hsub : F ⊆ {0} := fun f hf => by simp [hzero f hf]
      have := Finset.card_le_card hsub
      simp at this
      omega
    · set L := Real.log F.card with hL
      set c := B ^ 2 / (n:ℝ) with hc
      have hcpos : 0 < c := by rw [hc]; positivity
      set l := Real.sqrt (2 * L / c) with hl
      have hlpos : 0 < l := Real.sqrt_pos.mpr (by positivity)
      have hsq : l * l = 2 * L / c := Real.mul_self_sqrt (by positivity)
      have hbound := radS_chernoff hn F hne S hlpos hbd
      have hval : L / l + l * c / 2 = Real.sqrt (2 * L * c) :=
        optimal_lambda hcpos hlpos hsq
      have hfinal : Real.sqrt (2 * L * c) = B * Real.sqrt (2 * L) / Real.sqrt n := by
        rw [hc]
        rw [show 2 * L * (B ^ 2 / (n:ℝ)) = (2 * L) * (B ^ 2 / (n:ℝ)) by ring]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity),
          Real.sqrt_sq hBnn]
        ring
      rw [hval, hfinal] at hbound
      exact hbound
