-- Prove2me | solution 1 for AlmostLossless.exists_list_scheme_exponential
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T10:15:05.159661+00:00
-- url     : https://prove2.me/submissions/671727cd-7c3c-4c3c-9558-b0ea83b682b9

import Mathlib
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
import Theorems.Thm_AlmostLossless_exists_list_scheme_indepT
set_option autoImplicit false
open Finset BigOperators NonArchInfoTheory AlmostLossless
variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

theorem solution (μ : FinProbDist α) {H : Fin K → α → Fin M}
    {T : ℕ} (hI : IndepT H T) (hK : 0 < K) (hM : 0 < M)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K,
      setMass μ (Finset.univ.filter
          (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
          ≤ δ + ((l.length : ℝ) / M) ^ T
      ∧ (∀ i : Fin M, ((listHashScheme T l (H k)).dec i).length ≤ T) := by
  obtain ⟨k, hfail, hlen, _⟩ :=
    exists_list_scheme_indepT μ hI hK hM l hnd δ hδ
  refine ⟨k, ?_, hlen⟩
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMT : (0 : ℝ) < (M : ℝ) ^ T := by positivity
  have hchoose : (l.length.choose T : ℝ) ≤ (l.length : ℝ) ^ T := by
    have : l.length.choose T ≤ l.length ^ T := Nat.choose_le_pow _ _
    exact_mod_cast this
  have : (l.length.choose T : ℝ) / (M : ℝ) ^ T ≤ ((l.length : ℝ) / M) ^ T := by
    rw [div_pow, div_le_div_iff_of_pos_right hMT]
    exact hchoose
  linarith

#print axioms solution
