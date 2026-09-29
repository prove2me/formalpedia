-- Prove2me | solution 1 for mme_stothers_phi233_marginal_address_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:27:43.755942+00:00
-- url     : https://prove2.me/submissions/c27f65c4-2e34-4381-a757-dcfe5db19a1b

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_phi233_pattern_injective
import Theorems.Thm_mme_stothers_phi233_full_same_marginal_entropy_maximum
import Theorems.Thm_mme_stothers_phi233_integer_histogram_normalization
import Theorems.Thm_mme_stothers_phi233_marginal_address_label_histogram
import Theorems.Thm_mme_finite_word_family_histogram_entropy_upper

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L)
    (hsigma : ((2 * alpha + beta : ℕ) : ℝ) / (N : ℝ) =
      2 * H / (2 * H + L))
    (hmu : ((alpha + gamma : ℕ) : ℝ) / (N : ℝ) =
      E / (E + L)) :
    ∃ a b c d : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = 2 * H / (2 * H + L) ∧
      a + c = E / (E + L) ∧
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        (((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N : ℕ) : ℝ) *
            (4 * Real.negMulLog (a / 2) +
              2 * Real.negMulLog (b / 2) +
              2 * Real.negMulLog (c / 2) +
              2 * Real.negMulLog (d / 2))) := by
  classical
  let ftProfile : Fintype
      (MME.StothersFourth.Phi233.ProfileAddress N) := Pi.instFintype
  letI : Fintype
      (MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) :=
    @Subtype.fintype _ _ (Classical.decPred _) ftProfile
  obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd, hab, hac, hmax⟩ :=
    mme_stothers_phi233_full_same_marginal_entropy_maximum
      E H L hE hH hEL hHL
  refine ⟨a, b, c, d, ha, hb, hc, hd, habcd, hab, hac, ?_⟩
  let labelAt
      (x : MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) (j : Fin (2 * N)) : Fin 10 :=
    Classical.choose (x.2.1 j)
  have hlabelAt : ∀
      (x : MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) (i : Fin 3) (j : Fin (2 * N)),
      x.1 i j =
        MME.StothersFourth.Phi233.pattern (labelAt x j) i := by
    intro x i j
    exact congrFun (Classical.choose_spec (x.2.1 j)) i
  have hlabelInjective : Function.Injective labelAt := by
    intro x y hxy
    apply Subtype.ext
    funext i j
    rw [hlabelAt x i j, hxy, ← hlabelAt y i j]
  let F : Finset (Fin (2 * N) → Fin 10) :=
    Finset.univ.image labelAt
  have hFcard : F.card =
      Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) := by
    calc
      F.card =
          (Finset.univ : Finset
            (MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta)).card := by
        exact Finset.card_image_of_injective _ hlabelInjective
      _ = Fintype.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) := Finset.card_univ
      _ = Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) := Nat.card_eq_fintype_card.symm
  let T : ℝ :=
    4 * Real.negMulLog (a / 2) +
      2 * Real.negMulLog (b / 2) +
      2 * Real.negMulLog (c / 2) +
      2 * Real.negMulLog (d / 2)
  have hEntropy : ∀ f ∈ F,
      mme_modern_entropyBits
          (fun r ↦
            (Fintype.card {t : Fin (2 * N) // f t = r} : ℝ) /
              ((2 * N : ℕ) : ℝ)) ≤ T / Real.log 2 := by
    intro f hf
    obtain ⟨x, _hxUniv, hxf⟩ := Finset.mem_image.mp hf
    subst f
    obtain ⟨g, hgcoord, hgtotal, hgsigma0, hgsigma2,
        hgmuJ0, hgmuJ3, hgmuK0, hgmuK3⟩ :=
      mme_stothers_phi233_marginal_address_label_histogram
        N alpha beta gamma delta x
    have hgeq : g = labelAt x := by
      funext j
      apply mme_stothers_phi233_pattern_injective
      funext i
      exact (hgcoord i j).symm.trans (hlabelAt x i j)
    subst g
    let w : Fin 10 → ℕ := fun r ↦
      Fintype.card {t : Fin (2 * N) // labelAt x t = r}
    have hw : ∀ r : Fin 10,
        w r = ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun t ↦ labelAt x t = r)).card := by
      intro r
      dsimp only [w]
      exact Fintype.card_subtype (fun t : Fin (2 * N) ↦ labelAt x t = r)
    have hwtotal : (∑ r : Fin 10, w r) = 2 * N := by
      calc
        (∑ r : Fin 10, w r) =
            ∑ r : Fin 10,
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun t ↦ labelAt x t = r)).card := by
          exact Finset.sum_congr rfl (fun r _ ↦ hw r)
        _ = 2 * N := hgtotal
    have hwsigma0 : w 0 + w 1 + w 2 = 2 * alpha + beta := by
      rw [hw 0, hw 1, hw 2]
      exact hgsigma0
    have hwsigma2 : w 7 + w 8 + w 9 = 2 * alpha + beta := by
      rw [hw 7, hw 8, hw 9]
      exact hgsigma2
    have hwmuJ0 : w 3 + w 7 = alpha + gamma := by
      rw [hw 3, hw 7]
      exact hgmuJ0
    have hwmuJ3 : w 2 + w 6 = alpha + gamma := by
      rw [hw 2, hw 6]
      exact hgmuJ3
    have hwmuK0 : w 6 + w 9 = alpha + gamma := by
      rw [hw 6, hw 9]
      exact hgmuK0
    have hwmuK3 : w 0 + w 3 = alpha + gamma := by
      rw [hw 0, hw 3]
      exact hgmuK3
    have hnorm := mme_stothers_phi233_integer_histogram_normalization
      N alpha beta gamma hN w hwtotal hwsigma0 hwsigma2
        hwmuJ0 hwmuJ3 hwmuK0 hwmuK3
    dsimp only at hnorm
    obtain ⟨hpNonneg, hpTotal, hpSigma0, hpSigma2,
      hpMuJ0, hpMuJ3, hpMuK0, hpMuK3⟩ := hnorm
    rw [hsigma] at hpSigma0 hpSigma2
    rw [hmu] at hpMuJ0 hpMuJ3 hpMuK0 hpMuK3
    have hpEntropy := hmax
      (fun r ↦ (w r : ℝ) / ((2 * N : ℕ) : ℝ))
      hpNonneg hpTotal hpSigma0 hpSigma2
      hpMuJ0 hpMuJ3 hpMuK0 hpMuK3
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbits := div_le_div_of_nonneg_right hpEntropy (le_of_lt hlog)
    simpa only [mme_modern_entropyBits, w, T] using hbits
  have hbound := mme_finite_word_family_histogram_entropy_upper
    (2 * N) (by omega) F (T / Real.log 2) hEntropy
  have hlogNe : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hexponent :
      (((2 * N : ℕ) : ℝ) * Real.log 2 * (T / Real.log 2)) =
        ((2 * N : ℕ) : ℝ) * T := by
    field_simp [hlogNe]
  rw [hexponent] at hbound
  rw [← hFcard]
  simpa only [Fintype.card_fin, T] using hbound
