-- Prove2me | solution 1 for mme_stothers_phi224_marginal_profile_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:29:38.109085+00:00
-- url     : https://prove2.me/submissions/95e80ed5-5e4f-4c8b-868d-dd3bcceff6c9

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_phi224_normalized_same_marginal_entropy_maximum
import Theorems.Thm_mme_finite_word_family_histogram_entropy_upper

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option warningAsError true

private theorem projectedFiberCard
    {N : ℕ} (w : MME.StothersFourth.Phi224.ProfileWord N)
    (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi224.modeWord w i j = s)).card =
      ∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ w j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) //
          MME.StothersFourth.Phi224.modeWord w i j = s} ≃
        Sigma fun r : {r : Fin 9 //
            MME.StothersFourth.Phi224.pattern r i = s} =>
          {j : Fin (2 * N) // w j = r.1} := {
    toFun j := ⟨⟨w j.1, j.2⟩, ⟨j.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by
      change MME.StothersFourth.Phi224.pattern (w x.2.1) i = s
      rw [x.2.2]
      exact x.1.2⟩
    left_inv j := by
      apply Subtype.ext
      rfl
    right_inv x := by
      rcases x with ⟨⟨r, hr⟩, ⟨j, hj⟩⟩
      cases hj
      rfl
  }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Fintype.card_subtype]

private theorem sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

theorem solution
    (N alpha beta gamma delta : ℕ) (hN : 0 < N) :
    (Nat.card
        (MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta) : ℝ) ≤
      (((2 * N + 1 : ℕ) : ℝ)) ^ 9 *
        Real.exp (((2 * N : ℕ) : ℝ) *
          (2 * Real.negMulLog
              ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
            4 * Real.negMulLog
              ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog
              ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
            Real.negMulLog
              (((2 * delta : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)))) := by
  classical
  let ftWord : Fintype (MME.StothersFourth.Phi224.ProfileWord N) :=
    Pi.instFintype
  letI : Fintype
      (MME.StothersFourth.Phi224.MarginalProfileWord
        N alpha beta gamma delta) :=
    @Subtype.fintype _ _ (Classical.decPred _) ftWord
  let value :
      MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta →
        (Fin (2 * N) → Fin 9) := Subtype.val
  have hvalueInjective : Function.Injective value := Subtype.val_injective
  let F : Finset (Fin (2 * N) → Fin 9) :=
    Finset.univ.image value
  have hFcard : F.card =
      Nat.card
        (MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta) := by
    calc
      F.card =
          (Finset.univ : Finset
            (MME.StothersFourth.Phi224.MarginalProfileWord
              N alpha beta gamma delta)).card :=
        Finset.card_image_of_injective _ hvalueInjective
      _ = Fintype.card
          (MME.StothersFourth.Phi224.MarginalProfileWord
            N alpha beta gamma delta) := Finset.card_univ
      _ = Nat.card
          (MME.StothersFourth.Phi224.MarginalProfileWord
            N alpha beta gamma delta) := Nat.card_eq_fintype_card.symm
  let T : ℝ :=
    2 * Real.negMulLog
        ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
      4 * Real.negMulLog
        ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
      2 * Real.negMulLog
        ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
      Real.negMulLog
        (((2 * delta : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ))
  have hEntropy : ∀ f ∈ F,
      mme_modern_entropyBits
          (fun r ↦
            (Fintype.card {t : Fin (2 * N) // f t = r} : ℝ) /
              ((2 * N : ℕ) : ℝ)) ≤ T / Real.log 2 := by
    intro f hf
    obtain ⟨x, hxUniv, hxf⟩ := Finset.mem_image.mp hf
    subst f
    let w : Fin 9 → ℕ := fun r ↦
      Fintype.card {t : Fin (2 * N) // x.1 t = r}
    have hw : ∀ r : Fin 9,
        w r =
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun t ↦ x.1 t = r)).card := by
      intro r
      dsimp only [w]
      exact Fintype.card_subtype (fun t : Fin (2 * N) ↦ x.1 t = r)
    have hwMarginal : ∀ i : Fin 3, ∀ s : Fin 5,
        (∑ r : Fin 9,
          if MME.StothersFourth.Phi224.pattern r i = s then w r else 0) =
            MME.StothersFourth.Phi224.marginalMultiplicity
              alpha beta gamma delta i s := by
      intro i s
      have h := x.2 i s
      rw [projectedFiberCard] at h
      rw [← sum_ite_eq_sum_subtype
        (fun r : Fin 9 ↦ MME.StothersFourth.Phi224.pattern r i) s
        (fun r ↦
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun t ↦ x.1 t = r)).card)] at h
      simpa only [hw] using h
    let p : Fin 9 → ℝ := fun r ↦
      (w r : ℝ) / ((2 * N : ℕ) : ℝ)
    have hpNonneg : ∀ r, 0 ≤ p r := by
      intro r
      dsimp only [p]
      positivity
    have hpMarginal : ∀ i : Fin 3, ∀ s : Fin 5,
        (∑ r : Fin 9,
          if MME.StothersFourth.Phi224.pattern r i = s then p r else 0) =
            (MME.StothersFourth.Phi224.marginalMultiplicity
              alpha beta gamma delta i s : ℝ) /
                ((2 * N : ℕ) : ℝ) := by
      intro i s
      calc
        (∑ r : Fin 9,
            if MME.StothersFourth.Phi224.pattern r i = s then p r else 0) =
            (∑ r : Fin 9,
              ((if MME.StothersFourth.Phi224.pattern r i = s
                then w r else 0 : ℕ) : ℝ)) /
                ((2 * N : ℕ) : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro r hr
          dsimp only [p]
          split_ifs <;> simp
        _ = (MME.StothersFourth.Phi224.marginalMultiplicity
              alpha beta gamma delta i s : ℝ) /
                ((2 * N : ℕ) : ℝ) := by
          rw [← Nat.cast_sum, hwMarginal]
    have hpEntropy :=
      mme_stothers_phi224_normalized_same_marginal_entropy_maximum
        N alpha beta gamma delta hN p hpNonneg hpMarginal
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbits := div_le_div_of_nonneg_right hpEntropy (le_of_lt hlog)
    simpa only [mme_modern_entropyBits, p, w, T] using hbits
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
