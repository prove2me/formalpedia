-- Prove2me | solution 1 for mme_stothers_phi233_finite_extraction_tau_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T08:34:15.447529+00:00
-- url     : https://prove2.me/submissions/fa760f76-bb94-449c-8d15-7d13edb8f457

import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Definitions.Def_mme_stothers_phi233_hash_state_instances
import Theorems.Thm_mme_stothers_phi233_ambient_star_crude_bounds
import Theorems.Thm_mme_stothers_phi233_below_two_thirds_value_below
import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_actual_degree_isolated_extraction
import Theorems.Thm_mme_stothers_phi233_cyclic_mode_word_tuple_injective
import Theorems.Thm_mme_stothers_phi233_behrend_prime_of_ambient_degree
import Theorems.Thm_mme_stothers_phi233_profile_surplus_of_EHL_order
import Theorems.Thm_mme_stothers_phi233_isolated_kept_profile_value
import Theorems.Thm_mme_stothers_phi233_exact_profile_product_cyclic_value_below
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions

open MME BigOperators Filter
open MME.StothersFourth.Phi233

universe u
set_option autoImplicit false

private theorem phi233_isolated_of_supported_diagonal
    {N alpha beta gamma delta : ℕ}
    (kept : Finset (CyclicAmbientEdge N alpha beta gamma delta))
    (hdiag : ∀ x y z : kept,
      CyclicCoordinatewiseSupported x.1 y.1 z.1 → x = y ∧ y = z) :
    ∀ e : CyclicAmbientEdge N alpha beta gamma delta,
      (∀ i : Fin 3, ∃ f ∈ kept, cyclicModeWord e i = cyclicModeWord f i) →
      e ∈ kept := by
  intro e he
  obtain ⟨x, hx, h0⟩ := he 0
  obtain ⟨y, hy, h1⟩ := he 1
  obtain ⟨z, hz, h2⟩ := he 2
  have hm0 : mixedAddress x.1 y.1 z.1 = e.1.1 := by
    funext i j
    fin_cases i
    · exact (congrFun (congrArg Prod.fst h0) j).symm
    · exact (congrFun (congrArg Prod.fst h1) j).symm
    · exact (congrFun (congrArg Prod.fst h2) j).symm
  have hm1 : mixedAddress y.2.1 z.2.1 x.2.1 = e.2.1.1 := by
    funext i j
    fin_cases i
    · exact (congrFun (congrArg (fun w => w.2.1) h1) j).symm
    · exact (congrFun (congrArg (fun w => w.2.1) h2) j).symm
    · exact (congrFun (congrArg (fun w => w.2.1) h0) j).symm
  have hm2 : mixedAddress z.2.2 x.2.2 y.2.2 = e.2.2.1 := by
    funext i j
    fin_cases i
    · exact (congrFun (congrArg (fun w => w.2.2) h2) j).symm
    · exact (congrFun (congrArg (fun w => w.2.2) h0) j).symm
    · exact (congrFun (congrArg (fun w => w.2.2) h1) j).symm
  have hs : CyclicCoordinatewiseSupported x y z := by
    unfold CyclicCoordinatewiseSupported
    rw [hm0, hm1, hm2]
    exact ⟨e.1.2.1, e.2.1.2.1, e.2.2.2.1⟩
  obtain ⟨hxy, hyz⟩ := hdiag ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ hs
  have hyx : y = x := (congrArg Subtype.val hxy).symm
  have hzx : z = x := (congrArg Subtype.val hyz).symm.trans hyx
  subst y
  subst z
  have hex : e = x := mme_stothers_phi233_cyclic_mode_word_tuple_injective (by
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2)
  simpa only [hex] using hx

private theorem phi233_weighted_retention_bound
    (P D F S C M B V : ℝ)
    (hP : 0 < P) (hD : 0 < D) (hF : 0 < F)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hprime : P ≤ D * F)
    (hlabels : 6 * D ≤ S)
    (hkept : C * (S / (2 * P ^ 2)) ≤ M)
    (hbudget : V * D * F ^ 2 < C * B) :
    V < M * B := by
  have hp2 : 0 < 2 * P ^ 2 := by positivity
  have hcount : C * S ≤ M * (2 * P ^ 2) := by
    apply (div_le_iff₀ hp2).mp
    simpa only [mul_div_assoc] using hkept
  have hleft : 6 * D * C ≤ M * (2 * P ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlabels hC
    nlinarith
  have hsq : P ^ 2 ≤ (D * F) ^ 2 :=
    pow_le_pow_left₀ hP.le hprime 2
  have hright : M * (2 * P ^ 2) ≤ M * (2 * (D * F) ^ 2) := by
    gcongr
  have hboth := hleft.trans hright
  have hmargin : C ≤ M * (D * F ^ 2) := by
    nlinarith [mul_pos hD hF]
  have hweighted := mul_le_mul_of_nonneg_right hmargin hB
  have hpos : 0 < D * F ^ 2 := by positivity
  apply (mul_lt_mul_iff_left₀ hpos).mp
  nlinarith

private theorem phi233_finite_extraction_of_order
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (hEpos : 0 < MME.StothersFourth.E 6 tau)
    (hEH : MME.StothersFourth.E 6 tau < MME.StothersFourth.H 6 tau)
    (hHL : MME.StothersFourth.H 6 tau < MME.StothersFourth.L 6 tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  classical
  obtain ⟨N, alpha, beta, gamma, delta, hN, hsum, a, hsurplus⟩ :=
    mme_stothers_phi233_profile_surplus_of_EHL_order
      tau hEpos hEH hHL V hV hVlt
  let D : ℝ := ∏ l : Fin 3,
    (Nat.card {b : MarginalAddress N alpha beta gamma delta //
      b.1 l = a.1.1 l} : ℝ)
  let F : ℝ := Real.exp (2000 * Real.sqrt (((18 * N + 1 : ℕ) : ℝ)))
  let C : ℝ := (targetFinset N alpha beta gamma delta).card
  let B : ℝ := ∏ r : Fin 10,
          (![MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau] :
                Fin 10 → ℝ) r ^
            MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r
  have hD1 : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast (mme_stothers_phi233_ambient_star_crude_bounds
      N alpha beta gamma delta a).1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hF : 0 < F := Real.exp_pos _
  have hB : 0 ≤ B := by
    apply Finset.prod_nonneg
    intro r _
    apply pow_nonneg
    fin_cases r <;> dsimp <;>
      simp only [MME.StothersFourth.E, MME.StothersFourth.H,
        MME.StothersFourth.L] <;> positivity
  have hC : 0 ≤ C := Nat.cast_nonneg _
  obtain ⟨p, hp, hp7, S, hSfree, hSbig, hpbound⟩ :=
    mme_stothers_phi233_behrend_prime_of_ambient_degree N alpha beta gamma delta a
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, kept, hkept, _, hmode, hdiag, hcount⟩ :=
    mme_stothers_phi233_actual_degree_isolated_extraction hp7 hsum a S hSfree hSbig
  have htarget : kept ⊆ targetFinset N alpha beta gamma delta := by
    intro e he
    exact (Finset.mem_filter.mp (hkept he)).1
  have hisolated : ∀ e ∈ ambientFinset N alpha beta gamma delta,
      (∀ i : Fin 3, ∃ f ∈ kept, cyclicModeWord e i = cyclicModeWord f i) →
      e ∈ kept := by
    intro e _ he
    exact phi233_isolated_of_supported_diagonal kept hdiag e he
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hF2 : F ^ 2 = Real.exp (4000 * Real.sqrt (((18 * N + 1 : ℕ) : ℝ))) := by
    dsimp [F]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hscalar : V ^ (2 * N) * D * F ^ 2 < C * B := by
    rw [hF2]
    exact hsurplus
  have hvalue : V ^ (2 * N) < (kept.card : ℝ) * B := by
    apply phi233_weighted_retention_bound (p : ℝ) D F (S.card : ℝ)
      C (kept.card : ℝ) B (V ^ (2 * N)) hP hD hF hC
      (Nat.cast_nonneg _) hB hpbound hSbig
    · simpa only [Nat.cast_pow] using hcount
    · exact hscalar
  have hpower : HasTauValueAtLeast
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)).kronPow
          (2 * N)) tau (V ^ (2 * N)) := by
    apply mme_stothers_phi233_isolated_kept_profile_value 6 kept htarget
      hisolated hmode tau B hB
    · intro W hW hWB
      exact mme_stothers_phi233_exact_profile_product_cyclic_value_below
        tau htauLower alpha beta gamma delta W hW hWB
    · exact pow_nonneg hV _
    · exact hvalue
  have hbase := mme_HasTauValueAtLeast_kronPow_root
    (cyclicSymmetrization (MME.StothersFourth.cwFourthConstituent K 6 2 3 3))
    tau V (2 * N) (by omega) hV hpower
  obtain ⟨s, loss, hs, hloss, _, hfinite⟩ :=
    mme_HasTauValueAtLeast_to_cofinal_finite_extractions _ tau V hbase
  exact ⟨s, loss, hs, hloss, Filter.Eventually.of_forall hfinite⟩

open MME.StothersFourth

/-- The ordered component regime persists up to exponent eight. -/
theorem phi233_EHL_order_up_to_eight (tau : ℝ)
    (htau : 0 < tau) (hupper : tau ≤ 8) :
    0 < E 6 tau ∧ E 6 tau < H 6 tau ∧ H 6 tau < L 6 tau := by
  have ht : 0 < 3 * tau := by linarith
  have hE : 0 < E 6 tau := by unfold E; positivity
  have hEH : E 6 tau < H 6 tau := by
    norm_num [E, H]
    exact Real.rpow_lt_rpow (by norm_num) (by norm_num) ht
  have hratio : (38 / 36 : ℝ) ^ (3 * tau) < 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 38 / 36) (show 3 * tau ≤ 24 by linarith)
    have h24 : (38 / 36 : ℝ) ^ (24 : ℝ) < 4 := by norm_num
    exact h.trans_lt h24
  have h36 : 0 < (36 : ℝ) ^ (3 * tau) := by positivity
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 38)
    (by norm_num : (0 : ℝ) ≤ 36)] at hratio
  have hHbound := (div_lt_iff₀ h36).mp hratio
  have h36eq : (36 : ℝ) ^ (3 * tau) = ((6 : ℝ) ^ (3 * tau)) ^ 2 := by
    rw [show (36 : ℝ) = 6 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 6),
      mul_comm, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 6)]
  refine ⟨hE, hEH, ?_⟩
  norm_num [H, L] at hHbound ⊢
  rw [h36eq] at hHbound
  nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (3 * tau)]


/-- Cofinal finite extraction throughout the full exponent range up to eight. -/
theorem solution
    {K : Type u} [Field K] (tau : ℝ) (htau : tau ≤ 8) (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)  := by
  by_cases hlower : 3 * tau ≤ 2
  · have hv := mme_stothers_phi233_below_two_thirds_value_below
      (K := K) tau V hlower hV hVlt
    obtain ⟨s, loss, hs, hloss, _, hfinite⟩ :=
      mme_HasTauValueAtLeast_to_cofinal_finite_extractions _ tau V hv
    exact ⟨s, loss, hs, hloss, Filter.Eventually.of_forall hfinite⟩
  · obtain ⟨hE, hEH, hHL⟩ := phi233_EHL_order_up_to_eight tau (by linarith) htau
    exact phi233_finite_extraction_of_order tau (by linarith) hE hEH hHL V hV hVlt

