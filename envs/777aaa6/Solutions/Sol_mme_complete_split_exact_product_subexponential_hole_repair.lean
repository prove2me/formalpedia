-- Prove2me | solution 1 for mme_complete_split_exact_product_subexponential_hole_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:45:49.422195+00:00
-- url     : https://prove2.me/submissions/314233b7-b96f-46ee-97b8-935d6094fb63

import Theorems.Thm_mme_complete_split_exact_product_finite_hole_repair
import Theorems.Thm_mme_complete_split_exact_type_subexponential_repair_budget
import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_modern_three_mode_projected_tensor
import Definitions.Def_mme_tensor_quotient
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Filter MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.ModernRepair PiTensorProduct Module
open scoped BigOperators Classical

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem repair_depth_eventually (C : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∃ h : ℕ,
      3 ^ (C * N) < (2 * N) ^ h ∧
      Real.log ((8 ^ h : ℕ) : ℝ) < delta * N := by
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hn : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htwon : Tendsto (fun N : ℕ ↦ 2 * (N : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp htwon
  have hscale : Tendsto (fun N : ℕ ↦ delta * (N : ℝ)) atTop atTop :=
    hn.const_mul_atTop hdelta
  filter_upwards [eventually_ge_atTop 1,
    hlog.eventually (eventually_gt_atTop (2 * (C : ℝ) * Real.log 3 * Real.log 8 / delta)),
    hscale.eventually (eventually_gt_atTop (2 * Real.log 8))] with N hN hlarge hsmall
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hbase : 0 < Real.log (2 * (N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * N by omega))
  let x : ℝ := delta * (N : ℝ) / (2 * Real.log 8)
  let h : ℕ := Nat.ceil x
  have hx : 0 < x := by dsimp [x]; positivity
  have hlo : x ≤ (h : ℝ) := Nat.le_ceil x
  have hhi : (h : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
  have hstrict : ((C * N : ℕ) : ℝ) * Real.log 3 <
      (h : ℝ) * Real.log (2 * (N : ℝ)) := by
    calc
      _ = x * (2 * (C : ℝ) * Real.log 3 * Real.log 8 / delta) := by
        dsimp [x]
        push_cast
        field_simp
      _ < x * Real.log (2 * (N : ℝ)) := mul_lt_mul_of_pos_left hlarge hx
      _ ≤ _ := mul_le_mul_of_nonneg_right hlo hbase.le
  refine ⟨h, ?_, ?_⟩
  · have hr : ((3 ^ (C * N) : ℕ) : ℝ) < (((2 * N) ^ h : ℕ) : ℝ) := by
      apply (Real.log_lt_log_iff (by positivity) (by positivity)).1
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Real.log_pow] using hstrict
    exact_mod_cast hr
  · have hcost : (h : ℝ) * Real.log 8 < (x + 1) * Real.log 8 :=
      mul_lt_mul_of_pos_right hhi h8
    have hx8 : x * Real.log 8 = delta * (N : ℝ) / 2 := by
      dsimp [x]
      field_simp
    have hb : (h : ℝ) * Real.log 8 < delta * (N : ℝ) := by
      nlinarith
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using hb

private theorem product_exact_type_card_le (r ell : ℕ)
    (n : Fin r → ℕ) (beta : Fin r → Fin 3 → Profile ell) :
    (∏ i : Fin 3, Fintype.card
      (∀ t : Fin r, {w : PowIndex (CompleteWord ell) (n t) //
        ApproxConsistent id (beta t i) 0 w})) ≤
      3 ^ (3 * (2 ^ (ell - 1) * ∑ t, n t)) := by
  calc
    _ = ∏ t : Fin r, ∏ i : Fin 3,
        Fintype.card {w : PowIndex (CompleteWord ell) (n t) //
          ApproxConsistent id (beta t i) 0 w} := by
      simp only [Fintype.card_pi]
      rw [Finset.prod_comm]
    _ ≤ ∏ t : Fin r, 3 ^ (3 * (2 ^ (ell - 1)) * n t) := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun t _ ↦ (mme_complete_split_exact_type_subexponential_repair_budget ell).1
          (n t) (beta t))
    _ = _ := by
      rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, Nat.mul_assoc]

theorem solution
    {K : Type u} [Field K] {r : ℕ}
    (T : Fin r → TensorObj K 3) {I : Fin r → Fin 3 → Type u}
    (b : ∀ t i, Basis (I t i) K ((T t).V i)) {ell : ℕ}
    (label : ∀ t i, I t i → CompleteWord ell) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ M : ℕ in atTop,
      ∃ h : ℕ, Real.log ((8 ^ h : ℕ) : ℝ) < delta * M ∧
        ∀ n : Fin r → ℕ, 2 ^ (ell - 1) * (∑ t, n t) = M →
        ∀ beta : Fin r → Fin 3 → Profile ell,
          let Coord := fun t i ↦
            {w : PowIndex (I t i) (n t) //
              ApproxConsistent (label t i) (beta t i) 0 w}
          let Block := fun t i ↦
            {w : PowIndex (CompleteWord ell) (n t) //
              ApproxConsistent id (beta t i) 0 w}
          let Term := fun t ↦ restrictedPower (T t) (b t) (label t) (beta t) 0 (n t)
          let G := fun t ↦ ((T t).kronPow (n t)).basisAllAllowedGrading
            (fun i ↦ kronPowModeBasis (T t) i (b t i) (n t))
            (fun i ↦ ApproxConsistent (label t i) (beta t i) 0)
          let S := TensorObj.kronFin r Term
          ∃ B : ∀ t i, Basis (Coord t i) K ((Term t).V i),
          ∃ blockLabel : ∀ t i, Coord t i → Block t i,
            (∀ t i w, ((G t).classOf i 0).subtype (B t i w) =
              kronPowModeBasis (T t) i (b t i) (n t) w.1) ∧
            (∀ t i w, (blockLabel t i w).1 =
              PowIndex.ofFun (n t) (fun j ↦ label t i (PowIndex.get (n t) w.1 j))) ∧
            ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (∀ t : Fin r, Block t i),
              (∀ a i, 8 * M * (holes a i).card ≤
                Fintype.card (∀ t : Fin r, Block t i)) →
              TensorObj.Restrict S
                (TensorObj.bigAdd (fun a ↦ projected S
                  (fun i ↦ kronFinModePiBasis r Term i (fun t ↦ B t i))
                  (fun i w t ↦ blockLabel t i (w t))
                  (fun i ↦ Finset.univ \ holes a i))) := by
  classical
  intro delta hdelta
  filter_upwards [repair_depth_eventually 3 delta hdelta] with M hM
  obtain ⟨h, hthreshold, hcost⟩ := hM
  refine ⟨h, hcost, ?_⟩
  intro n hn beta
  obtain ⟨B, blockLabel, hB, hlabel, hrepair⟩ :=
    mme_complete_split_exact_product_finite_hole_repair T b label n beta
  refine ⟨B, blockLabel, hB, hlabel, ?_⟩
  intro holes hholes
  apply hrepair (2 * M) h
  · exact lt_of_le_of_lt
      (by simpa only [hn] using product_exact_type_card_le r ell n beta) hthreshold
  · intro a i
    convert hholes a i using 1
    ring
