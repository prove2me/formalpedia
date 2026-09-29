-- Prove2me | solution 1 for mme_dwz_fourth_coupled_cyclic_ledger_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:45:41.962623+00:00
-- url     : https://prove2.me/submissions/b043c172-08b9-4067-85cd-820e6a6490c4

import Definitions.Def_mme_dwz_fourth_q5_180_endpoint_bundle_data
import Definitions.Def_mme_dwz_fourth_coupled63_canonical_row_data
import Theorems.Thm_mme_dwz_fourth_coupled63_prescribedZ_six_values
import Theorems.Thm_mme_dwz_fourth_square_row_ledger_prescribedZ_adapter

open MME
open MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthPrescribedZ181
open MME.StothersFourth MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MME.DWZCoupledLedger

theorem profile_eq_of {t : ℕ} (p q : IntegerZSplitProfile t) (hd : p.denominator = q.denominator)
    (hc : p.count = q.count) : p = q := by
  cases p; cases q
  cases hd; cases hc
  rfl

/-- Move a coupled-row value along an equality of coarse addresses. -/
theorem transport (K : Type u) [Field K] (ρ ρ' : Fin 3 → Fin 5) (hρ : ρ = ρ')
    (p : IntegerZSplitProfile 3) (τ V : ℝ)
    (h : HasPrescribedZSixRestrictionValueAtLeast (CompleteSplitCanonicalSquare.obj K 5 ρ)
      (CompleteSplitCanonicalSquare.basis K 5 ρ 2)
      (fun x ↦ (CompleteSplitCanonicalSquare.label 5 ρ 2 x) 0) p τ V) :
    HasPrescribedZSixRestrictionValueAtLeast (CompleteSplitCanonicalSquare.obj K 5 ρ')
      (CompleteSplitCanonicalSquare.basis K 5 ρ' 2)
      (fun x ↦ (CompleteSplitCanonicalSquare.label 5 ρ' 2 x) 0) p τ V := by
  subst hρ
  exact h

theorem prof0 : HEq (componentZProfile ⟨28, by norm_num⟩) (Coupled63Scalar.profile ⟨0, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate0 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨28, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨0, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨28, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨0, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row0 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 28 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨28, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨28, by norm_num⟩ 1 1 2 rfl _ prof0 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate0)
    (transport K (Coupled63Scalar.rho ⟨0, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨0, by norm_num⟩))

theorem prof1 : HEq (componentZProfile ⟨29, by norm_num⟩) (Coupled63Scalar.profile ⟨1, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate1 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨29, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨1, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨29, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨1, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row1 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 29 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨29, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨29, by norm_num⟩ 1 2 1 rfl _ prof1 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate1)
    (transport K (Coupled63Scalar.rho ⟨1, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨1, by norm_num⟩))

theorem prof2 : HEq (componentZProfile ⟨30, by norm_num⟩) (Coupled63Scalar.profile ⟨2, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate2 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨30, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨2, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨30, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨2, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row2 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 30 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨30, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨30, by norm_num⟩ 2 1 1 rfl _ prof2 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate2)
    (transport K (Coupled63Scalar.rho ⟨2, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨2, by norm_num⟩))

theorem prof3 : HEq (componentZProfile ⟨33, by norm_num⟩) (Coupled63Scalar.profile ⟨3, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate3 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨33, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨3, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨33, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨3, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row3 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 33 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨33, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨33, by norm_num⟩ 1 1 2 rfl _ prof3 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate3)
    (transport K (Coupled63Scalar.rho ⟨3, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨3, by norm_num⟩))

theorem prof4 : HEq (componentZProfile ⟨34, by norm_num⟩) (Coupled63Scalar.profile ⟨4, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate4 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨34, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨4, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨34, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨4, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row4 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 34 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨34, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨34, by norm_num⟩ 1 2 1 rfl _ prof4 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate4)
    (transport K (Coupled63Scalar.rho ⟨4, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨4, by norm_num⟩))

theorem prof5 : HEq (componentZProfile ⟨36, by norm_num⟩) (Coupled63Scalar.profile ⟨5, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate5 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨36, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨5, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨36, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨5, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row5 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 36 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨36, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨36, by norm_num⟩ 2 1 1 rfl _ prof5 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate5)
    (transport K (Coupled63Scalar.rho ⟨5, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨5, by norm_num⟩))

theorem prof6 : HEq (componentZProfile ⟨40, by norm_num⟩) (Coupled63Scalar.profile ⟨6, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate6 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨40, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨6, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨40, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨6, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row6 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 40 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨40, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨40, by norm_num⟩ 1 1 2 rfl _ prof6 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate6)
    (transport K (Coupled63Scalar.rho ⟨6, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨6, by norm_num⟩))

theorem prof7 : HEq (componentZProfile ⟨41, by norm_num⟩) (Coupled63Scalar.profile ⟨7, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate7 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨41, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨7, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨41, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨7, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row7 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 41 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨41, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨41, by norm_num⟩ 1 2 1 rfl _ prof7 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate7)
    (transport K (Coupled63Scalar.rho ⟨7, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨7, by norm_num⟩))

theorem prof8 : HEq (componentZProfile ⟨43, by norm_num⟩) (Coupled63Scalar.profile ⟨8, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate8 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨43, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨8, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨43, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨8, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row8 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 43 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨43, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨43, by norm_num⟩ 2 1 1 rfl _ prof8 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate8)
    (transport K (Coupled63Scalar.rho ⟨8, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨8, by norm_num⟩))

theorem prof9 : HEq (componentZProfile ⟨47, by norm_num⟩) (Coupled63Scalar.profile ⟨9, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate9 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨47, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨9, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨47, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨9, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row9 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 47 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨47, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨47, by norm_num⟩ 1 1 2 rfl _ prof9 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate9)
    (transport K (Coupled63Scalar.rho ⟨9, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨9, by norm_num⟩))

theorem prof10 : HEq (componentZProfile ⟨48, by norm_num⟩) (Coupled63Scalar.profile ⟨10, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate10 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨48, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨10, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨48, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨10, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row10 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 48 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨48, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨48, by norm_num⟩ 1 2 1 rfl _ prof10 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate10)
    (transport K (Coupled63Scalar.rho ⟨10, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨10, by norm_num⟩))

theorem prof11 : HEq (componentZProfile ⟨50, by norm_num⟩) (Coupled63Scalar.profile ⟨11, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate11 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨50, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨11, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨50, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨11, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row11 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 50 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨50, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨50, by norm_num⟩ 2 1 1 rfl _ prof11 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate11)
    (transport K (Coupled63Scalar.rho ⟨11, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨11, by norm_num⟩))

theorem prof12 : HEq (componentZProfile ⟨54, by norm_num⟩) (Coupled63Scalar.profile ⟨12, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate12 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨54, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨12, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨54, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨12, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row12 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 54 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨54, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨54, by norm_num⟩ 1 1 2 rfl _ prof12 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate12)
    (transport K (Coupled63Scalar.rho ⟨12, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨12, by norm_num⟩))

theorem prof13 : HEq (componentZProfile ⟨55, by norm_num⟩) (Coupled63Scalar.profile ⟨13, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate13 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨55, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨13, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨55, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨13, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row13 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 55 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨55, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨55, by norm_num⟩ 1 2 1 rfl _ prof13 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate13)
    (transport K (Coupled63Scalar.rho ⟨13, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨13, by norm_num⟩))

theorem prof14 : HEq (componentZProfile ⟨57, by norm_num⟩) (Coupled63Scalar.profile ⟨14, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate14 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨57, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨14, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨57, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨14, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row14 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 57 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨57, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨57, by norm_num⟩ 2 1 1 rfl _ prof14 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate14)
    (transport K (Coupled63Scalar.rho ⟨14, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨14, by norm_num⟩))

theorem prof15 : HEq (componentZProfile ⟨60, by norm_num⟩) (Coupled63Scalar.profile ⟨15, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate15 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨60, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨15, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨60, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨15, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row15 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 60 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨60, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨60, by norm_num⟩ 1 1 2 rfl _ prof15 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate15)
    (transport K (Coupled63Scalar.rho ⟨15, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨15, by norm_num⟩))

theorem prof16 : HEq (componentZProfile ⟨61, by norm_num⟩) (Coupled63Scalar.profile ⟨16, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate16 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨61, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨16, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨61, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨16, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row16 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 61 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨61, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨61, by norm_num⟩ 1 2 1 rfl _ prof16 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate16)
    (transport K (Coupled63Scalar.rho ⟨16, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨16, by norm_num⟩))

theorem prof17 : HEq (componentZProfile ⟨62, by norm_num⟩) (Coupled63Scalar.profile ⟨17, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate17 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨62, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨17, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨62, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨17, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row17 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 62 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨62, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨62, by norm_num⟩ 2 1 1 rfl _ prof17 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate17)
    (transport K (Coupled63Scalar.rho ⟨17, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨17, by norm_num⟩))

theorem prof18 : HEq (componentZProfile ⟨67, by norm_num⟩) (Coupled63Scalar.profile ⟨18, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate18 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨67, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨18, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨67, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨18, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row18 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 67 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨67, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨67, by norm_num⟩ 1 1 2 rfl _ prof18 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate18)
    (transport K (Coupled63Scalar.rho ⟨18, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨18, by norm_num⟩))

theorem prof19 : HEq (componentZProfile ⟨68, by norm_num⟩) (Coupled63Scalar.profile ⟨19, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate19 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨68, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨19, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨68, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨19, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row19 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 68 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨68, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨68, by norm_num⟩ 1 2 1 rfl _ prof19 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate19)
    (transport K (Coupled63Scalar.rho ⟨19, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨19, by norm_num⟩))

theorem prof20 : HEq (componentZProfile ⟨70, by norm_num⟩) (Coupled63Scalar.profile ⟨20, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate20 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨70, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨20, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨70, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨20, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row20 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 70 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨70, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨70, by norm_num⟩ 2 1 1 rfl _ prof20 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate20)
    (transport K (Coupled63Scalar.rho ⟨20, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨20, by norm_num⟩))

theorem prof21 : HEq (componentZProfile ⟨74, by norm_num⟩) (Coupled63Scalar.profile ⟨21, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate21 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨74, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨21, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨74, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨21, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row21 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 74 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨74, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨74, by norm_num⟩ 1 1 2 rfl _ prof21 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate21)
    (transport K (Coupled63Scalar.rho ⟨21, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨21, by norm_num⟩))

theorem prof22 : HEq (componentZProfile ⟨75, by norm_num⟩) (Coupled63Scalar.profile ⟨22, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate22 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨75, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨22, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨75, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨22, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row22 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 75 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨75, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨75, by norm_num⟩ 1 2 1 rfl _ prof22 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate22)
    (transport K (Coupled63Scalar.rho ⟨22, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨22, by norm_num⟩))

theorem prof23 : HEq (componentZProfile ⟨77, by norm_num⟩) (Coupled63Scalar.profile ⟨23, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate23 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨77, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨23, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨77, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨23, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row23 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 77 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨77, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨77, by norm_num⟩ 2 1 1 rfl _ prof23 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate23)
    (transport K (Coupled63Scalar.rho ⟨23, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨23, by norm_num⟩))

theorem prof24 : HEq (componentZProfile ⟨81, by norm_num⟩) (Coupled63Scalar.profile ⟨24, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate24 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨81, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨24, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨81, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨24, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row24 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 81 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨81, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨81, by norm_num⟩ 1 1 2 rfl _ prof24 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate24)
    (transport K (Coupled63Scalar.rho ⟨24, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨24, by norm_num⟩))

theorem prof25 : HEq (componentZProfile ⟨82, by norm_num⟩) (Coupled63Scalar.profile ⟨25, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate25 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨82, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨25, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨82, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨25, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row25 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 82 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨82, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨82, by norm_num⟩ 1 2 1 rfl _ prof25 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate25)
    (transport K (Coupled63Scalar.rho ⟨25, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨25, by norm_num⟩))

theorem prof26 : HEq (componentZProfile ⟨84, by norm_num⟩) (Coupled63Scalar.profile ⟨26, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate26 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨84, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨26, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨84, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨26, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row26 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 84 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨84, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨84, by norm_num⟩ 2 1 1 rfl _ prof26 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate26)
    (transport K (Coupled63Scalar.rho ⟨26, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨26, by norm_num⟩))

theorem prof27 : HEq (componentZProfile ⟨88, by norm_num⟩) (Coupled63Scalar.profile ⟨27, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate27 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨88, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨27, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨88, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨27, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row27 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 88 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨88, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨88, by norm_num⟩ 1 1 2 rfl _ prof27 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate27)
    (transport K (Coupled63Scalar.rho ⟨27, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨27, by norm_num⟩))

theorem prof28 : HEq (componentZProfile ⟨89, by norm_num⟩) (Coupled63Scalar.profile ⟨28, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate28 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨89, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨28, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨89, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨28, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row28 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 89 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨89, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨89, by norm_num⟩ 1 2 1 rfl _ prof28 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate28)
    (transport K (Coupled63Scalar.rho ⟨28, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨28, by norm_num⟩))

theorem prof29 : HEq (componentZProfile ⟨91, by norm_num⟩) (Coupled63Scalar.profile ⟨29, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate29 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨91, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨29, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨91, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨29, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row29 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 91 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨91, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨91, by norm_num⟩ 2 1 1 rfl _ prof29 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate29)
    (transport K (Coupled63Scalar.rho ⟨29, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨29, by norm_num⟩))

theorem prof30 : HEq (componentZProfile ⟨95, by norm_num⟩) (Coupled63Scalar.profile ⟨30, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate30 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨95, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨30, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨95, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨30, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row30 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 95 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨95, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨95, by norm_num⟩ 1 1 2 rfl _ prof30 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate30)
    (transport K (Coupled63Scalar.rho ⟨30, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨30, by norm_num⟩))

theorem prof31 : HEq (componentZProfile ⟨96, by norm_num⟩) (Coupled63Scalar.profile ⟨31, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate31 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨96, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨31, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨96, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨31, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row31 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 96 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨96, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨96, by norm_num⟩ 1 2 1 rfl _ prof31 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate31)
    (transport K (Coupled63Scalar.rho ⟨31, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨31, by norm_num⟩))

theorem prof32 : HEq (componentZProfile ⟨98, by norm_num⟩) (Coupled63Scalar.profile ⟨32, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate32 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨98, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨32, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨98, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨32, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row32 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 98 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨98, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨98, by norm_num⟩ 2 1 1 rfl _ prof32 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate32)
    (transport K (Coupled63Scalar.rho ⟨32, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨32, by norm_num⟩))

theorem prof33 : HEq (componentZProfile ⟨104, by norm_num⟩) (Coupled63Scalar.profile ⟨33, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate33 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨104, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨33, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨104, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨33, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row33 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 104 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨104, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨104, by norm_num⟩ 1 1 2 rfl _ prof33 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate33)
    (transport K (Coupled63Scalar.rho ⟨33, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨33, by norm_num⟩))

theorem prof34 : HEq (componentZProfile ⟨105, by norm_num⟩) (Coupled63Scalar.profile ⟨34, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate34 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨105, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨34, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨105, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨34, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row34 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 105 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨105, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨105, by norm_num⟩ 1 2 1 rfl _ prof34 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate34)
    (transport K (Coupled63Scalar.rho ⟨34, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨34, by norm_num⟩))

theorem prof35 : HEq (componentZProfile ⟨107, by norm_num⟩) (Coupled63Scalar.profile ⟨35, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate35 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨107, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨35, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨107, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨35, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row35 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 107 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨107, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨107, by norm_num⟩ 2 1 1 rfl _ prof35 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate35)
    (transport K (Coupled63Scalar.rho ⟨35, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨35, by norm_num⟩))

theorem prof36 : HEq (componentZProfile ⟨111, by norm_num⟩) (Coupled63Scalar.profile ⟨36, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate36 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨111, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨36, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨111, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨36, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row36 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 111 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨111, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨111, by norm_num⟩ 1 1 2 rfl _ prof36 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate36)
    (transport K (Coupled63Scalar.rho ⟨36, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨36, by norm_num⟩))

theorem prof37 : HEq (componentZProfile ⟨112, by norm_num⟩) (Coupled63Scalar.profile ⟨37, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate37 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨112, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨37, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨112, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨37, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row37 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 112 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨112, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨112, by norm_num⟩ 1 2 1 rfl _ prof37 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate37)
    (transport K (Coupled63Scalar.rho ⟨37, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨37, by norm_num⟩))

theorem prof38 : HEq (componentZProfile ⟨114, by norm_num⟩) (Coupled63Scalar.profile ⟨38, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate38 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨114, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨38, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨114, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨38, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row38 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 114 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨114, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨114, by norm_num⟩ 2 1 1 rfl _ prof38 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate38)
    (transport K (Coupled63Scalar.rho ⟨38, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨38, by norm_num⟩))

theorem prof39 : HEq (componentZProfile ⟨118, by norm_num⟩) (Coupled63Scalar.profile ⟨39, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate39 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨118, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨39, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨118, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨39, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row39 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 118 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨118, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨118, by norm_num⟩ 1 1 2 rfl _ prof39 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate39)
    (transport K (Coupled63Scalar.rho ⟨39, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨39, by norm_num⟩))

theorem prof40 : HEq (componentZProfile ⟨119, by norm_num⟩) (Coupled63Scalar.profile ⟨40, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate40 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨119, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨40, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨119, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨40, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row40 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 119 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨119, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨119, by norm_num⟩ 1 2 1 rfl _ prof40 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate40)
    (transport K (Coupled63Scalar.rho ⟨40, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨40, by norm_num⟩))

theorem prof41 : HEq (componentZProfile ⟨121, by norm_num⟩) (Coupled63Scalar.profile ⟨41, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate41 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨121, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨41, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨121, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨41, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row41 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 121 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨121, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨121, by norm_num⟩ 2 1 1 rfl _ prof41 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate41)
    (transport K (Coupled63Scalar.rho ⟨41, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨41, by norm_num⟩))

theorem prof42 : HEq (componentZProfile ⟨125, by norm_num⟩) (Coupled63Scalar.profile ⟨42, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate42 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨125, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨42, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨125, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨42, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row42 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 125 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨125, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨125, by norm_num⟩ 1 1 2 rfl _ prof42 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate42)
    (transport K (Coupled63Scalar.rho ⟨42, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨42, by norm_num⟩))

theorem prof43 : HEq (componentZProfile ⟨126, by norm_num⟩) (Coupled63Scalar.profile ⟨43, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate43 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨126, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨43, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨126, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨43, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row43 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 126 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨126, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨126, by norm_num⟩ 1 2 1 rfl _ prof43 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate43)
    (transport K (Coupled63Scalar.rho ⟨43, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨43, by norm_num⟩))

theorem prof44 : HEq (componentZProfile ⟨128, by norm_num⟩) (Coupled63Scalar.profile ⟨44, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate44 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨128, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨44, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨128, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨44, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row44 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 128 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨128, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨128, by norm_num⟩ 2 1 1 rfl _ prof44 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate44)
    (transport K (Coupled63Scalar.rho ⟨44, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨44, by norm_num⟩))

theorem prof45 : HEq (componentZProfile ⟨134, by norm_num⟩) (Coupled63Scalar.profile ⟨45, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate45 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨134, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨45, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨134, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨45, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row45 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 134 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨134, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨134, by norm_num⟩ 1 1 2 rfl _ prof45 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate45)
    (transport K (Coupled63Scalar.rho ⟨45, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨45, by norm_num⟩))

theorem prof46 : HEq (componentZProfile ⟨135, by norm_num⟩) (Coupled63Scalar.profile ⟨46, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate46 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨135, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨46, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨135, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨46, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row46 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 135 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨135, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨135, by norm_num⟩ 1 2 1 rfl _ prof46 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate46)
    (transport K (Coupled63Scalar.rho ⟨46, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨46, by norm_num⟩))

theorem prof47 : HEq (componentZProfile ⟨137, by norm_num⟩) (Coupled63Scalar.profile ⟨47, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate47 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨137, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨47, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨137, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨47, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row47 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 137 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨137, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨137, by norm_num⟩ 2 1 1 rfl _ prof47 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate47)
    (transport K (Coupled63Scalar.rho ⟨47, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨47, by norm_num⟩))

theorem prof48 : HEq (componentZProfile ⟨141, by norm_num⟩) (Coupled63Scalar.profile ⟨48, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate48 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨141, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨48, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨141, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨48, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row48 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 141 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨141, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨141, by norm_num⟩ 1 1 2 rfl _ prof48 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate48)
    (transport K (Coupled63Scalar.rho ⟨48, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨48, by norm_num⟩))

theorem prof49 : HEq (componentZProfile ⟨142, by norm_num⟩) (Coupled63Scalar.profile ⟨49, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate49 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨142, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨49, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨142, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨49, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row49 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 142 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨142, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨142, by norm_num⟩ 1 2 1 rfl _ prof49 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate49)
    (transport K (Coupled63Scalar.rho ⟨49, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨49, by norm_num⟩))

theorem prof50 : HEq (componentZProfile ⟨144, by norm_num⟩) (Coupled63Scalar.profile ⟨50, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate50 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨144, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨50, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨144, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨50, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row50 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 144 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨144, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨144, by norm_num⟩ 2 1 1 rfl _ prof50 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate50)
    (transport K (Coupled63Scalar.rho ⟨50, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨50, by norm_num⟩))

theorem prof51 : HEq (componentZProfile ⟨148, by norm_num⟩) (Coupled63Scalar.profile ⟨51, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate51 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨148, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨51, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨148, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨51, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row51 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 148 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨148, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨148, by norm_num⟩ 1 1 2 rfl _ prof51 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate51)
    (transport K (Coupled63Scalar.rho ⟨51, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨51, by norm_num⟩))

theorem prof52 : HEq (componentZProfile ⟨149, by norm_num⟩) (Coupled63Scalar.profile ⟨52, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate52 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨149, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨52, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨149, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨52, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row52 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 149 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨149, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨149, by norm_num⟩ 1 2 1 rfl _ prof52 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate52)
    (transport K (Coupled63Scalar.rho ⟨52, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨52, by norm_num⟩))

theorem prof53 : HEq (componentZProfile ⟨151, by norm_num⟩) (Coupled63Scalar.profile ⟨53, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate53 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨151, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨53, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨151, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨53, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row53 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 151 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨151, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨151, by norm_num⟩ 2 1 1 rfl _ prof53 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate53)
    (transport K (Coupled63Scalar.rho ⟨53, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨53, by norm_num⟩))

theorem prof54 : HEq (componentZProfile ⟨157, by norm_num⟩) (Coupled63Scalar.profile ⟨54, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate54 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨157, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨54, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨157, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨54, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row54 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 157 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨157, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨157, by norm_num⟩ 1 1 2 rfl _ prof54 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate54)
    (transport K (Coupled63Scalar.rho ⟨54, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨54, by norm_num⟩))

theorem prof55 : HEq (componentZProfile ⟨158, by norm_num⟩) (Coupled63Scalar.profile ⟨55, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate55 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨158, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨55, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨158, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨55, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row55 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 158 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨158, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨158, by norm_num⟩ 1 2 1 rfl _ prof55 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate55)
    (transport K (Coupled63Scalar.rho ⟨55, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨55, by norm_num⟩))

theorem prof56 : HEq (componentZProfile ⟨160, by norm_num⟩) (Coupled63Scalar.profile ⟨56, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate56 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨160, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨56, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨160, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨56, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row56 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 160 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨160, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨160, by norm_num⟩ 2 1 1 rfl _ prof56 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate56)
    (transport K (Coupled63Scalar.rho ⟨56, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨56, by norm_num⟩))

theorem prof57 : HEq (componentZProfile ⟨164, by norm_num⟩) (Coupled63Scalar.profile ⟨57, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate57 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨164, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨57, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨164, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨57, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row57 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 164 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨164, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨164, by norm_num⟩ 1 1 2 rfl _ prof57 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate57)
    (transport K (Coupled63Scalar.rho ⟨57, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨57, by norm_num⟩))

theorem prof58 : HEq (componentZProfile ⟨165, by norm_num⟩) (Coupled63Scalar.profile ⟨58, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate58 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨165, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨58, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨165, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨58, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row58 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 165 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨165, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨165, by norm_num⟩ 1 2 1 rfl _ prof58 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate58)
    (transport K (Coupled63Scalar.rho ⟨58, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨58, by norm_num⟩))

theorem prof59 : HEq (componentZProfile ⟨167, by norm_num⟩) (Coupled63Scalar.profile ⟨59, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate59 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨167, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨59, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨167, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨59, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row59 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 167 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨167, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨167, by norm_num⟩ 2 1 1 rfl _ prof59 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate59)
    (transport K (Coupled63Scalar.rho ⟨59, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨59, by norm_num⟩))

theorem prof60 : HEq (componentZProfile ⟨172, by norm_num⟩) (Coupled63Scalar.profile ⟨60, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate60 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨172, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨60, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨172, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨60, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row60 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 172 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨172, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨172, by norm_num⟩ 1 1 2 rfl _ prof60 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate60)
    (transport K (Coupled63Scalar.rho ⟨60, by norm_num⟩) (cwSquareBlockType 1 1 2) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨60, by norm_num⟩))

theorem prof61 : HEq (componentZProfile ⟨173, by norm_num⟩) (Coupled63Scalar.profile ⟨61, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate61 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨173, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨61, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨173, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨61, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row61 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 173 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨173, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨173, by norm_num⟩ 1 2 1 rfl _ prof61 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate61)
    (transport K (Coupled63Scalar.rho ⟨61, by norm_num⟩) (cwSquareBlockType 1 2 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨61, by norm_num⟩))

theorem prof62 : HEq (componentZProfile ⟨174, by norm_num⟩) (Coupled63Scalar.profile ⟨62, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate62 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨174, by norm_num⟩ : ℚ) : ℝ) ≤
    ((Coupled63Scalar.rows ⟨62, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨174, by norm_num⟩ ≤
      (Coupled63Scalar.rows ⟨62, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row62 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 174 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨174, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨174, by norm_num⟩ 2 1 1 rfl _ prof62 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate62)
    (transport K (Coupled63Scalar.rho ⟨62, by norm_num⟩) (cwSquareBlockType 2 1 1) (by decide) _ _ _
      (mme_dwz_fourth_coupled63_prescribedZ_six_values K ⟨62, by norm_num⟩))

end MME.DWZCoupledLedger

theorem solution {K : Type u} [Field K] :
    DWZFourthQ5EndpointBundle.CoupledCyclicPrescribedZEndpoints K := by
  intro i hi
  have key : ∀ i : Fin 180, publicCoverageTier (componentSpecAt i) =
      PublicCoverageTier.square112ProfileTransport → i.val ∈ ([28, 29, 30, 33, 34, 36, 40, 41, 43, 47, 48, 50, 54, 55, 57, 60, 61, 62, 67, 68, 70, 74, 75, 77, 81, 82, 84, 88, 89, 91, 95, 96, 98, 104, 105, 107, 111, 112, 114, 118, 119, 121, 125, 126, 128, 134, 135, 137, 141, 142, 144, 148, 149, 151, 157, 158, 160, 164, 165, 167, 172, 173, 174] : List ℕ) := by
    decide +kernel
  have hm := key i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain rfl : i = ⟨28, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row0 K
  · obtain rfl : i = ⟨29, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row1 K
  · obtain rfl : i = ⟨30, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row2 K
  · obtain rfl : i = ⟨33, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row3 K
  · obtain rfl : i = ⟨34, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row4 K
  · obtain rfl : i = ⟨36, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row5 K
  · obtain rfl : i = ⟨40, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row6 K
  · obtain rfl : i = ⟨41, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row7 K
  · obtain rfl : i = ⟨43, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row8 K
  · obtain rfl : i = ⟨47, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row9 K
  · obtain rfl : i = ⟨48, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row10 K
  · obtain rfl : i = ⟨50, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row11 K
  · obtain rfl : i = ⟨54, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row12 K
  · obtain rfl : i = ⟨55, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row13 K
  · obtain rfl : i = ⟨57, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row14 K
  · obtain rfl : i = ⟨60, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row15 K
  · obtain rfl : i = ⟨61, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row16 K
  · obtain rfl : i = ⟨62, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row17 K
  · obtain rfl : i = ⟨67, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row18 K
  · obtain rfl : i = ⟨68, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row19 K
  · obtain rfl : i = ⟨70, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row20 K
  · obtain rfl : i = ⟨74, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row21 K
  · obtain rfl : i = ⟨75, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row22 K
  · obtain rfl : i = ⟨77, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row23 K
  · obtain rfl : i = ⟨81, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row24 K
  · obtain rfl : i = ⟨82, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row25 K
  · obtain rfl : i = ⟨84, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row26 K
  · obtain rfl : i = ⟨88, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row27 K
  · obtain rfl : i = ⟨89, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row28 K
  · obtain rfl : i = ⟨91, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row29 K
  · obtain rfl : i = ⟨95, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row30 K
  · obtain rfl : i = ⟨96, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row31 K
  · obtain rfl : i = ⟨98, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row32 K
  · obtain rfl : i = ⟨104, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row33 K
  · obtain rfl : i = ⟨105, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row34 K
  · obtain rfl : i = ⟨107, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row35 K
  · obtain rfl : i = ⟨111, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row36 K
  · obtain rfl : i = ⟨112, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row37 K
  · obtain rfl : i = ⟨114, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row38 K
  · obtain rfl : i = ⟨118, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row39 K
  · obtain rfl : i = ⟨119, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row40 K
  · obtain rfl : i = ⟨121, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row41 K
  · obtain rfl : i = ⟨125, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row42 K
  · obtain rfl : i = ⟨126, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row43 K
  · obtain rfl : i = ⟨128, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row44 K
  · obtain rfl : i = ⟨134, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row45 K
  · obtain rfl : i = ⟨135, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row46 K
  · obtain rfl : i = ⟨137, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row47 K
  · obtain rfl : i = ⟨141, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row48 K
  · obtain rfl : i = ⟨142, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row49 K
  · obtain rfl : i = ⟨144, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row50 K
  · obtain rfl : i = ⟨148, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row51 K
  · obtain rfl : i = ⟨149, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row52 K
  · obtain rfl : i = ⟨151, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row53 K
  · obtain rfl : i = ⟨157, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row54 K
  · obtain rfl : i = ⟨158, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row55 K
  · obtain rfl : i = ⟨160, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row56 K
  · obtain rfl : i = ⟨164, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row57 K
  · obtain rfl : i = ⟨165, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row58 K
  · obtain rfl : i = ⟨167, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row59 K
  · obtain rfl : i = ⟨172, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row60 K
  · obtain rfl : i = ⟨173, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row61 K
  · obtain rfl : i = ⟨174, by norm_num⟩ := Fin.ext h
    exact MME.DWZCoupledLedger.row62 K
