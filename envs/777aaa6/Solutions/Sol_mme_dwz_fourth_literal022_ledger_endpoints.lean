-- Prove2me | solution 1 for mme_dwz_fourth_literal022_ledger_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:40:58.925205+00:00
-- url     : https://prove2.me/submissions/5902f366-0dd5-4560-a643-29c8d365a862

import Definitions.Def_mme_dwz_fourth_q5_180_endpoint_bundle_data
import Definitions.Def_mme_dwz_fourth_literal022_row_data
import Theorems.Thm_mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints
import Theorems.Thm_mme_dwz_fourth_square_row_ledger_prescribedZ_adapter

open MME
open MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthPrescribedZ181
open MME.StothersFourth MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MME.DWZLiteral022Ledger

theorem profile_eq_of {t : ℕ} (p q : IntegerZSplitProfile t) (hd : p.denominator = q.denominator)
    (hc : p.count = q.count) : p = q := by
  cases p; cases q
  cases hd; cases hc
  rfl

theorem prof0 : HEq (componentZProfile ⟨14, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨0, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate0 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨14, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨0, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨14, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨0, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row0 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 14 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨14, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨14, by norm_num⟩ 0 2 2 rfl _ prof0 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate0)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨0, by norm_num⟩)

theorem prof1 : HEq (componentZProfile ⟨32, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨1, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate1 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨32, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨1, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨32, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨1, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row1 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 32 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨32, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨32, by norm_num⟩ 0 2 2 rfl _ prof1 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate1)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨1, by norm_num⟩)

theorem prof2 : HEq (componentZProfile ⟨39, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨2, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate2 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨39, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨2, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨39, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨2, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row2 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 39 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨39, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨39, by norm_num⟩ 0 2 2 rfl _ prof2 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate2)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨2, by norm_num⟩)

theorem prof3 : HEq (componentZProfile ⟨46, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨3, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate3 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨46, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨3, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨46, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨3, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row3 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 46 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨46, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨46, by norm_num⟩ 0 2 2 rfl _ prof3 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate3)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨3, by norm_num⟩)

theorem prof4 : HEq (componentZProfile ⟨53, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨4, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate4 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨53, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨4, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨53, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨4, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row4 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 53 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨53, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨53, by norm_num⟩ 0 2 2 rfl _ prof4 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate4)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨4, by norm_num⟩)

theorem prof5 : HEq (componentZProfile ⟨66, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨5, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate5 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨66, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨5, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨66, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨5, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row5 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 66 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨66, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨66, by norm_num⟩ 0 2 2 rfl _ prof5 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate5)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨5, by norm_num⟩)

theorem prof6 : HEq (componentZProfile ⟨73, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨6, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate6 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨73, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨6, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨73, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨6, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row6 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 73 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨73, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨73, by norm_num⟩ 0 2 2 rfl _ prof6 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate6)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨6, by norm_num⟩)

theorem prof7 : HEq (componentZProfile ⟨80, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨7, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate7 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨80, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨7, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨80, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨7, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row7 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 80 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨80, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨80, by norm_num⟩ 0 2 2 rfl _ prof7 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate7)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨7, by norm_num⟩)

theorem prof8 : HEq (componentZProfile ⟨87, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨8, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate8 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨87, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨8, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨87, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨8, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row8 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 87 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨87, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨87, by norm_num⟩ 0 2 2 rfl _ prof8 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate8)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨8, by norm_num⟩)

theorem prof9 : HEq (componentZProfile ⟨94, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨9, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate9 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨94, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨9, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨94, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨9, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row9 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 94 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨94, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨94, by norm_num⟩ 0 2 2 rfl _ prof9 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate9)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨9, by norm_num⟩)

theorem prof10 : HEq (componentZProfile ⟨103, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨10, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate10 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨103, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨10, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨103, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨10, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row10 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 103 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨103, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨103, by norm_num⟩ 0 2 2 rfl _ prof10 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate10)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨10, by norm_num⟩)

theorem prof11 : HEq (componentZProfile ⟨110, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨11, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate11 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨110, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨11, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨110, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨11, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row11 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 110 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨110, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨110, by norm_num⟩ 0 2 2 rfl _ prof11 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate11)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨11, by norm_num⟩)

theorem prof12 : HEq (componentZProfile ⟨117, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨12, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate12 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨117, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨12, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨117, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨12, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row12 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 117 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨117, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨117, by norm_num⟩ 0 2 2 rfl _ prof12 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate12)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨12, by norm_num⟩)

theorem prof13 : HEq (componentZProfile ⟨124, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨13, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate13 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨124, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨13, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨124, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨13, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row13 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 124 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨124, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨124, by norm_num⟩ 0 2 2 rfl _ prof13 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate13)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨13, by norm_num⟩)

theorem prof14 : HEq (componentZProfile ⟨133, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨14, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate14 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨133, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨14, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨133, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨14, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row14 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 133 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨133, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨133, by norm_num⟩ 0 2 2 rfl _ prof14 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate14)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨14, by norm_num⟩)

theorem prof15 : HEq (componentZProfile ⟨140, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨15, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate15 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨140, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨15, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨140, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨15, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row15 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 140 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨140, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨140, by norm_num⟩ 0 2 2 rfl _ prof15 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate15)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨15, by norm_num⟩)

theorem prof16 : HEq (componentZProfile ⟨147, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨16, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate16 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨147, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨16, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨147, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨16, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row16 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 147 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨147, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨147, by norm_num⟩ 0 2 2 rfl _ prof16 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate16)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨16, by norm_num⟩)

theorem prof17 : HEq (componentZProfile ⟨156, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨17, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate17 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨156, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨17, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨156, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨17, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row17 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 156 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨156, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨156, by norm_num⟩ 0 2 2 rfl _ prof17 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate17)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨17, by norm_num⟩)

theorem prof18 : HEq (componentZProfile ⟨163, by norm_num⟩) (ZEndpoint022PublicRows.profile ⟨18, by norm_num⟩) := by
  apply heq_of_eq
  apply profile_eq_of
  · decide +kernel
  · funext a
    fin_cases a <;> decide +kernel

theorem rate18 : ((DWZFourthPrescribedZ181.properLedgerRate ⟨163, by norm_num⟩ : ℚ) : ℝ) ≤
    ((ZEndpoint022PublicRows.rows ⟨18, by norm_num⟩).rate : ℝ) := by
  have h : DWZFourthPrescribedZ181.properLedgerRate ⟨163, by norm_num⟩ ≤
      (ZEndpoint022PublicRows.rows ⟨18, by norm_num⟩).rate := by decide +kernel
  exact_mod_cast h

theorem row18 (K : Type u) [Field K] :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) 163 (790643 / 1000000)
      (Real.exp (DWZFourthPrescribedZ181.properLedgerRate ⟨163, by norm_num⟩ : ℝ)) :=
  mme_dwz_fourth_square_row_ledger_prescribedZ_adapter K ⟨163, by norm_num⟩ 0 2 2 rfl _ prof18 _ _ _
    (Real.exp_pos _).le (Real.exp_le_exp.mpr rate18)
    (mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints K ⟨18, by norm_num⟩)

end MME.DWZLiteral022Ledger

theorem solution {K : Type u} [Field K] :
    DWZFourthQ5EndpointBundle.Literal022PrescribedZEndpoints K := by
  intro i hi
  have key : ∀ i : Fin 180, publicCoverageTier (componentSpecAt i) =
      PublicCoverageTier.square022PrescribedZ → i.val ∈ ([14, 32, 39, 46, 53, 66, 73, 80, 87, 94, 103, 110, 117, 124, 133, 140, 147, 156, 163] : List ℕ) := by
    decide +kernel
  have hm := key i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain rfl : i = ⟨14, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row0 K
  · obtain rfl : i = ⟨32, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row1 K
  · obtain rfl : i = ⟨39, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row2 K
  · obtain rfl : i = ⟨46, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row3 K
  · obtain rfl : i = ⟨53, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row4 K
  · obtain rfl : i = ⟨66, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row5 K
  · obtain rfl : i = ⟨73, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row6 K
  · obtain rfl : i = ⟨80, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row7 K
  · obtain rfl : i = ⟨87, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row8 K
  · obtain rfl : i = ⟨94, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row9 K
  · obtain rfl : i = ⟨103, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row10 K
  · obtain rfl : i = ⟨110, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row11 K
  · obtain rfl : i = ⟨117, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row12 K
  · obtain rfl : i = ⟨124, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row13 K
  · obtain rfl : i = ⟨133, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row14 K
  · obtain rfl : i = ⟨140, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row15 K
  · obtain rfl : i = ⟨147, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row16 K
  · obtain rfl : i = ⟨156, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row17 K
  · obtain rfl : i = ⟨163, by norm_num⟩ := Fin.ext h
    exact MME.DWZLiteral022Ledger.row18 K
