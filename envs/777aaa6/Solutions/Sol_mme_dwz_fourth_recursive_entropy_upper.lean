-- Prove2me | solution 1 for mme_dwz_fourth_recursive_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T07:13:06.497758+00:00
-- url     : https://prove2.me/submissions/d9c1aea8-45ee-41ca-8ed5-8ac849ded5c4

import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Theorems.Thm_mme_modern_entropyNat_upper_from_positive_reference
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open MME.DWZFourthRecursiveWitness BigOperators Finset
set_option autoImplicit false
set_option warningAsError true

private def seriesLengths : Fin 63 → List ℕ :=
  ![[7, 8, 8, 7], [5, 8, 8, 5], [5, 8, 8, 5], [6, 4, 3, 3, 4, 6], [5, 4, 5, 5, 4, 5], [5, 4, 4, 4, 4, 5], [2, 7, 6, 6, 6, 6, 7, 2], [3, 7, 7, 7, 7, 7, 8, 3], [1, 7, 6, 6, 6, 6, 7, 1], [6, 6, 3, 5, 5, 3, 6, 6], [3, 1, 7, 7, 7, 7, 1, 3], [6, 6, 2, 4, 4, 2, 6, 6], [5, 4, 7, 7, 4, 5], [5, 4, 7, 7, 4, 5], [3, 4, 5, 5, 5, 3], [5, 7, 7, 5], [7, 2, 2, 7], [5, 7, 7, 5], [6, 3, 4, 4, 3, 6], [5, 4, 4, 4, 4, 5], [5, 5, 4, 4, 5, 5], [2, 3, 3, 3, 3, 3, 3, 3, 2], [7, 3, 3, 3, 3, 3, 3, 3, 7], [3, 6, 5, 6, 6, 6, 5, 6, 3], [5, 4, 5, 6, 4, 4, 6, 5, 4, 5], [5, 4, 5, 6, 4, 4, 6, 5, 4, 5], [6, 5, 6, 6, 5, 5, 6, 6, 5, 6], [5, 6, 3, 6, 6, 6, 3, 6, 5], [3, 4, 5, 4, 3, 4, 5, 4, 3], [3, 4, 5, 4, 3, 4, 5, 4, 3], [5, 7, 4, 4, 7, 5], [5, 7, 4, 4, 7, 5], [4, 4, 4, 4, 4, 4], [2, 6, 7, 6, 6, 7, 6, 2], [1, 6, 7, 6, 6, 7, 6, 1], [3, 6, 7, 2, 7, 7, 6, 3], [6, 6, 6, 5, 5, 5, 5, 6, 6, 6], [6, 5, 5, 4, 4, 4, 4, 5, 5, 6], [6, 5, 5, 4, 4, 4, 4, 5, 5, 6], [5, 6, 4, 4, 5, 5, 4, 4, 6, 5], [5, 6, 4, 4, 5, 5, 4, 4, 6, 5], [5, 4, 7, 7, 5, 5, 7, 7, 4, 5], [2, 7, 2, 2, 2, 2, 7, 2], [6, 5, 6, 3, 3, 6, 5, 6], [6, 4, 6, 2, 2, 6, 4, 6], [5, 6, 3, 6, 6, 3, 6, 5], [4, 6, 2, 6, 6, 2, 6, 4], [5, 5, 7, 3, 2, 7, 5, 5], [5, 4, 4, 3, 3, 3, 4, 4, 5], [5, 4, 4, 3, 3, 3, 4, 4, 5], [3, 6, 6, 5, 6, 5, 6, 6, 3], [7, 2, 2, 2, 2, 2, 2, 7], [4, 2, 6, 6, 6, 6, 2, 4], [5, 3, 6, 6, 6, 6, 3, 5], [7, 5, 4, 4, 5, 7], [5, 2, 5, 4, 2, 5], [7, 5, 4, 4, 5, 7], [7, 4, 5, 5, 4, 7], [4, 4, 4, 4, 4, 4], [7, 4, 5, 5, 4, 7], [7, 5, 5, 7], [7, 5, 5, 7], [2, 7, 7, 2]]

private def seriesLength (r : Fin 63) (a : Fin (witness r).cellCount) : ℕ :=
  (seriesLengths r)[a.val]?.getD 0

private abbrev Certified (r : Fin 63) (a : Fin (witness r).cellCount) : Prop :=
  let q := (witness r).reference a
  let t := logParameter r a
  let k := (witness r).logScale a
  let n := seriesLength r a
  0 < q ∧ 0 ≤ t ∧ t < 1 ∧
  q * 2 ^ k = (1 + t) / (1 - t) ∧
  logLower r a + k * (69314718057 / 100000000000 : ℚ) ≤
    2 * ∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1) ∧
  2 * ((∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1)) +
    t ^ (2 * n + 1) / (1 - t ^ 2)) -
    k * (69314718055 / 100000000000 : ℚ) ≤ 0

private theorem cert_0_0 : Certified 0 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_0_1 : Certified 0 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_0_2 : Certified 0 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_0_3 : Certified 0 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_0 (a : Fin (witness 0).cellCount) : Certified 0 a := by
  fin_cases a
  · exact cert_0_0
  · exact cert_0_1
  · exact cert_0_2
  · exact cert_0_3

private theorem cert_1_0 : Certified 1 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_1_1 : Certified 1 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_1_2 : Certified 1 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_1_3 : Certified 1 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_1 (a : Fin (witness 1).cellCount) : Certified 1 a := by
  fin_cases a
  · exact cert_1_0
  · exact cert_1_1
  · exact cert_1_2
  · exact cert_1_3

private theorem cert_2_0 : Certified 2 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_2_1 : Certified 2 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_2_2 : Certified 2 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_2_3 : Certified 2 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_2 (a : Fin (witness 2).cellCount) : Certified 2 a := by
  fin_cases a
  · exact cert_2_0
  · exact cert_2_1
  · exact cert_2_2
  · exact cert_2_3

private theorem cert_3_0 : Certified 3 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_3_1 : Certified 3 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_3_2 : Certified 3 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_3_3 : Certified 3 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_3_4 : Certified 3 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_3_5 : Certified 3 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_3 (a : Fin (witness 3).cellCount) : Certified 3 a := by
  fin_cases a
  · exact cert_3_0
  · exact cert_3_1
  · exact cert_3_2
  · exact cert_3_3
  · exact cert_3_4
  · exact cert_3_5

private theorem cert_4_0 : Certified 4 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_4_1 : Certified 4 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_4_2 : Certified 4 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_4_3 : Certified 4 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_4_4 : Certified 4 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_4_5 : Certified 4 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_4 (a : Fin (witness 4).cellCount) : Certified 4 a := by
  fin_cases a
  · exact cert_4_0
  · exact cert_4_1
  · exact cert_4_2
  · exact cert_4_3
  · exact cert_4_4
  · exact cert_4_5

private theorem cert_5_0 : Certified 5 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_5_1 : Certified 5 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_5_2 : Certified 5 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_5_3 : Certified 5 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_5_4 : Certified 5 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_5_5 : Certified 5 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_5 (a : Fin (witness 5).cellCount) : Certified 5 a := by
  fin_cases a
  · exact cert_5_0
  · exact cert_5_1
  · exact cert_5_2
  · exact cert_5_3
  · exact cert_5_4
  · exact cert_5_5

private theorem cert_6_0 : Certified 6 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_6_1 : Certified 6 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_6_2 : Certified 6 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_6_3 : Certified 6 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_6_4 : Certified 6 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_6_5 : Certified 6 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_6_6 : Certified 6 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_6_7 : Certified 6 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_6 (a : Fin (witness 6).cellCount) : Certified 6 a := by
  fin_cases a
  · exact cert_6_0
  · exact cert_6_1
  · exact cert_6_2
  · exact cert_6_3
  · exact cert_6_4
  · exact cert_6_5
  · exact cert_6_6
  · exact cert_6_7

private theorem cert_7_0 : Certified 7 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_7_1 : Certified 7 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_7_2 : Certified 7 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_7_3 : Certified 7 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_7_4 : Certified 7 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_7_5 : Certified 7 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_7_6 : Certified 7 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_7_7 : Certified 7 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_7 (a : Fin (witness 7).cellCount) : Certified 7 a := by
  fin_cases a
  · exact cert_7_0
  · exact cert_7_1
  · exact cert_7_2
  · exact cert_7_3
  · exact cert_7_4
  · exact cert_7_5
  · exact cert_7_6
  · exact cert_7_7

private theorem cert_8_0 : Certified 8 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_8_1 : Certified 8 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_8_2 : Certified 8 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_8_3 : Certified 8 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_8_4 : Certified 8 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_8_5 : Certified 8 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_8_6 : Certified 8 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_8_7 : Certified 8 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_8 (a : Fin (witness 8).cellCount) : Certified 8 a := by
  fin_cases a
  · exact cert_8_0
  · exact cert_8_1
  · exact cert_8_2
  · exact cert_8_3
  · exact cert_8_4
  · exact cert_8_5
  · exact cert_8_6
  · exact cert_8_7

private theorem cert_9_0 : Certified 9 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_9_1 : Certified 9 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_9_2 : Certified 9 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_9_3 : Certified 9 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_9_4 : Certified 9 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_9_5 : Certified 9 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_9_6 : Certified 9 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_9_7 : Certified 9 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_9 (a : Fin (witness 9).cellCount) : Certified 9 a := by
  fin_cases a
  · exact cert_9_0
  · exact cert_9_1
  · exact cert_9_2
  · exact cert_9_3
  · exact cert_9_4
  · exact cert_9_5
  · exact cert_9_6
  · exact cert_9_7

private theorem cert_10_0 : Certified 10 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_10_1 : Certified 10 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_10_2 : Certified 10 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_10_3 : Certified 10 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_10_4 : Certified 10 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_10_5 : Certified 10 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_10_6 : Certified 10 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_10_7 : Certified 10 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_10 (a : Fin (witness 10).cellCount) : Certified 10 a := by
  fin_cases a
  · exact cert_10_0
  · exact cert_10_1
  · exact cert_10_2
  · exact cert_10_3
  · exact cert_10_4
  · exact cert_10_5
  · exact cert_10_6
  · exact cert_10_7

private theorem cert_11_0 : Certified 11 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_11_1 : Certified 11 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_11_2 : Certified 11 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_11_3 : Certified 11 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_11_4 : Certified 11 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_11_5 : Certified 11 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_11_6 : Certified 11 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_11_7 : Certified 11 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_11 (a : Fin (witness 11).cellCount) : Certified 11 a := by
  fin_cases a
  · exact cert_11_0
  · exact cert_11_1
  · exact cert_11_2
  · exact cert_11_3
  · exact cert_11_4
  · exact cert_11_5
  · exact cert_11_6
  · exact cert_11_7

private theorem cert_12_0 : Certified 12 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_12_1 : Certified 12 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_12_2 : Certified 12 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_12_3 : Certified 12 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_12_4 : Certified 12 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_12_5 : Certified 12 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_12 (a : Fin (witness 12).cellCount) : Certified 12 a := by
  fin_cases a
  · exact cert_12_0
  · exact cert_12_1
  · exact cert_12_2
  · exact cert_12_3
  · exact cert_12_4
  · exact cert_12_5

private theorem cert_13_0 : Certified 13 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_13_1 : Certified 13 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_13_2 : Certified 13 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_13_3 : Certified 13 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_13_4 : Certified 13 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_13_5 : Certified 13 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_13 (a : Fin (witness 13).cellCount) : Certified 13 a := by
  fin_cases a
  · exact cert_13_0
  · exact cert_13_1
  · exact cert_13_2
  · exact cert_13_3
  · exact cert_13_4
  · exact cert_13_5

private theorem cert_14_0 : Certified 14 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_14_1 : Certified 14 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_14_2 : Certified 14 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_14_3 : Certified 14 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_14_4 : Certified 14 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_14_5 : Certified 14 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_14 (a : Fin (witness 14).cellCount) : Certified 14 a := by
  fin_cases a
  · exact cert_14_0
  · exact cert_14_1
  · exact cert_14_2
  · exact cert_14_3
  · exact cert_14_4
  · exact cert_14_5

private theorem cert_15_0 : Certified 15 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_15_1 : Certified 15 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_15_2 : Certified 15 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_15_3 : Certified 15 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_15 (a : Fin (witness 15).cellCount) : Certified 15 a := by
  fin_cases a
  · exact cert_15_0
  · exact cert_15_1
  · exact cert_15_2
  · exact cert_15_3

private theorem cert_16_0 : Certified 16 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_16_1 : Certified 16 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_16_2 : Certified 16 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_16_3 : Certified 16 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_16 (a : Fin (witness 16).cellCount) : Certified 16 a := by
  fin_cases a
  · exact cert_16_0
  · exact cert_16_1
  · exact cert_16_2
  · exact cert_16_3

private theorem cert_17_0 : Certified 17 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_17_1 : Certified 17 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_17_2 : Certified 17 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_17_3 : Certified 17 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_17 (a : Fin (witness 17).cellCount) : Certified 17 a := by
  fin_cases a
  · exact cert_17_0
  · exact cert_17_1
  · exact cert_17_2
  · exact cert_17_3

private theorem cert_18_0 : Certified 18 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_18_1 : Certified 18 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_18_2 : Certified 18 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_18_3 : Certified 18 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_18_4 : Certified 18 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_18_5 : Certified 18 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_18 (a : Fin (witness 18).cellCount) : Certified 18 a := by
  fin_cases a
  · exact cert_18_0
  · exact cert_18_1
  · exact cert_18_2
  · exact cert_18_3
  · exact cert_18_4
  · exact cert_18_5

private theorem cert_19_0 : Certified 19 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_19_1 : Certified 19 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_19_2 : Certified 19 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_19_3 : Certified 19 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_19_4 : Certified 19 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_19_5 : Certified 19 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_19 (a : Fin (witness 19).cellCount) : Certified 19 a := by
  fin_cases a
  · exact cert_19_0
  · exact cert_19_1
  · exact cert_19_2
  · exact cert_19_3
  · exact cert_19_4
  · exact cert_19_5

private theorem cert_20_0 : Certified 20 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_20_1 : Certified 20 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_20_2 : Certified 20 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_20_3 : Certified 20 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_20_4 : Certified 20 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_20_5 : Certified 20 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_20 (a : Fin (witness 20).cellCount) : Certified 20 a := by
  fin_cases a
  · exact cert_20_0
  · exact cert_20_1
  · exact cert_20_2
  · exact cert_20_3
  · exact cert_20_4
  · exact cert_20_5

private theorem cert_21_0 : Certified 21 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_21_1 : Certified 21 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_21_2 : Certified 21 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_21_3 : Certified 21 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_21_4 : Certified 21 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_21_5 : Certified 21 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_21_6 : Certified 21 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_21_7 : Certified 21 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_21_8 : Certified 21 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_21 (a : Fin (witness 21).cellCount) : Certified 21 a := by
  fin_cases a
  · exact cert_21_0
  · exact cert_21_1
  · exact cert_21_2
  · exact cert_21_3
  · exact cert_21_4
  · exact cert_21_5
  · exact cert_21_6
  · exact cert_21_7
  · exact cert_21_8

private theorem cert_22_0 : Certified 22 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_22_1 : Certified 22 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_22_2 : Certified 22 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_22_3 : Certified 22 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_22_4 : Certified 22 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_22_5 : Certified 22 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_22_6 : Certified 22 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_22_7 : Certified 22 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_22_8 : Certified 22 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_22 (a : Fin (witness 22).cellCount) : Certified 22 a := by
  fin_cases a
  · exact cert_22_0
  · exact cert_22_1
  · exact cert_22_2
  · exact cert_22_3
  · exact cert_22_4
  · exact cert_22_5
  · exact cert_22_6
  · exact cert_22_7
  · exact cert_22_8

private theorem cert_23_0 : Certified 23 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_23_1 : Certified 23 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_23_2 : Certified 23 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_23_3 : Certified 23 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_23_4 : Certified 23 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_23_5 : Certified 23 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_23_6 : Certified 23 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_23_7 : Certified 23 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_23_8 : Certified 23 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_23 (a : Fin (witness 23).cellCount) : Certified 23 a := by
  fin_cases a
  · exact cert_23_0
  · exact cert_23_1
  · exact cert_23_2
  · exact cert_23_3
  · exact cert_23_4
  · exact cert_23_5
  · exact cert_23_6
  · exact cert_23_7
  · exact cert_23_8

private theorem cert_24_0 : Certified 24 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_1 : Certified 24 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_2 : Certified 24 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_3 : Certified 24 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_4 : Certified 24 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_5 : Certified 24 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_6 : Certified 24 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_7 : Certified 24 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_8 : Certified 24 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_24_9 : Certified 24 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_24 (a : Fin (witness 24).cellCount) : Certified 24 a := by
  fin_cases a
  · exact cert_24_0
  · exact cert_24_1
  · exact cert_24_2
  · exact cert_24_3
  · exact cert_24_4
  · exact cert_24_5
  · exact cert_24_6
  · exact cert_24_7
  · exact cert_24_8
  · exact cert_24_9

private theorem cert_25_0 : Certified 25 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_1 : Certified 25 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_2 : Certified 25 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_3 : Certified 25 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_4 : Certified 25 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_5 : Certified 25 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_6 : Certified 25 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_7 : Certified 25 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_8 : Certified 25 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_25_9 : Certified 25 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_25 (a : Fin (witness 25).cellCount) : Certified 25 a := by
  fin_cases a
  · exact cert_25_0
  · exact cert_25_1
  · exact cert_25_2
  · exact cert_25_3
  · exact cert_25_4
  · exact cert_25_5
  · exact cert_25_6
  · exact cert_25_7
  · exact cert_25_8
  · exact cert_25_9

private theorem cert_26_0 : Certified 26 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_1 : Certified 26 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_2 : Certified 26 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_3 : Certified 26 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_4 : Certified 26 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_5 : Certified 26 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_6 : Certified 26 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_7 : Certified 26 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_8 : Certified 26 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_26_9 : Certified 26 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_26 (a : Fin (witness 26).cellCount) : Certified 26 a := by
  fin_cases a
  · exact cert_26_0
  · exact cert_26_1
  · exact cert_26_2
  · exact cert_26_3
  · exact cert_26_4
  · exact cert_26_5
  · exact cert_26_6
  · exact cert_26_7
  · exact cert_26_8
  · exact cert_26_9

private theorem cert_27_0 : Certified 27 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_27_1 : Certified 27 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_27_2 : Certified 27 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_27_3 : Certified 27 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_27_4 : Certified 27 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_27_5 : Certified 27 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_27_6 : Certified 27 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_27_7 : Certified 27 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_27_8 : Certified 27 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_27 (a : Fin (witness 27).cellCount) : Certified 27 a := by
  fin_cases a
  · exact cert_27_0
  · exact cert_27_1
  · exact cert_27_2
  · exact cert_27_3
  · exact cert_27_4
  · exact cert_27_5
  · exact cert_27_6
  · exact cert_27_7
  · exact cert_27_8

private theorem cert_28_0 : Certified 28 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_28_1 : Certified 28 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_28_2 : Certified 28 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_28_3 : Certified 28 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_28_4 : Certified 28 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_28_5 : Certified 28 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_28_6 : Certified 28 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_28_7 : Certified 28 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_28_8 : Certified 28 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_28 (a : Fin (witness 28).cellCount) : Certified 28 a := by
  fin_cases a
  · exact cert_28_0
  · exact cert_28_1
  · exact cert_28_2
  · exact cert_28_3
  · exact cert_28_4
  · exact cert_28_5
  · exact cert_28_6
  · exact cert_28_7
  · exact cert_28_8

private theorem cert_29_0 : Certified 29 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_29_1 : Certified 29 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_29_2 : Certified 29 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_29_3 : Certified 29 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_29_4 : Certified 29 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_29_5 : Certified 29 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_29_6 : Certified 29 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_29_7 : Certified 29 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_29_8 : Certified 29 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_29 (a : Fin (witness 29).cellCount) : Certified 29 a := by
  fin_cases a
  · exact cert_29_0
  · exact cert_29_1
  · exact cert_29_2
  · exact cert_29_3
  · exact cert_29_4
  · exact cert_29_5
  · exact cert_29_6
  · exact cert_29_7
  · exact cert_29_8

private theorem cert_30_0 : Certified 30 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_30_1 : Certified 30 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_30_2 : Certified 30 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_30_3 : Certified 30 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_30_4 : Certified 30 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_30_5 : Certified 30 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_30 (a : Fin (witness 30).cellCount) : Certified 30 a := by
  fin_cases a
  · exact cert_30_0
  · exact cert_30_1
  · exact cert_30_2
  · exact cert_30_3
  · exact cert_30_4
  · exact cert_30_5

private theorem cert_31_0 : Certified 31 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_31_1 : Certified 31 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_31_2 : Certified 31 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_31_3 : Certified 31 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_31_4 : Certified 31 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_31_5 : Certified 31 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_31 (a : Fin (witness 31).cellCount) : Certified 31 a := by
  fin_cases a
  · exact cert_31_0
  · exact cert_31_1
  · exact cert_31_2
  · exact cert_31_3
  · exact cert_31_4
  · exact cert_31_5

private theorem cert_32_0 : Certified 32 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_32_1 : Certified 32 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_32_2 : Certified 32 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_32_3 : Certified 32 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_32_4 : Certified 32 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_32_5 : Certified 32 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_32 (a : Fin (witness 32).cellCount) : Certified 32 a := by
  fin_cases a
  · exact cert_32_0
  · exact cert_32_1
  · exact cert_32_2
  · exact cert_32_3
  · exact cert_32_4
  · exact cert_32_5

private theorem cert_33_0 : Certified 33 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_33_1 : Certified 33 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_33_2 : Certified 33 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_33_3 : Certified 33 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_33_4 : Certified 33 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_33_5 : Certified 33 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_33_6 : Certified 33 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_33_7 : Certified 33 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_33 (a : Fin (witness 33).cellCount) : Certified 33 a := by
  fin_cases a
  · exact cert_33_0
  · exact cert_33_1
  · exact cert_33_2
  · exact cert_33_3
  · exact cert_33_4
  · exact cert_33_5
  · exact cert_33_6
  · exact cert_33_7

private theorem cert_34_0 : Certified 34 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_34_1 : Certified 34 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_34_2 : Certified 34 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_34_3 : Certified 34 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_34_4 : Certified 34 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_34_5 : Certified 34 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_34_6 : Certified 34 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_34_7 : Certified 34 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_34 (a : Fin (witness 34).cellCount) : Certified 34 a := by
  fin_cases a
  · exact cert_34_0
  · exact cert_34_1
  · exact cert_34_2
  · exact cert_34_3
  · exact cert_34_4
  · exact cert_34_5
  · exact cert_34_6
  · exact cert_34_7

private theorem cert_35_0 : Certified 35 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_35_1 : Certified 35 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_35_2 : Certified 35 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_35_3 : Certified 35 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_35_4 : Certified 35 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_35_5 : Certified 35 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_35_6 : Certified 35 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_35_7 : Certified 35 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_35 (a : Fin (witness 35).cellCount) : Certified 35 a := by
  fin_cases a
  · exact cert_35_0
  · exact cert_35_1
  · exact cert_35_2
  · exact cert_35_3
  · exact cert_35_4
  · exact cert_35_5
  · exact cert_35_6
  · exact cert_35_7

private theorem cert_36_0 : Certified 36 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_1 : Certified 36 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_2 : Certified 36 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_3 : Certified 36 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_4 : Certified 36 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_5 : Certified 36 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_6 : Certified 36 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_7 : Certified 36 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_8 : Certified 36 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_36_9 : Certified 36 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_36 (a : Fin (witness 36).cellCount) : Certified 36 a := by
  fin_cases a
  · exact cert_36_0
  · exact cert_36_1
  · exact cert_36_2
  · exact cert_36_3
  · exact cert_36_4
  · exact cert_36_5
  · exact cert_36_6
  · exact cert_36_7
  · exact cert_36_8
  · exact cert_36_9

private theorem cert_37_0 : Certified 37 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_1 : Certified 37 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_2 : Certified 37 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_3 : Certified 37 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_4 : Certified 37 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_5 : Certified 37 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_6 : Certified 37 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_7 : Certified 37 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_8 : Certified 37 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_37_9 : Certified 37 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_37 (a : Fin (witness 37).cellCount) : Certified 37 a := by
  fin_cases a
  · exact cert_37_0
  · exact cert_37_1
  · exact cert_37_2
  · exact cert_37_3
  · exact cert_37_4
  · exact cert_37_5
  · exact cert_37_6
  · exact cert_37_7
  · exact cert_37_8
  · exact cert_37_9

private theorem cert_38_0 : Certified 38 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_1 : Certified 38 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_2 : Certified 38 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_3 : Certified 38 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_4 : Certified 38 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_5 : Certified 38 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_6 : Certified 38 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_7 : Certified 38 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_8 : Certified 38 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_38_9 : Certified 38 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_38 (a : Fin (witness 38).cellCount) : Certified 38 a := by
  fin_cases a
  · exact cert_38_0
  · exact cert_38_1
  · exact cert_38_2
  · exact cert_38_3
  · exact cert_38_4
  · exact cert_38_5
  · exact cert_38_6
  · exact cert_38_7
  · exact cert_38_8
  · exact cert_38_9

private theorem cert_39_0 : Certified 39 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_1 : Certified 39 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_2 : Certified 39 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_3 : Certified 39 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_4 : Certified 39 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_5 : Certified 39 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_6 : Certified 39 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_7 : Certified 39 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_8 : Certified 39 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_39_9 : Certified 39 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_39 (a : Fin (witness 39).cellCount) : Certified 39 a := by
  fin_cases a
  · exact cert_39_0
  · exact cert_39_1
  · exact cert_39_2
  · exact cert_39_3
  · exact cert_39_4
  · exact cert_39_5
  · exact cert_39_6
  · exact cert_39_7
  · exact cert_39_8
  · exact cert_39_9

private theorem cert_40_0 : Certified 40 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_1 : Certified 40 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_2 : Certified 40 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_3 : Certified 40 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_4 : Certified 40 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_5 : Certified 40 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_6 : Certified 40 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_7 : Certified 40 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_8 : Certified 40 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_40_9 : Certified 40 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_40 (a : Fin (witness 40).cellCount) : Certified 40 a := by
  fin_cases a
  · exact cert_40_0
  · exact cert_40_1
  · exact cert_40_2
  · exact cert_40_3
  · exact cert_40_4
  · exact cert_40_5
  · exact cert_40_6
  · exact cert_40_7
  · exact cert_40_8
  · exact cert_40_9

private theorem cert_41_0 : Certified 41 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_1 : Certified 41 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_2 : Certified 41 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_3 : Certified 41 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_4 : Certified 41 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_5 : Certified 41 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_6 : Certified 41 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_7 : Certified 41 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_8 : Certified 41 ⟨8, by decide +kernel⟩ := by decide +kernel
private theorem cert_41_9 : Certified 41 ⟨9, by decide +kernel⟩ := by decide +kernel

private theorem certificates_41 (a : Fin (witness 41).cellCount) : Certified 41 a := by
  fin_cases a
  · exact cert_41_0
  · exact cert_41_1
  · exact cert_41_2
  · exact cert_41_3
  · exact cert_41_4
  · exact cert_41_5
  · exact cert_41_6
  · exact cert_41_7
  · exact cert_41_8
  · exact cert_41_9

private theorem cert_42_0 : Certified 42 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_42_1 : Certified 42 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_42_2 : Certified 42 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_42_3 : Certified 42 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_42_4 : Certified 42 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_42_5 : Certified 42 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_42_6 : Certified 42 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_42_7 : Certified 42 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_42 (a : Fin (witness 42).cellCount) : Certified 42 a := by
  fin_cases a
  · exact cert_42_0
  · exact cert_42_1
  · exact cert_42_2
  · exact cert_42_3
  · exact cert_42_4
  · exact cert_42_5
  · exact cert_42_6
  · exact cert_42_7

private theorem cert_43_0 : Certified 43 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_43_1 : Certified 43 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_43_2 : Certified 43 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_43_3 : Certified 43 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_43_4 : Certified 43 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_43_5 : Certified 43 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_43_6 : Certified 43 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_43_7 : Certified 43 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_43 (a : Fin (witness 43).cellCount) : Certified 43 a := by
  fin_cases a
  · exact cert_43_0
  · exact cert_43_1
  · exact cert_43_2
  · exact cert_43_3
  · exact cert_43_4
  · exact cert_43_5
  · exact cert_43_6
  · exact cert_43_7

private theorem cert_44_0 : Certified 44 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_44_1 : Certified 44 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_44_2 : Certified 44 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_44_3 : Certified 44 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_44_4 : Certified 44 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_44_5 : Certified 44 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_44_6 : Certified 44 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_44_7 : Certified 44 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_44 (a : Fin (witness 44).cellCount) : Certified 44 a := by
  fin_cases a
  · exact cert_44_0
  · exact cert_44_1
  · exact cert_44_2
  · exact cert_44_3
  · exact cert_44_4
  · exact cert_44_5
  · exact cert_44_6
  · exact cert_44_7

private theorem cert_45_0 : Certified 45 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_45_1 : Certified 45 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_45_2 : Certified 45 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_45_3 : Certified 45 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_45_4 : Certified 45 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_45_5 : Certified 45 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_45_6 : Certified 45 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_45_7 : Certified 45 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_45 (a : Fin (witness 45).cellCount) : Certified 45 a := by
  fin_cases a
  · exact cert_45_0
  · exact cert_45_1
  · exact cert_45_2
  · exact cert_45_3
  · exact cert_45_4
  · exact cert_45_5
  · exact cert_45_6
  · exact cert_45_7

private theorem cert_46_0 : Certified 46 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_46_1 : Certified 46 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_46_2 : Certified 46 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_46_3 : Certified 46 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_46_4 : Certified 46 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_46_5 : Certified 46 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_46_6 : Certified 46 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_46_7 : Certified 46 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_46 (a : Fin (witness 46).cellCount) : Certified 46 a := by
  fin_cases a
  · exact cert_46_0
  · exact cert_46_1
  · exact cert_46_2
  · exact cert_46_3
  · exact cert_46_4
  · exact cert_46_5
  · exact cert_46_6
  · exact cert_46_7

private theorem cert_47_0 : Certified 47 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_47_1 : Certified 47 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_47_2 : Certified 47 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_47_3 : Certified 47 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_47_4 : Certified 47 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_47_5 : Certified 47 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_47_6 : Certified 47 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_47_7 : Certified 47 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_47 (a : Fin (witness 47).cellCount) : Certified 47 a := by
  fin_cases a
  · exact cert_47_0
  · exact cert_47_1
  · exact cert_47_2
  · exact cert_47_3
  · exact cert_47_4
  · exact cert_47_5
  · exact cert_47_6
  · exact cert_47_7

private theorem cert_48_0 : Certified 48 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_48_1 : Certified 48 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_48_2 : Certified 48 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_48_3 : Certified 48 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_48_4 : Certified 48 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_48_5 : Certified 48 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_48_6 : Certified 48 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_48_7 : Certified 48 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_48_8 : Certified 48 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_48 (a : Fin (witness 48).cellCount) : Certified 48 a := by
  fin_cases a
  · exact cert_48_0
  · exact cert_48_1
  · exact cert_48_2
  · exact cert_48_3
  · exact cert_48_4
  · exact cert_48_5
  · exact cert_48_6
  · exact cert_48_7
  · exact cert_48_8

private theorem cert_49_0 : Certified 49 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_49_1 : Certified 49 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_49_2 : Certified 49 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_49_3 : Certified 49 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_49_4 : Certified 49 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_49_5 : Certified 49 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_49_6 : Certified 49 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_49_7 : Certified 49 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_49_8 : Certified 49 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_49 (a : Fin (witness 49).cellCount) : Certified 49 a := by
  fin_cases a
  · exact cert_49_0
  · exact cert_49_1
  · exact cert_49_2
  · exact cert_49_3
  · exact cert_49_4
  · exact cert_49_5
  · exact cert_49_6
  · exact cert_49_7
  · exact cert_49_8

private theorem cert_50_0 : Certified 50 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_50_1 : Certified 50 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_50_2 : Certified 50 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_50_3 : Certified 50 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_50_4 : Certified 50 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_50_5 : Certified 50 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_50_6 : Certified 50 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_50_7 : Certified 50 ⟨7, by decide +kernel⟩ := by decide +kernel
private theorem cert_50_8 : Certified 50 ⟨8, by decide +kernel⟩ := by decide +kernel

private theorem certificates_50 (a : Fin (witness 50).cellCount) : Certified 50 a := by
  fin_cases a
  · exact cert_50_0
  · exact cert_50_1
  · exact cert_50_2
  · exact cert_50_3
  · exact cert_50_4
  · exact cert_50_5
  · exact cert_50_6
  · exact cert_50_7
  · exact cert_50_8

private theorem cert_51_0 : Certified 51 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_51_1 : Certified 51 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_51_2 : Certified 51 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_51_3 : Certified 51 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_51_4 : Certified 51 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_51_5 : Certified 51 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_51_6 : Certified 51 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_51_7 : Certified 51 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_51 (a : Fin (witness 51).cellCount) : Certified 51 a := by
  fin_cases a
  · exact cert_51_0
  · exact cert_51_1
  · exact cert_51_2
  · exact cert_51_3
  · exact cert_51_4
  · exact cert_51_5
  · exact cert_51_6
  · exact cert_51_7

private theorem cert_52_0 : Certified 52 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_52_1 : Certified 52 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_52_2 : Certified 52 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_52_3 : Certified 52 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_52_4 : Certified 52 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_52_5 : Certified 52 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_52_6 : Certified 52 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_52_7 : Certified 52 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_52 (a : Fin (witness 52).cellCount) : Certified 52 a := by
  fin_cases a
  · exact cert_52_0
  · exact cert_52_1
  · exact cert_52_2
  · exact cert_52_3
  · exact cert_52_4
  · exact cert_52_5
  · exact cert_52_6
  · exact cert_52_7

private theorem cert_53_0 : Certified 53 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_53_1 : Certified 53 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_53_2 : Certified 53 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_53_3 : Certified 53 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_53_4 : Certified 53 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_53_5 : Certified 53 ⟨5, by decide +kernel⟩ := by decide +kernel
private theorem cert_53_6 : Certified 53 ⟨6, by decide +kernel⟩ := by decide +kernel
private theorem cert_53_7 : Certified 53 ⟨7, by decide +kernel⟩ := by decide +kernel

private theorem certificates_53 (a : Fin (witness 53).cellCount) : Certified 53 a := by
  fin_cases a
  · exact cert_53_0
  · exact cert_53_1
  · exact cert_53_2
  · exact cert_53_3
  · exact cert_53_4
  · exact cert_53_5
  · exact cert_53_6
  · exact cert_53_7

private theorem cert_54_0 : Certified 54 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_54_1 : Certified 54 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_54_2 : Certified 54 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_54_3 : Certified 54 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_54_4 : Certified 54 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_54_5 : Certified 54 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_54 (a : Fin (witness 54).cellCount) : Certified 54 a := by
  fin_cases a
  · exact cert_54_0
  · exact cert_54_1
  · exact cert_54_2
  · exact cert_54_3
  · exact cert_54_4
  · exact cert_54_5

private theorem cert_55_0 : Certified 55 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_55_1 : Certified 55 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_55_2 : Certified 55 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_55_3 : Certified 55 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_55_4 : Certified 55 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_55_5 : Certified 55 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_55 (a : Fin (witness 55).cellCount) : Certified 55 a := by
  fin_cases a
  · exact cert_55_0
  · exact cert_55_1
  · exact cert_55_2
  · exact cert_55_3
  · exact cert_55_4
  · exact cert_55_5

private theorem cert_56_0 : Certified 56 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_56_1 : Certified 56 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_56_2 : Certified 56 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_56_3 : Certified 56 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_56_4 : Certified 56 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_56_5 : Certified 56 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_56 (a : Fin (witness 56).cellCount) : Certified 56 a := by
  fin_cases a
  · exact cert_56_0
  · exact cert_56_1
  · exact cert_56_2
  · exact cert_56_3
  · exact cert_56_4
  · exact cert_56_5

private theorem cert_57_0 : Certified 57 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_57_1 : Certified 57 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_57_2 : Certified 57 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_57_3 : Certified 57 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_57_4 : Certified 57 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_57_5 : Certified 57 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_57 (a : Fin (witness 57).cellCount) : Certified 57 a := by
  fin_cases a
  · exact cert_57_0
  · exact cert_57_1
  · exact cert_57_2
  · exact cert_57_3
  · exact cert_57_4
  · exact cert_57_5

private theorem cert_58_0 : Certified 58 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_58_1 : Certified 58 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_58_2 : Certified 58 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_58_3 : Certified 58 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_58_4 : Certified 58 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_58_5 : Certified 58 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_58 (a : Fin (witness 58).cellCount) : Certified 58 a := by
  fin_cases a
  · exact cert_58_0
  · exact cert_58_1
  · exact cert_58_2
  · exact cert_58_3
  · exact cert_58_4
  · exact cert_58_5

private theorem cert_59_0 : Certified 59 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_59_1 : Certified 59 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_59_2 : Certified 59 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_59_3 : Certified 59 ⟨3, by decide +kernel⟩ := by decide +kernel
private theorem cert_59_4 : Certified 59 ⟨4, by decide +kernel⟩ := by decide +kernel
private theorem cert_59_5 : Certified 59 ⟨5, by decide +kernel⟩ := by decide +kernel

private theorem certificates_59 (a : Fin (witness 59).cellCount) : Certified 59 a := by
  fin_cases a
  · exact cert_59_0
  · exact cert_59_1
  · exact cert_59_2
  · exact cert_59_3
  · exact cert_59_4
  · exact cert_59_5

private theorem cert_60_0 : Certified 60 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_60_1 : Certified 60 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_60_2 : Certified 60 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_60_3 : Certified 60 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_60 (a : Fin (witness 60).cellCount) : Certified 60 a := by
  fin_cases a
  · exact cert_60_0
  · exact cert_60_1
  · exact cert_60_2
  · exact cert_60_3

private theorem cert_61_0 : Certified 61 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_61_1 : Certified 61 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_61_2 : Certified 61 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_61_3 : Certified 61 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_61 (a : Fin (witness 61).cellCount) : Certified 61 a := by
  fin_cases a
  · exact cert_61_0
  · exact cert_61_1
  · exact cert_61_2
  · exact cert_61_3

private theorem cert_62_0 : Certified 62 ⟨0, by decide +kernel⟩ := by decide +kernel
private theorem cert_62_1 : Certified 62 ⟨1, by decide +kernel⟩ := by decide +kernel
private theorem cert_62_2 : Certified 62 ⟨2, by decide +kernel⟩ := by decide +kernel
private theorem cert_62_3 : Certified 62 ⟨3, by decide +kernel⟩ := by decide +kernel

private theorem certificates_62 (a : Fin (witness 62).cellCount) : Certified 62 a := by
  fin_cases a
  · exact cert_62_0
  · exact cert_62_1
  · exact cert_62_2
  · exact cert_62_3

private theorem certificates (r : Fin 63) (a : Fin (witness r).cellCount) : Certified r a := by
  fin_cases r
  · exact certificates_0 a
  · exact certificates_1 a
  · exact certificates_2 a
  · exact certificates_3 a
  · exact certificates_4 a
  · exact certificates_5 a
  · exact certificates_6 a
  · exact certificates_7 a
  · exact certificates_8 a
  · exact certificates_9 a
  · exact certificates_10 a
  · exact certificates_11 a
  · exact certificates_12 a
  · exact certificates_13 a
  · exact certificates_14 a
  · exact certificates_15 a
  · exact certificates_16 a
  · exact certificates_17 a
  · exact certificates_18 a
  · exact certificates_19 a
  · exact certificates_20 a
  · exact certificates_21 a
  · exact certificates_22 a
  · exact certificates_23 a
  · exact certificates_24 a
  · exact certificates_25 a
  · exact certificates_26 a
  · exact certificates_27 a
  · exact certificates_28 a
  · exact certificates_29 a
  · exact certificates_30 a
  · exact certificates_31 a
  · exact certificates_32 a
  · exact certificates_33 a
  · exact certificates_34 a
  · exact certificates_35 a
  · exact certificates_36 a
  · exact certificates_37 a
  · exact certificates_38 a
  · exact certificates_39 a
  · exact certificates_40 a
  · exact certificates_41 a
  · exact certificates_42 a
  · exact certificates_43 a
  · exact certificates_44 a
  · exact certificates_45 a
  · exact certificates_46 a
  · exact certificates_47 a
  · exact certificates_48 a
  · exact certificates_49 a
  · exact certificates_50 a
  · exact certificates_51 a
  · exact certificates_52 a
  · exact certificates_53 a
  · exact certificates_54 a
  · exact certificates_55 a
  · exact certificates_56 a
  · exact certificates_57 a
  · exact certificates_58 a
  · exact certificates_59 a
  · exact certificates_60 a
  · exact certificates_61 a
  · exact certificates_62 a

private theorem all_logs (r : Fin 63) (a : Fin (witness r).cellCount) :
    (logLower r a : ℝ) ≤ Real.log ((witness r).reference a : ℝ) := by
  obtain ⟨hq, ht0, ht1, hscale, hlo, hhi⟩ := certificates r a
  exact (mme_log_interval_of_exact_rational_series_certificate
    ((witness r).reference a) (logParameter r a) (logLower r a) 0
    ((witness r).logScale a) (seriesLength r a) hq ht0 ht1 hscale hlo hhi).1

private abbrev Facts (r : Fin 63) : Prop :=
  (∑ a, (witness r).alpha a = 1) ∧
  (∑ a, (witness r).reference a = 1) ∧
  (∀ a, 0 < (witness r).reference a) ∧
  -(∑ a, (witness r).alpha a * potential r a) +
    (witness r).epsilon ≤ (witness r).entropyUpper

private theorem facts_0 : Facts 0 := by decide +kernel
private theorem facts_1 : Facts 1 := by decide +kernel
private theorem facts_2 : Facts 2 := by decide +kernel
private theorem facts_3 : Facts 3 := by decide +kernel
private theorem facts_4 : Facts 4 := by decide +kernel
private theorem facts_5 : Facts 5 := by decide +kernel
private theorem facts_6 : Facts 6 := by decide +kernel
private theorem facts_7 : Facts 7 := by decide +kernel
private theorem facts_8 : Facts 8 := by decide +kernel
private theorem facts_9 : Facts 9 := by decide +kernel
private theorem facts_10 : Facts 10 := by decide +kernel
private theorem facts_11 : Facts 11 := by decide +kernel
private theorem facts_12 : Facts 12 := by decide +kernel
private theorem facts_13 : Facts 13 := by decide +kernel
private theorem facts_14 : Facts 14 := by decide +kernel
private theorem facts_15 : Facts 15 := by decide +kernel
private theorem facts_16 : Facts 16 := by decide +kernel
private theorem facts_17 : Facts 17 := by decide +kernel
private theorem facts_18 : Facts 18 := by decide +kernel
private theorem facts_19 : Facts 19 := by decide +kernel
private theorem facts_20 : Facts 20 := by decide +kernel
private theorem facts_21 : Facts 21 := by decide +kernel
private theorem facts_22 : Facts 22 := by decide +kernel
private theorem facts_23 : Facts 23 := by decide +kernel
private theorem facts_24 : Facts 24 := by decide +kernel
private theorem facts_25 : Facts 25 := by decide +kernel
private theorem facts_26 : Facts 26 := by decide +kernel
private theorem facts_27 : Facts 27 := by decide +kernel
private theorem facts_28 : Facts 28 := by decide +kernel
private theorem facts_29 : Facts 29 := by decide +kernel
private theorem facts_30 : Facts 30 := by decide +kernel
private theorem facts_31 : Facts 31 := by decide +kernel
private theorem facts_32 : Facts 32 := by decide +kernel
private theorem facts_33 : Facts 33 := by decide +kernel
private theorem facts_34 : Facts 34 := by decide +kernel
private theorem facts_35 : Facts 35 := by decide +kernel
private theorem facts_36 : Facts 36 := by decide +kernel
private theorem facts_37 : Facts 37 := by decide +kernel
private theorem facts_38 : Facts 38 := by decide +kernel
private theorem facts_39 : Facts 39 := by decide +kernel
private theorem facts_40 : Facts 40 := by decide +kernel
private theorem facts_41 : Facts 41 := by decide +kernel
private theorem facts_42 : Facts 42 := by decide +kernel
private theorem facts_43 : Facts 43 := by decide +kernel
private theorem facts_44 : Facts 44 := by decide +kernel
private theorem facts_45 : Facts 45 := by decide +kernel
private theorem facts_46 : Facts 46 := by decide +kernel
private theorem facts_47 : Facts 47 := by decide +kernel
private theorem facts_48 : Facts 48 := by decide +kernel
private theorem facts_49 : Facts 49 := by decide +kernel
private theorem facts_50 : Facts 50 := by decide +kernel
private theorem facts_51 : Facts 51 := by decide +kernel
private theorem facts_52 : Facts 52 := by decide +kernel
private theorem facts_53 : Facts 53 := by decide +kernel
private theorem facts_54 : Facts 54 := by decide +kernel
private theorem facts_55 : Facts 55 := by decide +kernel
private theorem facts_56 : Facts 56 := by decide +kernel
private theorem facts_57 : Facts 57 := by decide +kernel
private theorem facts_58 : Facts 58 := by decide +kernel
private theorem facts_59 : Facts 59 := by decide +kernel
private theorem facts_60 : Facts 60 := by decide +kernel
private theorem facts_61 : Facts 61 := by decide +kernel
private theorem facts_62 : Facts 62 := by decide +kernel

private theorem facts (r : Fin 63) : Facts r := by
  fin_cases r
  · exact facts_0
  · exact facts_1
  · exact facts_2
  · exact facts_3
  · exact facts_4
  · exact facts_5
  · exact facts_6
  · exact facts_7
  · exact facts_8
  · exact facts_9
  · exact facts_10
  · exact facts_11
  · exact facts_12
  · exact facts_13
  · exact facts_14
  · exact facts_15
  · exact facts_16
  · exact facts_17
  · exact facts_18
  · exact facts_19
  · exact facts_20
  · exact facts_21
  · exact facts_22
  · exact facts_23
  · exact facts_24
  · exact facts_25
  · exact facts_26
  · exact facts_27
  · exact facts_28
  · exact facts_29
  · exact facts_30
  · exact facts_31
  · exact facts_32
  · exact facts_33
  · exact facts_34
  · exact facts_35
  · exact facts_36
  · exact facts_37
  · exact facts_38
  · exact facts_39
  · exact facts_40
  · exact facts_41
  · exact facts_42
  · exact facts_43
  · exact facts_44
  · exact facts_45
  · exact facts_46
  · exact facts_47
  · exact facts_48
  · exact facts_49
  · exact facts_50
  · exact facts_51
  · exact facts_52
  · exact facts_53
  · exact facts_54
  · exact facts_55
  · exact facts_56
  · exact facts_57
  · exact facts_58
  · exact facts_59
  · exact facts_60
  · exact facts_61
  · exact facts_62

theorem solution (r : Fin 63) (rho : Fin (witness r).cellCount → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 5),
      mme_modern_marginal (fun a ↦ (witness r).coarseAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ (witness r).coarseAddress a mode)
        (fun a ↦ ((witness r).alpha a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ ((witness r).entropyUpper : ℝ) := by
  obtain ⟨hasum, hysum, hypos, hupper⟩ := facts r
  have hy : ∀ a, (0 : ℝ) < ((witness r).reference a : ℝ) := by
    intro a
    exact_mod_cast hypos a
  have halphaSum : ∑ a, ((witness r).alpha a : ℝ) = 1 := by
    exact_mod_cast hasum
  have hySum : ∑ a, ((witness r).reference a : ℝ) = 1 := by
    exact_mod_cast hysum
  have hlog : ∀ a,
      ((witness r).lambdaZero : ℝ) +
        ((witness r).lambdaModes 0 ((witness r).coarseAddress a 0) : ℝ) +
        ((witness r).lambdaModes 1 ((witness r).coarseAddress a 1) : ℝ) +
        ((witness r).lambdaModes 2 ((witness r).coarseAddress a 2) : ℝ) -
        ((witness r).epsilon : ℝ) ≤ Real.log ((witness r).reference a : ℝ) := by
    intro a
    simpa only [logLower, potential, Rat.cast_sub, Rat.cast_add] using all_logs r a
  have h := mme_modern_entropyNat_upper_from_positive_reference
    (fun a ↦ (witness r).coarseAddress a 0) (fun a ↦ (witness r).coarseAddress a 1)
    (fun a ↦ (witness r).coarseAddress a 2) rho
    (fun a ↦ ((witness r).alpha a : ℝ)) (fun a ↦ ((witness r).reference a : ℝ))
    ((witness r).lambdaZero : ℝ) (fun j ↦ ((witness r).lambdaModes 0 j : ℝ))
    (fun j ↦ ((witness r).lambdaModes 1 j : ℝ)) (fun j ↦ ((witness r).lambdaModes 2 j : ℝ))
    ((witness r).epsilon : ℝ) hrho hy hrhoSum halphaSum hySum
    (hmarg 0) (hmarg 1) (hmarg 2) hlog
  have hbound : -(∑ a, ((witness r).alpha a : ℝ) * (potential r a : ℝ)) +
      ((witness r).epsilon : ℝ) ≤ ((witness r).entropyUpper : ℝ) := by
    exact_mod_cast hupper
  apply h.trans
  simpa only [potential, Rat.cast_add] using hbound
