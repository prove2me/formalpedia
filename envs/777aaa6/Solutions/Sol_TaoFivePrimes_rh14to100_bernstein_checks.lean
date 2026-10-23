-- Prove2me | solution 1 for TaoFivePrimes.rh14to100_bernstein_checks
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T09:53:18.287371+00:00
-- url     : https://prove2.me/submissions/7791d392-81cd-43f5-a7ce-12b298ff1cfc

/- Original finite validators and certificates: sometik179,
Prove2Me c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03).
Ordinary kernel proof adaptation; theta/Mellin attribution to Gabewhigham.
-/
import Definitions.Def_TaoFivePrimes_RH14To100BernsteinInterface
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes
local instance cert_bernstein_decidableValid (i : Fin 86) (j : Nat) (c : Certificate) : Decidable (valid i j c) := by
  unfold valid
  infer_instance

theorem cert_bernstein_row_valid_0 : ∀ j : Fin 2, j.val<(rowSpecs (0:Fin 86)).length →
    valid (0:Fin 86) j.val (certificateAt (0:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_1 : ∀ j : Fin 2, j.val<(rowSpecs (1:Fin 86)).length →
    valid (1:Fin 86) j.val (certificateAt (1:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_2 : ∀ j : Fin 2, j.val<(rowSpecs (2:Fin 86)).length →
    valid (2:Fin 86) j.val (certificateAt (2:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_3 : ∀ j : Fin 2, j.val<(rowSpecs (3:Fin 86)).length →
    valid (3:Fin 86) j.val (certificateAt (3:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_4 : ∀ j : Fin 2, j.val<(rowSpecs (4:Fin 86)).length →
    valid (4:Fin 86) j.val (certificateAt (4:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_5 : ∀ j : Fin 2, j.val<(rowSpecs (5:Fin 86)).length →
    valid (5:Fin 86) j.val (certificateAt (5:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_6 : ∀ j : Fin 2, j.val<(rowSpecs (6:Fin 86)).length →
    valid (6:Fin 86) j.val (certificateAt (6:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_7 : ∀ j : Fin 2, j.val<(rowSpecs (7:Fin 86)).length →
    valid (7:Fin 86) j.val (certificateAt (7:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_8 : ∀ j : Fin 2, j.val<(rowSpecs (8:Fin 86)).length →
    valid (8:Fin 86) j.val (certificateAt (8:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_9 : ∀ j : Fin 2, j.val<(rowSpecs (9:Fin 86)).length →
    valid (9:Fin 86) j.val (certificateAt (9:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_10 : ∀ j : Fin 2, j.val<(rowSpecs (10:Fin 86)).length →
    valid (10:Fin 86) j.val (certificateAt (10:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_11 : ∀ j : Fin 2, j.val<(rowSpecs (11:Fin 86)).length →
    valid (11:Fin 86) j.val (certificateAt (11:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_12 : ∀ j : Fin 2, j.val<(rowSpecs (12:Fin 86)).length →
    valid (12:Fin 86) j.val (certificateAt (12:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_13 : ∀ j : Fin 2, j.val<(rowSpecs (13:Fin 86)).length →
    valid (13:Fin 86) j.val (certificateAt (13:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_14 : ∀ j : Fin 2, j.val<(rowSpecs (14:Fin 86)).length →
    valid (14:Fin 86) j.val (certificateAt (14:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_15 : ∀ j : Fin 2, j.val<(rowSpecs (15:Fin 86)).length →
    valid (15:Fin 86) j.val (certificateAt (15:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_16 : ∀ j : Fin 2, j.val<(rowSpecs (16:Fin 86)).length →
    valid (16:Fin 86) j.val (certificateAt (16:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_17 : ∀ j : Fin 2, j.val<(rowSpecs (17:Fin 86)).length →
    valid (17:Fin 86) j.val (certificateAt (17:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_18 : ∀ j : Fin 2, j.val<(rowSpecs (18:Fin 86)).length →
    valid (18:Fin 86) j.val (certificateAt (18:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_19 : ∀ j : Fin 2, j.val<(rowSpecs (19:Fin 86)).length →
    valid (19:Fin 86) j.val (certificateAt (19:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_20 : ∀ j : Fin 2, j.val<(rowSpecs (20:Fin 86)).length →
    valid (20:Fin 86) j.val (certificateAt (20:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_21 : ∀ j : Fin 2, j.val<(rowSpecs (21:Fin 86)).length →
    valid (21:Fin 86) j.val (certificateAt (21:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_22 : ∀ j : Fin 2, j.val<(rowSpecs (22:Fin 86)).length →
    valid (22:Fin 86) j.val (certificateAt (22:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_23 : ∀ j : Fin 2, j.val<(rowSpecs (23:Fin 86)).length →
    valid (23:Fin 86) j.val (certificateAt (23:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_24 : ∀ j : Fin 2, j.val<(rowSpecs (24:Fin 86)).length →
    valid (24:Fin 86) j.val (certificateAt (24:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_25 : ∀ j : Fin 2, j.val<(rowSpecs (25:Fin 86)).length →
    valid (25:Fin 86) j.val (certificateAt (25:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_26 : ∀ j : Fin 2, j.val<(rowSpecs (26:Fin 86)).length →
    valid (26:Fin 86) j.val (certificateAt (26:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_27 : ∀ j : Fin 2, j.val<(rowSpecs (27:Fin 86)).length →
    valid (27:Fin 86) j.val (certificateAt (27:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_28 : ∀ j : Fin 2, j.val<(rowSpecs (28:Fin 86)).length →
    valid (28:Fin 86) j.val (certificateAt (28:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_29 : ∀ j : Fin 2, j.val<(rowSpecs (29:Fin 86)).length →
    valid (29:Fin 86) j.val (certificateAt (29:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_30 : ∀ j : Fin 2, j.val<(rowSpecs (30:Fin 86)).length →
    valid (30:Fin 86) j.val (certificateAt (30:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_31 : ∀ j : Fin 2, j.val<(rowSpecs (31:Fin 86)).length →
    valid (31:Fin 86) j.val (certificateAt (31:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_32 : ∀ j : Fin 2, j.val<(rowSpecs (32:Fin 86)).length →
    valid (32:Fin 86) j.val (certificateAt (32:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_33 : ∀ j : Fin 2, j.val<(rowSpecs (33:Fin 86)).length →
    valid (33:Fin 86) j.val (certificateAt (33:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_34 : ∀ j : Fin 2, j.val<(rowSpecs (34:Fin 86)).length →
    valid (34:Fin 86) j.val (certificateAt (34:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_35 : ∀ j : Fin 2, j.val<(rowSpecs (35:Fin 86)).length →
    valid (35:Fin 86) j.val (certificateAt (35:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_36 : ∀ j : Fin 2, j.val<(rowSpecs (36:Fin 86)).length →
    valid (36:Fin 86) j.val (certificateAt (36:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_37 : ∀ j : Fin 2, j.val<(rowSpecs (37:Fin 86)).length →
    valid (37:Fin 86) j.val (certificateAt (37:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_38 : ∀ j : Fin 2, j.val<(rowSpecs (38:Fin 86)).length →
    valid (38:Fin 86) j.val (certificateAt (38:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_39 : ∀ j : Fin 2, j.val<(rowSpecs (39:Fin 86)).length →
    valid (39:Fin 86) j.val (certificateAt (39:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_40 : ∀ j : Fin 2, j.val<(rowSpecs (40:Fin 86)).length →
    valid (40:Fin 86) j.val (certificateAt (40:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_41 : ∀ j : Fin 2, j.val<(rowSpecs (41:Fin 86)).length →
    valid (41:Fin 86) j.val (certificateAt (41:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_42 : ∀ j : Fin 2, j.val<(rowSpecs (42:Fin 86)).length →
    valid (42:Fin 86) j.val (certificateAt (42:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_43 : ∀ j : Fin 2, j.val<(rowSpecs (43:Fin 86)).length →
    valid (43:Fin 86) j.val (certificateAt (43:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_44 : ∀ j : Fin 2, j.val<(rowSpecs (44:Fin 86)).length →
    valid (44:Fin 86) j.val (certificateAt (44:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_45 : ∀ j : Fin 2, j.val<(rowSpecs (45:Fin 86)).length →
    valid (45:Fin 86) j.val (certificateAt (45:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_46 : ∀ j : Fin 2, j.val<(rowSpecs (46:Fin 86)).length →
    valid (46:Fin 86) j.val (certificateAt (46:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_47 : ∀ j : Fin 2, j.val<(rowSpecs (47:Fin 86)).length →
    valid (47:Fin 86) j.val (certificateAt (47:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_48 : ∀ j : Fin 2, j.val<(rowSpecs (48:Fin 86)).length →
    valid (48:Fin 86) j.val (certificateAt (48:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_49 : ∀ j : Fin 2, j.val<(rowSpecs (49:Fin 86)).length →
    valid (49:Fin 86) j.val (certificateAt (49:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_50 : ∀ j : Fin 2, j.val<(rowSpecs (50:Fin 86)).length →
    valid (50:Fin 86) j.val (certificateAt (50:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_51 : ∀ j : Fin 2, j.val<(rowSpecs (51:Fin 86)).length →
    valid (51:Fin 86) j.val (certificateAt (51:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_52 : ∀ j : Fin 2, j.val<(rowSpecs (52:Fin 86)).length →
    valid (52:Fin 86) j.val (certificateAt (52:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_53 : ∀ j : Fin 2, j.val<(rowSpecs (53:Fin 86)).length →
    valid (53:Fin 86) j.val (certificateAt (53:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_54 : ∀ j : Fin 2, j.val<(rowSpecs (54:Fin 86)).length →
    valid (54:Fin 86) j.val (certificateAt (54:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_55 : ∀ j : Fin 2, j.val<(rowSpecs (55:Fin 86)).length →
    valid (55:Fin 86) j.val (certificateAt (55:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_56 : ∀ j : Fin 2, j.val<(rowSpecs (56:Fin 86)).length →
    valid (56:Fin 86) j.val (certificateAt (56:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_57 : ∀ j : Fin 2, j.val<(rowSpecs (57:Fin 86)).length →
    valid (57:Fin 86) j.val (certificateAt (57:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_58 : ∀ j : Fin 2, j.val<(rowSpecs (58:Fin 86)).length →
    valid (58:Fin 86) j.val (certificateAt (58:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_59 : ∀ j : Fin 2, j.val<(rowSpecs (59:Fin 86)).length →
    valid (59:Fin 86) j.val (certificateAt (59:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_60 : ∀ j : Fin 2, j.val<(rowSpecs (60:Fin 86)).length →
    valid (60:Fin 86) j.val (certificateAt (60:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_61 : ∀ j : Fin 2, j.val<(rowSpecs (61:Fin 86)).length →
    valid (61:Fin 86) j.val (certificateAt (61:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_62 : ∀ j : Fin 2, j.val<(rowSpecs (62:Fin 86)).length →
    valid (62:Fin 86) j.val (certificateAt (62:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_63 : ∀ j : Fin 2, j.val<(rowSpecs (63:Fin 86)).length →
    valid (63:Fin 86) j.val (certificateAt (63:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_64 : ∀ j : Fin 2, j.val<(rowSpecs (64:Fin 86)).length →
    valid (64:Fin 86) j.val (certificateAt (64:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_65 : ∀ j : Fin 2, j.val<(rowSpecs (65:Fin 86)).length →
    valid (65:Fin 86) j.val (certificateAt (65:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_66 : ∀ j : Fin 2, j.val<(rowSpecs (66:Fin 86)).length →
    valid (66:Fin 86) j.val (certificateAt (66:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_67 : ∀ j : Fin 2, j.val<(rowSpecs (67:Fin 86)).length →
    valid (67:Fin 86) j.val (certificateAt (67:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_68 : ∀ j : Fin 2, j.val<(rowSpecs (68:Fin 86)).length →
    valid (68:Fin 86) j.val (certificateAt (68:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_69 : ∀ j : Fin 2, j.val<(rowSpecs (69:Fin 86)).length →
    valid (69:Fin 86) j.val (certificateAt (69:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_70 : ∀ j : Fin 2, j.val<(rowSpecs (70:Fin 86)).length →
    valid (70:Fin 86) j.val (certificateAt (70:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_71 : ∀ j : Fin 2, j.val<(rowSpecs (71:Fin 86)).length →
    valid (71:Fin 86) j.val (certificateAt (71:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_72 : ∀ j : Fin 2, j.val<(rowSpecs (72:Fin 86)).length →
    valid (72:Fin 86) j.val (certificateAt (72:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_73 : ∀ j : Fin 2, j.val<(rowSpecs (73:Fin 86)).length →
    valid (73:Fin 86) j.val (certificateAt (73:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_74 : ∀ j : Fin 2, j.val<(rowSpecs (74:Fin 86)).length →
    valid (74:Fin 86) j.val (certificateAt (74:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_75 : ∀ j : Fin 2, j.val<(rowSpecs (75:Fin 86)).length →
    valid (75:Fin 86) j.val (certificateAt (75:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_76 : ∀ j : Fin 2, j.val<(rowSpecs (76:Fin 86)).length →
    valid (76:Fin 86) j.val (certificateAt (76:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_77 : ∀ j : Fin 2, j.val<(rowSpecs (77:Fin 86)).length →
    valid (77:Fin 86) j.val (certificateAt (77:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_78 : ∀ j : Fin 2, j.val<(rowSpecs (78:Fin 86)).length →
    valid (78:Fin 86) j.val (certificateAt (78:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_79 : ∀ j : Fin 2, j.val<(rowSpecs (79:Fin 86)).length →
    valid (79:Fin 86) j.val (certificateAt (79:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_80 : ∀ j : Fin 2, j.val<(rowSpecs (80:Fin 86)).length →
    valid (80:Fin 86) j.val (certificateAt (80:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_81 : ∀ j : Fin 2, j.val<(rowSpecs (81:Fin 86)).length →
    valid (81:Fin 86) j.val (certificateAt (81:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_82 : ∀ j : Fin 2, j.val<(rowSpecs (82:Fin 86)).length →
    valid (82:Fin 86) j.val (certificateAt (82:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_83 : ∀ j : Fin 2, j.val<(rowSpecs (83:Fin 86)).length →
    valid (83:Fin 86) j.val (certificateAt (83:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_84 : ∀ j : Fin 2, j.val<(rowSpecs (84:Fin 86)).length →
    valid (84:Fin 86) j.val (certificateAt (84:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_valid_85 : ∀ j : Fin 2, j.val<(rowSpecs (85:Fin 86)).length →
    valid (85:Fin 86) j.val (certificateAt (85:Fin 86) j.val) := by decide +kernel

theorem cert_bernstein_row_lengths : ∀ i : Fin 86, (rowSpecs i).length≤ 2 := by decide +kernel

theorem cert_bernstein_certificates_valid (i : Fin 86) (j : ℕ) (hj : j<(rowSpecs i).length) :
    valid i j (certificateAt i j) := by
  have hj2 : j<2 := hj.trans_le (cert_bernstein_row_lengths i)
  let j' : Fin 2 := ⟨j,hj2⟩
  change valid i j'.val (certificateAt i j'.val)
  fin_cases i
  · exact cert_bernstein_row_valid_0 j' hj
  · exact cert_bernstein_row_valid_1 j' hj
  · exact cert_bernstein_row_valid_2 j' hj
  · exact cert_bernstein_row_valid_3 j' hj
  · exact cert_bernstein_row_valid_4 j' hj
  · exact cert_bernstein_row_valid_5 j' hj
  · exact cert_bernstein_row_valid_6 j' hj
  · exact cert_bernstein_row_valid_7 j' hj
  · exact cert_bernstein_row_valid_8 j' hj
  · exact cert_bernstein_row_valid_9 j' hj
  · exact cert_bernstein_row_valid_10 j' hj
  · exact cert_bernstein_row_valid_11 j' hj
  · exact cert_bernstein_row_valid_12 j' hj
  · exact cert_bernstein_row_valid_13 j' hj
  · exact cert_bernstein_row_valid_14 j' hj
  · exact cert_bernstein_row_valid_15 j' hj
  · exact cert_bernstein_row_valid_16 j' hj
  · exact cert_bernstein_row_valid_17 j' hj
  · exact cert_bernstein_row_valid_18 j' hj
  · exact cert_bernstein_row_valid_19 j' hj
  · exact cert_bernstein_row_valid_20 j' hj
  · exact cert_bernstein_row_valid_21 j' hj
  · exact cert_bernstein_row_valid_22 j' hj
  · exact cert_bernstein_row_valid_23 j' hj
  · exact cert_bernstein_row_valid_24 j' hj
  · exact cert_bernstein_row_valid_25 j' hj
  · exact cert_bernstein_row_valid_26 j' hj
  · exact cert_bernstein_row_valid_27 j' hj
  · exact cert_bernstein_row_valid_28 j' hj
  · exact cert_bernstein_row_valid_29 j' hj
  · exact cert_bernstein_row_valid_30 j' hj
  · exact cert_bernstein_row_valid_31 j' hj
  · exact cert_bernstein_row_valid_32 j' hj
  · exact cert_bernstein_row_valid_33 j' hj
  · exact cert_bernstein_row_valid_34 j' hj
  · exact cert_bernstein_row_valid_35 j' hj
  · exact cert_bernstein_row_valid_36 j' hj
  · exact cert_bernstein_row_valid_37 j' hj
  · exact cert_bernstein_row_valid_38 j' hj
  · exact cert_bernstein_row_valid_39 j' hj
  · exact cert_bernstein_row_valid_40 j' hj
  · exact cert_bernstein_row_valid_41 j' hj
  · exact cert_bernstein_row_valid_42 j' hj
  · exact cert_bernstein_row_valid_43 j' hj
  · exact cert_bernstein_row_valid_44 j' hj
  · exact cert_bernstein_row_valid_45 j' hj
  · exact cert_bernstein_row_valid_46 j' hj
  · exact cert_bernstein_row_valid_47 j' hj
  · exact cert_bernstein_row_valid_48 j' hj
  · exact cert_bernstein_row_valid_49 j' hj
  · exact cert_bernstein_row_valid_50 j' hj
  · exact cert_bernstein_row_valid_51 j' hj
  · exact cert_bernstein_row_valid_52 j' hj
  · exact cert_bernstein_row_valid_53 j' hj
  · exact cert_bernstein_row_valid_54 j' hj
  · exact cert_bernstein_row_valid_55 j' hj
  · exact cert_bernstein_row_valid_56 j' hj
  · exact cert_bernstein_row_valid_57 j' hj
  · exact cert_bernstein_row_valid_58 j' hj
  · exact cert_bernstein_row_valid_59 j' hj
  · exact cert_bernstein_row_valid_60 j' hj
  · exact cert_bernstein_row_valid_61 j' hj
  · exact cert_bernstein_row_valid_62 j' hj
  · exact cert_bernstein_row_valid_63 j' hj
  · exact cert_bernstein_row_valid_64 j' hj
  · exact cert_bernstein_row_valid_65 j' hj
  · exact cert_bernstein_row_valid_66 j' hj
  · exact cert_bernstein_row_valid_67 j' hj
  · exact cert_bernstein_row_valid_68 j' hj
  · exact cert_bernstein_row_valid_69 j' hj
  · exact cert_bernstein_row_valid_70 j' hj
  · exact cert_bernstein_row_valid_71 j' hj
  · exact cert_bernstein_row_valid_72 j' hj
  · exact cert_bernstein_row_valid_73 j' hj
  · exact cert_bernstein_row_valid_74 j' hj
  · exact cert_bernstein_row_valid_75 j' hj
  · exact cert_bernstein_row_valid_76 j' hj
  · exact cert_bernstein_row_valid_77 j' hj
  · exact cert_bernstein_row_valid_78 j' hj
  · exact cert_bernstein_row_valid_79 j' hj
  · exact cert_bernstein_row_valid_80 j' hj
  · exact cert_bernstein_row_valid_81 j' hj
  · exact cert_bernstein_row_valid_82 j' hj
  · exact cert_bernstein_row_valid_83 j' hj
  · exact cert_bernstein_row_valid_84 j' hj
  · exact cert_bernstein_row_valid_85 j' hj

end CertifiedStreamingLocalBoxes

theorem TaoFivePrimes.rh14to100_bernstein_checks : (∀ (i : Fin 86) (j : ℕ), j<(CertifiedLocalBoxes.rowSpecs i).length →
      CertifiedStreamingLocalBoxes.valid i j (CertifiedStreamingLocalBoxes.certificateAt i j)) ∧
    (∀ i : Fin 86, (CertifiedLocalBoxes.rowSpecs i).length≤ 2) := by
  exact ⟨CertifiedStreamingLocalBoxes.cert_bernstein_certificates_valid,
     CertifiedStreamingLocalBoxes.cert_bernstein_row_lengths⟩

theorem solution : (∀ (i : Fin 86) (j : ℕ), j<(CertifiedLocalBoxes.rowSpecs i).length →
      CertifiedStreamingLocalBoxes.valid i j (CertifiedStreamingLocalBoxes.certificateAt i j)) ∧
    (∀ i : Fin 86, (CertifiedLocalBoxes.rowSpecs i).length≤ 2) := TaoFivePrimes.rh14to100_bernstein_checks
