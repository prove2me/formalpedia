-- Prove2me | solution 1 for Couret.Certificate.separating_words_checked
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:18.331641+00:00
-- url     : https://prove2.me/submissions/933ee44b-7433-4e4a-b85f-929c4ac4e86f

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Theorems.Thm_Couret_Certificate_class_row_0
import Theorems.Thm_Couret_Certificate_class_row_1
import Theorems.Thm_Couret_Certificate_class_row_10
import Theorems.Thm_Couret_Certificate_class_row_100
import Theorems.Thm_Couret_Certificate_class_row_11
import Theorems.Thm_Couret_Certificate_class_row_12
import Theorems.Thm_Couret_Certificate_class_row_13
import Theorems.Thm_Couret_Certificate_class_row_14
import Theorems.Thm_Couret_Certificate_class_row_15
import Theorems.Thm_Couret_Certificate_class_row_16
import Theorems.Thm_Couret_Certificate_class_row_17
import Theorems.Thm_Couret_Certificate_class_row_18
import Theorems.Thm_Couret_Certificate_class_row_19
import Theorems.Thm_Couret_Certificate_class_row_2
import Theorems.Thm_Couret_Certificate_class_row_20
import Theorems.Thm_Couret_Certificate_class_row_21
import Theorems.Thm_Couret_Certificate_class_row_22
import Theorems.Thm_Couret_Certificate_class_row_23
import Theorems.Thm_Couret_Certificate_class_row_24
import Theorems.Thm_Couret_Certificate_class_row_25
import Theorems.Thm_Couret_Certificate_class_row_26
import Theorems.Thm_Couret_Certificate_class_row_27
import Theorems.Thm_Couret_Certificate_class_row_28
import Theorems.Thm_Couret_Certificate_class_row_29
import Theorems.Thm_Couret_Certificate_class_row_3
import Theorems.Thm_Couret_Certificate_class_row_30
import Theorems.Thm_Couret_Certificate_class_row_31
import Theorems.Thm_Couret_Certificate_class_row_32
import Theorems.Thm_Couret_Certificate_class_row_33
import Theorems.Thm_Couret_Certificate_class_row_34
import Theorems.Thm_Couret_Certificate_class_row_35
import Theorems.Thm_Couret_Certificate_class_row_36
import Theorems.Thm_Couret_Certificate_class_row_37
import Theorems.Thm_Couret_Certificate_class_row_38
import Theorems.Thm_Couret_Certificate_class_row_39
import Theorems.Thm_Couret_Certificate_class_row_4
import Theorems.Thm_Couret_Certificate_class_row_40
import Theorems.Thm_Couret_Certificate_class_row_41
import Theorems.Thm_Couret_Certificate_class_row_42
import Theorems.Thm_Couret_Certificate_class_row_43
import Theorems.Thm_Couret_Certificate_class_row_44
import Theorems.Thm_Couret_Certificate_class_row_45
import Theorems.Thm_Couret_Certificate_class_row_46
import Theorems.Thm_Couret_Certificate_class_row_47
import Theorems.Thm_Couret_Certificate_class_row_48
import Theorems.Thm_Couret_Certificate_class_row_49
import Theorems.Thm_Couret_Certificate_class_row_5
import Theorems.Thm_Couret_Certificate_class_row_50
import Theorems.Thm_Couret_Certificate_class_row_51
import Theorems.Thm_Couret_Certificate_class_row_52
import Theorems.Thm_Couret_Certificate_class_row_53
import Theorems.Thm_Couret_Certificate_class_row_54
import Theorems.Thm_Couret_Certificate_class_row_55
import Theorems.Thm_Couret_Certificate_class_row_56
import Theorems.Thm_Couret_Certificate_class_row_57
import Theorems.Thm_Couret_Certificate_class_row_58
import Theorems.Thm_Couret_Certificate_class_row_59
import Theorems.Thm_Couret_Certificate_class_row_6
import Theorems.Thm_Couret_Certificate_class_row_60
import Theorems.Thm_Couret_Certificate_class_row_61
import Theorems.Thm_Couret_Certificate_class_row_62
import Theorems.Thm_Couret_Certificate_class_row_63
import Theorems.Thm_Couret_Certificate_class_row_64
import Theorems.Thm_Couret_Certificate_class_row_65
import Theorems.Thm_Couret_Certificate_class_row_66
import Theorems.Thm_Couret_Certificate_class_row_67
import Theorems.Thm_Couret_Certificate_class_row_68
import Theorems.Thm_Couret_Certificate_class_row_69
import Theorems.Thm_Couret_Certificate_class_row_7
import Theorems.Thm_Couret_Certificate_class_row_70
import Theorems.Thm_Couret_Certificate_class_row_71
import Theorems.Thm_Couret_Certificate_class_row_72
import Theorems.Thm_Couret_Certificate_class_row_73
import Theorems.Thm_Couret_Certificate_class_row_74
import Theorems.Thm_Couret_Certificate_class_row_75
import Theorems.Thm_Couret_Certificate_class_row_76
import Theorems.Thm_Couret_Certificate_class_row_77
import Theorems.Thm_Couret_Certificate_class_row_78
import Theorems.Thm_Couret_Certificate_class_row_79
import Theorems.Thm_Couret_Certificate_class_row_8
import Theorems.Thm_Couret_Certificate_class_row_80
import Theorems.Thm_Couret_Certificate_class_row_81
import Theorems.Thm_Couret_Certificate_class_row_82
import Theorems.Thm_Couret_Certificate_class_row_83
import Theorems.Thm_Couret_Certificate_class_row_84
import Theorems.Thm_Couret_Certificate_class_row_85
import Theorems.Thm_Couret_Certificate_class_row_86
import Theorems.Thm_Couret_Certificate_class_row_87
import Theorems.Thm_Couret_Certificate_class_row_88
import Theorems.Thm_Couret_Certificate_class_row_89
import Theorems.Thm_Couret_Certificate_class_row_9
import Theorems.Thm_Couret_Certificate_class_row_90
import Theorems.Thm_Couret_Certificate_class_row_91
import Theorems.Thm_Couret_Certificate_class_row_92
import Theorems.Thm_Couret_Certificate_class_row_93
import Theorems.Thm_Couret_Certificate_class_row_94
import Theorems.Thm_Couret_Certificate_class_row_95
import Theorems.Thm_Couret_Certificate_class_row_96
import Theorems.Thm_Couret_Certificate_class_row_97
import Theorems.Thm_Couret_Certificate_class_row_98
import Theorems.Thm_Couret_Certificate_class_row_99
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate



theorem all_class_facts : ∀ c : ClassId, ClassFacts c := by
  exact (Fin.cases (class_row_0) (Fin.cases (class_row_1) (Fin.cases (class_row_2) (Fin.cases (class_row_3) (Fin.cases (class_row_4) (Fin.cases (class_row_5) (Fin.cases (class_row_6) (Fin.cases (class_row_7) (Fin.cases (class_row_8) (Fin.cases (class_row_9) (Fin.cases (class_row_10) (Fin.cases (class_row_11) (Fin.cases (class_row_12) (Fin.cases (class_row_13) (Fin.cases (class_row_14) (Fin.cases (class_row_15) (Fin.cases (class_row_16) (Fin.cases (class_row_17) (Fin.cases (class_row_18) (Fin.cases (class_row_19) (Fin.cases (class_row_20) (Fin.cases (class_row_21) (Fin.cases (class_row_22) (Fin.cases (class_row_23) (Fin.cases (class_row_24) (Fin.cases (class_row_25) (Fin.cases (class_row_26) (Fin.cases (class_row_27) (Fin.cases (class_row_28) (Fin.cases (class_row_29) (Fin.cases (class_row_30) (Fin.cases (class_row_31) (Fin.cases (class_row_32) (Fin.cases (class_row_33) (Fin.cases (class_row_34) (Fin.cases (class_row_35) (Fin.cases (class_row_36) (Fin.cases (class_row_37) (Fin.cases (class_row_38) (Fin.cases (class_row_39) (Fin.cases (class_row_40) (Fin.cases (class_row_41) (Fin.cases (class_row_42) (Fin.cases (class_row_43) (Fin.cases (class_row_44) (Fin.cases (class_row_45) (Fin.cases (class_row_46) (Fin.cases (class_row_47) (Fin.cases (class_row_48) (Fin.cases (class_row_49) (Fin.cases (class_row_50) (Fin.cases (class_row_51) (Fin.cases (class_row_52) (Fin.cases (class_row_53) (Fin.cases (class_row_54) (Fin.cases (class_row_55) (Fin.cases (class_row_56) (Fin.cases (class_row_57) (Fin.cases (class_row_58) (Fin.cases (class_row_59) (Fin.cases (class_row_60) (Fin.cases (class_row_61) (Fin.cases (class_row_62) (Fin.cases (class_row_63) (Fin.cases (class_row_64) (Fin.cases (class_row_65) (Fin.cases (class_row_66) (Fin.cases (class_row_67) (Fin.cases (class_row_68) (Fin.cases (class_row_69) (Fin.cases (class_row_70) (Fin.cases (class_row_71) (Fin.cases (class_row_72) (Fin.cases (class_row_73) (Fin.cases (class_row_74) (Fin.cases (class_row_75) (Fin.cases (class_row_76) (Fin.cases (class_row_77) (Fin.cases (class_row_78) (Fin.cases (class_row_79) (Fin.cases (class_row_80) (Fin.cases (class_row_81) (Fin.cases (class_row_82) (Fin.cases (class_row_83) (Fin.cases (class_row_84) (Fin.cases (class_row_85) (Fin.cases (class_row_86) (Fin.cases (class_row_87) (Fin.cases (class_row_88) (Fin.cases (class_row_89) (Fin.cases (class_row_90) (Fin.cases (class_row_91) (Fin.cases (class_row_92) (Fin.cases (class_row_93) (Fin.cases (class_row_94) (Fin.cases (class_row_95) (Fin.cases (class_row_96) (Fin.cases (class_row_97) (Fin.cases (class_row_98) (Fin.cases (class_row_99) (Fin.cases (class_row_100) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))













theorem p2m_local_separating_words_checked (c d : ClassId) (h : c ≠ d) : quotientOutput (quotientRun c (separatingWord c d)) ≠ quotientOutput (quotientRun d (separatingWord c d)) := (all_class_facts c).2.2.2.1 d h



end Certificate
end Couret

theorem solution : ∀ (c d : Couret.Certificate.ClassId),
  @Ne.{1} Couret.Certificate.ClassId c d →
    @Ne.{1} Nat
      (Couret.Certificate.quotientOutput (Couret.Certificate.quotientRun c (Couret.Certificate.separatingWord c d)))
      (Couret.Certificate.quotientOutput (Couret.Certificate.quotientRun d (Couret.Certificate.separatingWord c d))) := @_root_.Couret.Certificate.p2m_local_separating_words_checked

