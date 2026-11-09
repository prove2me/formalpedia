-- Prove2me | solution 1 for Couret.Certificate.transitions_checked
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:25.10332+00:00
-- url     : https://prove2.me/submissions/efbc5cfe-0cc1-4e3a-8933-0648af010814

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Theorems.Thm_Couret_Certificate_state_row_0
import Theorems.Thm_Couret_Certificate_state_row_1
import Theorems.Thm_Couret_Certificate_state_row_10
import Theorems.Thm_Couret_Certificate_state_row_100
import Theorems.Thm_Couret_Certificate_state_row_101
import Theorems.Thm_Couret_Certificate_state_row_102
import Theorems.Thm_Couret_Certificate_state_row_103
import Theorems.Thm_Couret_Certificate_state_row_104
import Theorems.Thm_Couret_Certificate_state_row_105
import Theorems.Thm_Couret_Certificate_state_row_106
import Theorems.Thm_Couret_Certificate_state_row_107
import Theorems.Thm_Couret_Certificate_state_row_108
import Theorems.Thm_Couret_Certificate_state_row_109
import Theorems.Thm_Couret_Certificate_state_row_11
import Theorems.Thm_Couret_Certificate_state_row_110
import Theorems.Thm_Couret_Certificate_state_row_111
import Theorems.Thm_Couret_Certificate_state_row_112
import Theorems.Thm_Couret_Certificate_state_row_113
import Theorems.Thm_Couret_Certificate_state_row_114
import Theorems.Thm_Couret_Certificate_state_row_115
import Theorems.Thm_Couret_Certificate_state_row_116
import Theorems.Thm_Couret_Certificate_state_row_117
import Theorems.Thm_Couret_Certificate_state_row_118
import Theorems.Thm_Couret_Certificate_state_row_119
import Theorems.Thm_Couret_Certificate_state_row_12
import Theorems.Thm_Couret_Certificate_state_row_120
import Theorems.Thm_Couret_Certificate_state_row_121
import Theorems.Thm_Couret_Certificate_state_row_122
import Theorems.Thm_Couret_Certificate_state_row_123
import Theorems.Thm_Couret_Certificate_state_row_124
import Theorems.Thm_Couret_Certificate_state_row_125
import Theorems.Thm_Couret_Certificate_state_row_126
import Theorems.Thm_Couret_Certificate_state_row_127
import Theorems.Thm_Couret_Certificate_state_row_128
import Theorems.Thm_Couret_Certificate_state_row_129
import Theorems.Thm_Couret_Certificate_state_row_13
import Theorems.Thm_Couret_Certificate_state_row_130
import Theorems.Thm_Couret_Certificate_state_row_131
import Theorems.Thm_Couret_Certificate_state_row_132
import Theorems.Thm_Couret_Certificate_state_row_133
import Theorems.Thm_Couret_Certificate_state_row_134
import Theorems.Thm_Couret_Certificate_state_row_135
import Theorems.Thm_Couret_Certificate_state_row_136
import Theorems.Thm_Couret_Certificate_state_row_137
import Theorems.Thm_Couret_Certificate_state_row_138
import Theorems.Thm_Couret_Certificate_state_row_139
import Theorems.Thm_Couret_Certificate_state_row_14
import Theorems.Thm_Couret_Certificate_state_row_140
import Theorems.Thm_Couret_Certificate_state_row_141
import Theorems.Thm_Couret_Certificate_state_row_142
import Theorems.Thm_Couret_Certificate_state_row_143
import Theorems.Thm_Couret_Certificate_state_row_144
import Theorems.Thm_Couret_Certificate_state_row_145
import Theorems.Thm_Couret_Certificate_state_row_146
import Theorems.Thm_Couret_Certificate_state_row_15
import Theorems.Thm_Couret_Certificate_state_row_16
import Theorems.Thm_Couret_Certificate_state_row_17
import Theorems.Thm_Couret_Certificate_state_row_18
import Theorems.Thm_Couret_Certificate_state_row_19
import Theorems.Thm_Couret_Certificate_state_row_2
import Theorems.Thm_Couret_Certificate_state_row_20
import Theorems.Thm_Couret_Certificate_state_row_21
import Theorems.Thm_Couret_Certificate_state_row_22
import Theorems.Thm_Couret_Certificate_state_row_23
import Theorems.Thm_Couret_Certificate_state_row_24
import Theorems.Thm_Couret_Certificate_state_row_25
import Theorems.Thm_Couret_Certificate_state_row_26
import Theorems.Thm_Couret_Certificate_state_row_27
import Theorems.Thm_Couret_Certificate_state_row_28
import Theorems.Thm_Couret_Certificate_state_row_29
import Theorems.Thm_Couret_Certificate_state_row_3
import Theorems.Thm_Couret_Certificate_state_row_30
import Theorems.Thm_Couret_Certificate_state_row_31
import Theorems.Thm_Couret_Certificate_state_row_32
import Theorems.Thm_Couret_Certificate_state_row_33
import Theorems.Thm_Couret_Certificate_state_row_34
import Theorems.Thm_Couret_Certificate_state_row_35
import Theorems.Thm_Couret_Certificate_state_row_36
import Theorems.Thm_Couret_Certificate_state_row_37
import Theorems.Thm_Couret_Certificate_state_row_38
import Theorems.Thm_Couret_Certificate_state_row_39
import Theorems.Thm_Couret_Certificate_state_row_4
import Theorems.Thm_Couret_Certificate_state_row_40
import Theorems.Thm_Couret_Certificate_state_row_41
import Theorems.Thm_Couret_Certificate_state_row_42
import Theorems.Thm_Couret_Certificate_state_row_43
import Theorems.Thm_Couret_Certificate_state_row_44
import Theorems.Thm_Couret_Certificate_state_row_45
import Theorems.Thm_Couret_Certificate_state_row_46
import Theorems.Thm_Couret_Certificate_state_row_47
import Theorems.Thm_Couret_Certificate_state_row_48
import Theorems.Thm_Couret_Certificate_state_row_49
import Theorems.Thm_Couret_Certificate_state_row_5
import Theorems.Thm_Couret_Certificate_state_row_50
import Theorems.Thm_Couret_Certificate_state_row_51
import Theorems.Thm_Couret_Certificate_state_row_52
import Theorems.Thm_Couret_Certificate_state_row_53
import Theorems.Thm_Couret_Certificate_state_row_54
import Theorems.Thm_Couret_Certificate_state_row_55
import Theorems.Thm_Couret_Certificate_state_row_56
import Theorems.Thm_Couret_Certificate_state_row_57
import Theorems.Thm_Couret_Certificate_state_row_58
import Theorems.Thm_Couret_Certificate_state_row_59
import Theorems.Thm_Couret_Certificate_state_row_6
import Theorems.Thm_Couret_Certificate_state_row_60
import Theorems.Thm_Couret_Certificate_state_row_61
import Theorems.Thm_Couret_Certificate_state_row_62
import Theorems.Thm_Couret_Certificate_state_row_63
import Theorems.Thm_Couret_Certificate_state_row_64
import Theorems.Thm_Couret_Certificate_state_row_65
import Theorems.Thm_Couret_Certificate_state_row_66
import Theorems.Thm_Couret_Certificate_state_row_67
import Theorems.Thm_Couret_Certificate_state_row_68
import Theorems.Thm_Couret_Certificate_state_row_69
import Theorems.Thm_Couret_Certificate_state_row_7
import Theorems.Thm_Couret_Certificate_state_row_70
import Theorems.Thm_Couret_Certificate_state_row_71
import Theorems.Thm_Couret_Certificate_state_row_72
import Theorems.Thm_Couret_Certificate_state_row_73
import Theorems.Thm_Couret_Certificate_state_row_74
import Theorems.Thm_Couret_Certificate_state_row_75
import Theorems.Thm_Couret_Certificate_state_row_76
import Theorems.Thm_Couret_Certificate_state_row_77
import Theorems.Thm_Couret_Certificate_state_row_78
import Theorems.Thm_Couret_Certificate_state_row_79
import Theorems.Thm_Couret_Certificate_state_row_8
import Theorems.Thm_Couret_Certificate_state_row_80
import Theorems.Thm_Couret_Certificate_state_row_81
import Theorems.Thm_Couret_Certificate_state_row_82
import Theorems.Thm_Couret_Certificate_state_row_83
import Theorems.Thm_Couret_Certificate_state_row_84
import Theorems.Thm_Couret_Certificate_state_row_85
import Theorems.Thm_Couret_Certificate_state_row_86
import Theorems.Thm_Couret_Certificate_state_row_87
import Theorems.Thm_Couret_Certificate_state_row_88
import Theorems.Thm_Couret_Certificate_state_row_89
import Theorems.Thm_Couret_Certificate_state_row_9
import Theorems.Thm_Couret_Certificate_state_row_90
import Theorems.Thm_Couret_Certificate_state_row_91
import Theorems.Thm_Couret_Certificate_state_row_92
import Theorems.Thm_Couret_Certificate_state_row_93
import Theorems.Thm_Couret_Certificate_state_row_94
import Theorems.Thm_Couret_Certificate_state_row_95
import Theorems.Thm_Couret_Certificate_state_row_96
import Theorems.Thm_Couret_Certificate_state_row_97
import Theorems.Thm_Couret_Certificate_state_row_98
import Theorems.Thm_Couret_Certificate_state_row_99
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

theorem all_state_facts : ∀ i : StateId, StateFacts i := by
  exact (Fin.cases (state_row_0) (Fin.cases (state_row_1) (Fin.cases (state_row_2) (Fin.cases (state_row_3) (Fin.cases (state_row_4) (Fin.cases (state_row_5) (Fin.cases (state_row_6) (Fin.cases (state_row_7) (Fin.cases (state_row_8) (Fin.cases (state_row_9) (Fin.cases (state_row_10) (Fin.cases (state_row_11) (Fin.cases (state_row_12) (Fin.cases (state_row_13) (Fin.cases (state_row_14) (Fin.cases (state_row_15) (Fin.cases (state_row_16) (Fin.cases (state_row_17) (Fin.cases (state_row_18) (Fin.cases (state_row_19) (Fin.cases (state_row_20) (Fin.cases (state_row_21) (Fin.cases (state_row_22) (Fin.cases (state_row_23) (Fin.cases (state_row_24) (Fin.cases (state_row_25) (Fin.cases (state_row_26) (Fin.cases (state_row_27) (Fin.cases (state_row_28) (Fin.cases (state_row_29) (Fin.cases (state_row_30) (Fin.cases (state_row_31) (Fin.cases (state_row_32) (Fin.cases (state_row_33) (Fin.cases (state_row_34) (Fin.cases (state_row_35) (Fin.cases (state_row_36) (Fin.cases (state_row_37) (Fin.cases (state_row_38) (Fin.cases (state_row_39) (Fin.cases (state_row_40) (Fin.cases (state_row_41) (Fin.cases (state_row_42) (Fin.cases (state_row_43) (Fin.cases (state_row_44) (Fin.cases (state_row_45) (Fin.cases (state_row_46) (Fin.cases (state_row_47) (Fin.cases (state_row_48) (Fin.cases (state_row_49) (Fin.cases (state_row_50) (Fin.cases (state_row_51) (Fin.cases (state_row_52) (Fin.cases (state_row_53) (Fin.cases (state_row_54) (Fin.cases (state_row_55) (Fin.cases (state_row_56) (Fin.cases (state_row_57) (Fin.cases (state_row_58) (Fin.cases (state_row_59) (Fin.cases (state_row_60) (Fin.cases (state_row_61) (Fin.cases (state_row_62) (Fin.cases (state_row_63) (Fin.cases (state_row_64) (Fin.cases (state_row_65) (Fin.cases (state_row_66) (Fin.cases (state_row_67) (Fin.cases (state_row_68) (Fin.cases (state_row_69) (Fin.cases (state_row_70) (Fin.cases (state_row_71) (Fin.cases (state_row_72) (Fin.cases (state_row_73) (Fin.cases (state_row_74) (Fin.cases (state_row_75) (Fin.cases (state_row_76) (Fin.cases (state_row_77) (Fin.cases (state_row_78) (Fin.cases (state_row_79) (Fin.cases (state_row_80) (Fin.cases (state_row_81) (Fin.cases (state_row_82) (Fin.cases (state_row_83) (Fin.cases (state_row_84) (Fin.cases (state_row_85) (Fin.cases (state_row_86) (Fin.cases (state_row_87) (Fin.cases (state_row_88) (Fin.cases (state_row_89) (Fin.cases (state_row_90) (Fin.cases (state_row_91) (Fin.cases (state_row_92) (Fin.cases (state_row_93) (Fin.cases (state_row_94) (Fin.cases (state_row_95) (Fin.cases (state_row_96) (Fin.cases (state_row_97) (Fin.cases (state_row_98) (Fin.cases (state_row_99) (Fin.cases (state_row_100) (Fin.cases (state_row_101) (Fin.cases (state_row_102) (Fin.cases (state_row_103) (Fin.cases (state_row_104) (Fin.cases (state_row_105) (Fin.cases (state_row_106) (Fin.cases (state_row_107) (Fin.cases (state_row_108) (Fin.cases (state_row_109) (Fin.cases (state_row_110) (Fin.cases (state_row_111) (Fin.cases (state_row_112) (Fin.cases (state_row_113) (Fin.cases (state_row_114) (Fin.cases (state_row_115) (Fin.cases (state_row_116) (Fin.cases (state_row_117) (Fin.cases (state_row_118) (Fin.cases (state_row_119) (Fin.cases (state_row_120) (Fin.cases (state_row_121) (Fin.cases (state_row_122) (Fin.cases (state_row_123) (Fin.cases (state_row_124) (Fin.cases (state_row_125) (Fin.cases (state_row_126) (Fin.cases (state_row_127) (Fin.cases (state_row_128) (Fin.cases (state_row_129) (Fin.cases (state_row_130) (Fin.cases (state_row_131) (Fin.cases (state_row_132) (Fin.cases (state_row_133) (Fin.cases (state_row_134) (Fin.cases (state_row_135) (Fin.cases (state_row_136) (Fin.cases (state_row_137) (Fin.cases (state_row_138) (Fin.cases (state_row_139) (Fin.cases (state_row_140) (Fin.cases (state_row_141) (Fin.cases (state_row_142) (Fin.cases (state_row_143) (Fin.cases (state_row_144) (Fin.cases (state_row_145) (Fin.cases (state_row_146) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))








theorem p2m_local_transitions_checked (i : StateId) (g : Symbol) : StepValid (entry i) (entry (tableNext i g)) g := (all_state_facts i).2.2.2.2.1 g










end Certificate
end Couret

theorem solution : ∀ (i : Couret.Certificate.StateId) (g : Couret.Certificate.Symbol),
  Couret.Certificate.StepValid (Couret.Certificate.entry i)
    (Couret.Certificate.entry (Couret.Certificate.tableNext i g)) g := @_root_.Couret.Certificate.p2m_local_transitions_checked

