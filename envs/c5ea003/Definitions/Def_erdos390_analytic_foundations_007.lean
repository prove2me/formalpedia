-- Prove2me | Definitions.Def_erdos390_analytic_foundations_007
-- name    : erdos390_analytic_foundations_007
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T15:00:06.37597+00:00
-- url     : https://prove2.me/theorems/4d1ca18d-e60a-4630-9724-785d31002ee1
-- title:
--   Stationary anchors, tangent requests and collision events
-- statement:
--   This bundle defines the finite allocation sets and stationary-prefix cofactor routing objects, explicit prime-interval bound quantities, anchor/precharge bookkeeping, raw correction-pool densities, tangent-flow algebra, split requests, clean multiplier lists, and the finite probability spaces used to study endpoint collisions.
--
--   For a finite directed flow $F$ on labels, its divergence records outgoing mass minus incoming mass:
--   $$\operatorname{div}F(v)=\sum_wF(v,w)-\sum_wF(w,v).$$
--   A split request has a source label $u_j$, target label $v_j$, mass and a finite list of allowed common multipliers. A choice $m_j$ produces numerical endpoints $u_jm_j$ and $v_jm_j$; collision events express equality between endpoints of distinct requests. The bundle defines uniform product choice measures and the associated collision counts, local loads and census budgets.
--
--   It also names selector valuation deficits and the predicates for prime-band balance, support of the deficit and integral complete-rough-row sums. These definitions expose the precise finite objects needed by collision-free selection and tangent-correction theorems; the endpoint-distinctness predicate is a condition to be established.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/TangentCollisionCounting.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.WholePaper.AllocationCertificateRowChecks1, Erdos390.WholePaper.AllocationCertificateRowChecks2, Erdos390.WholePaper.AllocationCertificateRowChecks3, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006


/- Source module: Erdos390.WholePaper.AllocationCertificateRowChecks1 -/
section


/-! Bounded kernel checks for the finite allocation certificate (row batch 1). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawRowCrossEq_1 :
    (rawRowMass 1).CrossEq (rawAlpha 1) := by decide
@[simp] theorem rawRowCrossEq_2 :
    (rawRowMass 2).CrossEq (rawAlpha 2) := by decide
@[simp] theorem rawRowCrossEq_3 :
    (rawRowMass 3).CrossEq (rawAlpha 3) := by decide
@[simp] theorem rawRowCrossEq_4 :
    (rawRowMass 4).CrossEq (rawAlpha 4) := by decide
@[simp] theorem rawRowCrossEq_5 :
    (rawRowMass 5).CrossEq (rawAlpha 5) := by decide
@[simp] theorem rawRowCrossEq_6 :
    (rawRowMass 6).CrossEq (rawAlpha 6) := by decide
@[simp] theorem rawRowCrossEq_7 :
    (rawRowMass 7).CrossEq (rawAlpha 7) := by decide
@[simp] theorem rawRowCrossEq_8 :
    (rawRowMass 8).CrossEq (rawAlpha 8) := by decide
@[simp] theorem rawRowCrossEq_9 :
    (rawRowMass 9).CrossEq (rawAlpha 9) := by decide
@[simp] theorem rawRowCrossEq_10 :
    (rawRowMass 10).CrossEq (rawAlpha 10) := by decide
@[simp] theorem rawRowCrossEq_11 :
    (rawRowMass 11).CrossEq (rawAlpha 11) := by decide
@[simp] theorem rawRowCrossEq_12 :
    (rawRowMass 12).CrossEq (rawAlpha 12) := by decide
@[simp] theorem rawRowCrossEq_13 :
    (rawRowMass 13).CrossEq (rawAlpha 13) := by decide
@[simp] theorem rawRowCrossEq_14 :
    (rawRowMass 14).CrossEq (rawAlpha 14) := by decide
@[simp] theorem rawRowCrossEq_15 :
    (rawRowMass 15).CrossEq (rawAlpha 15) := by decide
@[simp] theorem rawRowCrossEq_16 :
    (rawRowMass 16).CrossEq (rawAlpha 16) := by decide
@[simp] theorem rawRowCrossEq_17 :
    (rawRowMass 17).CrossEq (rawAlpha 17) := by decide
@[simp] theorem rawRowCrossEq_18 :
    (rawRowMass 18).CrossEq (rawAlpha 18) := by decide
@[simp] theorem rawRowCrossEq_19 :
    (rawRowMass 19).CrossEq (rawAlpha 19) := by decide
@[simp] theorem rawRowCrossEq_20 :
    (rawRowMass 20).CrossEq (rawAlpha 20) := by decide
@[simp] theorem rawRowCrossEq_21 :
    (rawRowMass 21).CrossEq (rawAlpha 21) := by decide
@[simp] theorem rawRowCrossEq_22 :
    (rawRowMass 22).CrossEq (rawAlpha 22) := by decide
@[simp] theorem rawRowCrossEq_23 :
    (rawRowMass 23).CrossEq (rawAlpha 23) := by decide
@[simp] theorem rawRowCrossEq_24 :
    (rawRowMass 24).CrossEq (rawAlpha 24) := by decide
@[simp] theorem rawRowCrossEq_25 :
    (rawRowMass 25).CrossEq (rawAlpha 25) := by decide
@[simp] theorem rawRowCrossEq_26 :
    (rawRowMass 26).CrossEq (rawAlpha 26) := by decide
@[simp] theorem rawRowCrossEq_27 :
    (rawRowMass 27).CrossEq (rawAlpha 27) := by decide
@[simp] theorem rawRowCrossEq_28 :
    (rawRowMass 28).CrossEq (rawAlpha 28) := by decide
@[simp] theorem rawRowCrossEq_29 :
    (rawRowMass 29).CrossEq (rawAlpha 29) := by decide
@[simp] theorem rawRowCrossEq_30 :
    (rawRowMass 30).CrossEq (rawAlpha 30) := by decide
@[simp] theorem rawRowCrossEq_31 :
    (rawRowMass 31).CrossEq (rawAlpha 31) := by decide
@[simp] theorem rawRowCrossEq_32 :
    (rawRowMass 32).CrossEq (rawAlpha 32) := by decide
@[simp] theorem rawRowCrossEq_33 :
    (rawRowMass 33).CrossEq (rawAlpha 33) := by decide
@[simp] theorem rawRowCrossEq_34 :
    (rawRowMass 34).CrossEq (rawAlpha 34) := by decide
@[simp] theorem rawRowCrossEq_35 :
    (rawRowMass 35).CrossEq (rawAlpha 35) := by decide
@[simp] theorem rawRowCrossEq_36 :
    (rawRowMass 36).CrossEq (rawAlpha 36) := by decide
@[simp] theorem rawRowCrossEq_37 :
    (rawRowMass 37).CrossEq (rawAlpha 37) := by decide
@[simp] theorem rawRowCrossEq_38 :
    (rawRowMass 38).CrossEq (rawAlpha 38) := by decide
@[simp] theorem rawRowCrossEq_39 :
    (rawRowMass 39).CrossEq (rawAlpha 39) := by decide
@[simp] theorem rawRowCrossEq_40 :
    (rawRowMass 40).CrossEq (rawAlpha 40) := by decide
@[simp] theorem rawRowCrossEq_41 :
    (rawRowMass 41).CrossEq (rawAlpha 41) := by decide
@[simp] theorem rawRowCrossEq_42 :
    (rawRowMass 42).CrossEq (rawAlpha 42) := by decide
@[simp] theorem rawRowCrossEq_43 :
    (rawRowMass 43).CrossEq (rawAlpha 43) := by decide
@[simp] theorem rawRowCrossEq_44 :
    (rawRowMass 44).CrossEq (rawAlpha 44) := by decide
@[simp] theorem rawRowCrossEq_45 :
    (rawRowMass 45).CrossEq (rawAlpha 45) := by decide
@[simp] theorem rawRowCrossEq_46 :
    (rawRowMass 46).CrossEq (rawAlpha 46) := by decide
@[simp] theorem rawRowCrossEq_47 :
    (rawRowMass 47).CrossEq (rawAlpha 47) := by decide
@[simp] theorem rawRowCrossEq_48 :
    (rawRowMass 48).CrossEq (rawAlpha 48) := by decide
@[simp] theorem rawRowCrossEq_49 :
    (rawRowMass 49).CrossEq (rawAlpha 49) := by decide
@[simp] theorem rawRowCrossEq_50 :
    (rawRowMass 50).CrossEq (rawAlpha 50) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateRowChecks2 -/
section


/-! Bounded kernel checks for the finite allocation certificate (row batch 2). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawRowCrossEq_51 :
    (rawRowMass 51).CrossEq (rawAlpha 51) := by decide
@[simp] theorem rawRowCrossEq_52 :
    (rawRowMass 52).CrossEq (rawAlpha 52) := by decide
@[simp] theorem rawRowCrossEq_53 :
    (rawRowMass 53).CrossEq (rawAlpha 53) := by decide
@[simp] theorem rawRowCrossEq_54 :
    (rawRowMass 54).CrossEq (rawAlpha 54) := by decide
@[simp] theorem rawRowCrossEq_55 :
    (rawRowMass 55).CrossEq (rawAlpha 55) := by decide
@[simp] theorem rawRowCrossEq_56 :
    (rawRowMass 56).CrossEq (rawAlpha 56) := by decide
@[simp] theorem rawRowCrossEq_57 :
    (rawRowMass 57).CrossEq (rawAlpha 57) := by decide
@[simp] theorem rawRowCrossEq_58 :
    (rawRowMass 58).CrossEq (rawAlpha 58) := by decide
@[simp] theorem rawRowCrossEq_59 :
    (rawRowMass 59).CrossEq (rawAlpha 59) := by decide
@[simp] theorem rawRowCrossEq_60 :
    (rawRowMass 60).CrossEq (rawAlpha 60) := by decide
@[simp] theorem rawRowCrossEq_61 :
    (rawRowMass 61).CrossEq (rawAlpha 61) := by decide
@[simp] theorem rawRowCrossEq_62 :
    (rawRowMass 62).CrossEq (rawAlpha 62) := by decide
@[simp] theorem rawRowCrossEq_63 :
    (rawRowMass 63).CrossEq (rawAlpha 63) := by decide
@[simp] theorem rawRowCrossEq_64 :
    (rawRowMass 64).CrossEq (rawAlpha 64) := by decide
@[simp] theorem rawRowCrossEq_65 :
    (rawRowMass 65).CrossEq (rawAlpha 65) := by decide
@[simp] theorem rawRowCrossEq_66 :
    (rawRowMass 66).CrossEq (rawAlpha 66) := by decide
@[simp] theorem rawRowCrossEq_67 :
    (rawRowMass 67).CrossEq (rawAlpha 67) := by decide
@[simp] theorem rawRowCrossEq_68 :
    (rawRowMass 68).CrossEq (rawAlpha 68) := by decide
@[simp] theorem rawRowCrossEq_69 :
    (rawRowMass 69).CrossEq (rawAlpha 69) := by decide
@[simp] theorem rawRowCrossEq_70 :
    (rawRowMass 70).CrossEq (rawAlpha 70) := by decide
@[simp] theorem rawRowCrossEq_71 :
    (rawRowMass 71).CrossEq (rawAlpha 71) := by decide
@[simp] theorem rawRowCrossEq_72 :
    (rawRowMass 72).CrossEq (rawAlpha 72) := by decide
@[simp] theorem rawRowCrossEq_73 :
    (rawRowMass 73).CrossEq (rawAlpha 73) := by decide
@[simp] theorem rawRowCrossEq_74 :
    (rawRowMass 74).CrossEq (rawAlpha 74) := by decide
@[simp] theorem rawRowCrossEq_75 :
    (rawRowMass 75).CrossEq (rawAlpha 75) := by decide
@[simp] theorem rawRowCrossEq_76 :
    (rawRowMass 76).CrossEq (rawAlpha 76) := by decide
@[simp] theorem rawRowCrossEq_77 :
    (rawRowMass 77).CrossEq (rawAlpha 77) := by decide
@[simp] theorem rawRowCrossEq_78 :
    (rawRowMass 78).CrossEq (rawAlpha 78) := by decide
@[simp] theorem rawRowCrossEq_79 :
    (rawRowMass 79).CrossEq (rawAlpha 79) := by decide
@[simp] theorem rawRowCrossEq_80 :
    (rawRowMass 80).CrossEq (rawAlpha 80) := by decide
@[simp] theorem rawRowCrossEq_81 :
    (rawRowMass 81).CrossEq (rawAlpha 81) := by decide
@[simp] theorem rawRowCrossEq_82 :
    (rawRowMass 82).CrossEq (rawAlpha 82) := by decide
@[simp] theorem rawRowCrossEq_83 :
    (rawRowMass 83).CrossEq (rawAlpha 83) := by decide
@[simp] theorem rawRowCrossEq_84 :
    (rawRowMass 84).CrossEq (rawAlpha 84) := by decide
@[simp] theorem rawRowCrossEq_85 :
    (rawRowMass 85).CrossEq (rawAlpha 85) := by decide
@[simp] theorem rawRowCrossEq_86 :
    (rawRowMass 86).CrossEq (rawAlpha 86) := by decide
@[simp] theorem rawRowCrossEq_87 :
    (rawRowMass 87).CrossEq (rawAlpha 87) := by decide
@[simp] theorem rawRowCrossEq_88 :
    (rawRowMass 88).CrossEq (rawAlpha 88) := by decide
@[simp] theorem rawRowCrossEq_89 :
    (rawRowMass 89).CrossEq (rawAlpha 89) := by decide
@[simp] theorem rawRowCrossEq_90 :
    (rawRowMass 90).CrossEq (rawAlpha 90) := by decide
@[simp] theorem rawRowCrossEq_91 :
    (rawRowMass 91).CrossEq (rawAlpha 91) := by decide
@[simp] theorem rawRowCrossEq_92 :
    (rawRowMass 92).CrossEq (rawAlpha 92) := by decide
@[simp] theorem rawRowCrossEq_93 :
    (rawRowMass 93).CrossEq (rawAlpha 93) := by decide
@[simp] theorem rawRowCrossEq_94 :
    (rawRowMass 94).CrossEq (rawAlpha 94) := by decide
@[simp] theorem rawRowCrossEq_95 :
    (rawRowMass 95).CrossEq (rawAlpha 95) := by decide
@[simp] theorem rawRowCrossEq_96 :
    (rawRowMass 96).CrossEq (rawAlpha 96) := by decide
@[simp] theorem rawRowCrossEq_97 :
    (rawRowMass 97).CrossEq (rawAlpha 97) := by decide
@[simp] theorem rawRowCrossEq_98 :
    (rawRowMass 98).CrossEq (rawAlpha 98) := by decide
@[simp] theorem rawRowCrossEq_99 :
    (rawRowMass 99).CrossEq (rawAlpha 99) := by decide
@[simp] theorem rawRowCrossEq_100 :
    (rawRowMass 100).CrossEq (rawAlpha 100) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateRowChecks3 -/
section


/-! Bounded kernel checks for the finite allocation certificate (row batch 3). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawRowCrossEq_101 :
    (rawRowMass 101).CrossEq (rawAlpha 101) := by decide
@[simp] theorem rawRowCrossEq_102 :
    (rawRowMass 102).CrossEq (rawAlpha 102) := by decide
@[simp] theorem rawRowCrossEq_103 :
    (rawRowMass 103).CrossEq (rawAlpha 103) := by decide
@[simp] theorem rawRowCrossEq_104 :
    (rawRowMass 104).CrossEq (rawAlpha 104) := by decide
@[simp] theorem rawRowCrossEq_105 :
    (rawRowMass 105).CrossEq (rawAlpha 105) := by decide
@[simp] theorem rawRowCrossEq_106 :
    (rawRowMass 106).CrossEq (rawAlpha 106) := by decide
@[simp] theorem rawRowCrossEq_107 :
    (rawRowMass 107).CrossEq (rawAlpha 107) := by decide
@[simp] theorem rawRowCrossEq_108 :
    (rawRowMass 108).CrossEq (rawAlpha 108) := by decide
@[simp] theorem rawRowCrossEq_109 :
    (rawRowMass 109).CrossEq (rawAlpha 109) := by decide
@[simp] theorem rawRowCrossEq_110 :
    (rawRowMass 110).CrossEq (rawAlpha 110) := by decide
@[simp] theorem rawRowCrossEq_111 :
    (rawRowMass 111).CrossEq (rawAlpha 111) := by decide
@[simp] theorem rawRowCrossEq_112 :
    (rawRowMass 112).CrossEq (rawAlpha 112) := by decide
@[simp] theorem rawRowCrossEq_113 :
    (rawRowMass 113).CrossEq (rawAlpha 113) := by decide
@[simp] theorem rawRowCrossEq_114 :
    (rawRowMass 114).CrossEq (rawAlpha 114) := by decide
@[simp] theorem rawRowCrossEq_115 :
    (rawRowMass 115).CrossEq (rawAlpha 115) := by decide
@[simp] theorem rawRowCrossEq_116 :
    (rawRowMass 116).CrossEq (rawAlpha 116) := by decide
@[simp] theorem rawRowCrossEq_117 :
    (rawRowMass 117).CrossEq (rawAlpha 117) := by decide
@[simp] theorem rawRowCrossEq_118 :
    (rawRowMass 118).CrossEq (rawAlpha 118) := by decide
@[simp] theorem rawRowCrossEq_119 :
    (rawRowMass 119).CrossEq (rawAlpha 119) := by decide
@[simp] theorem rawRowCrossEq_120 :
    (rawRowMass 120).CrossEq (rawAlpha 120) := by decide
@[simp] theorem rawRowCrossEq_121 :
    (rawRowMass 121).CrossEq (rawAlpha 121) := by decide
@[simp] theorem rawRowCrossEq_122 :
    (rawRowMass 122).CrossEq (rawAlpha 122) := by decide
@[simp] theorem rawRowCrossEq_123 :
    (rawRowMass 123).CrossEq (rawAlpha 123) := by decide
@[simp] theorem rawRowCrossEq_124 :
    (rawRowMass 124).CrossEq (rawAlpha 124) := by decide
@[simp] theorem rawRowCrossEq_125 :
    (rawRowMass 125).CrossEq (rawAlpha 125) := by decide
@[simp] theorem rawRowCrossEq_126 :
    (rawRowMass 126).CrossEq (rawAlpha 126) := by decide
@[simp] theorem rawRowCrossEq_127 :
    (rawRowMass 127).CrossEq (rawAlpha 127) := by decide
@[simp] theorem rawRowCrossEq_128 :
    (rawRowMass 128).CrossEq (rawAlpha 128) := by decide
@[simp] theorem rawRowCrossEq_129 :
    (rawRowMass 129).CrossEq (rawAlpha 129) := by decide
@[simp] theorem rawRowCrossEq_130 :
    (rawRowMass 130).CrossEq (rawAlpha 130) := by decide
@[simp] theorem rawRowCrossEq_131 :
    (rawRowMass 131).CrossEq (rawAlpha 131) := by decide
@[simp] theorem rawRowCrossEq_132 :
    (rawRowMass 132).CrossEq (rawAlpha 132) := by decide
@[simp] theorem rawRowCrossEq_133 :
    (rawRowMass 133).CrossEq (rawAlpha 133) := by decide
@[simp] theorem rawRowCrossEq_134 :
    (rawRowMass 134).CrossEq (rawAlpha 134) := by decide
@[simp] theorem rawRowCrossEq_135 :
    (rawRowMass 135).CrossEq (rawAlpha 135) := by decide
@[simp] theorem rawRowCrossEq_136 :
    (rawRowMass 136).CrossEq (rawAlpha 136) := by decide
@[simp] theorem rawRowCrossEq_137 :
    (rawRowMass 137).CrossEq (rawAlpha 137) := by decide
@[simp] theorem rawRowCrossEq_138 :
    (rawRowMass 138).CrossEq (rawAlpha 138) := by decide
@[simp] theorem rawRowCrossEq_139 :
    (rawRowMass 139).CrossEq (rawAlpha 139) := by decide
@[simp] theorem rawRowCrossEq_140 :
    (rawRowMass 140).CrossEq (rawAlpha 140) := by decide
@[simp] theorem rawRowCrossEq_141 :
    (rawRowMass 141).CrossEq (rawAlpha 141) := by decide
@[simp] theorem rawRowCrossEq_142 :
    (rawRowMass 142).CrossEq (rawAlpha 142) := by decide
@[simp] theorem rawRowCrossEq_143 :
    (rawRowMass 143).CrossEq (rawAlpha 143) := by decide
@[simp] theorem rawRowCrossEq_144 :
    (rawRowMass 144).CrossEq (rawAlpha 144) := by decide
@[simp] theorem rawRowCrossEq_145 :
    (rawRowMass 145).CrossEq (rawAlpha 145) := by decide
@[simp] theorem rawRowCrossEq_146 :
    (rawRowMass 146).CrossEq (rawAlpha 146) := by decide
@[simp] theorem rawRowCrossEq_147 :
    (rawRowMass 147).CrossEq (rawAlpha 147) := by decide
@[simp] theorem rawRowCrossEq_148 :
    (rawRowMass 148).CrossEq (rawAlpha 148) := by decide
@[simp] theorem rawRowCrossEq_149 :
    (rawRowMass 149).CrossEq (rawAlpha 149) := by decide
@[simp] theorem rawRowCrossEq_150 :
    (rawRowMass 150).CrossEq (rawAlpha 150) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateRowChecks4 -/
section


/-! Bounded kernel checks for the finite allocation certificate (row batch 4). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawRowCrossEq_151 :
    (rawRowMass 151).CrossEq (rawAlpha 151) := by decide
@[simp] theorem rawRowCrossEq_152 :
    (rawRowMass 152).CrossEq (rawAlpha 152) := by decide
@[simp] theorem rawRowCrossEq_153 :
    (rawRowMass 153).CrossEq (rawAlpha 153) := by decide
@[simp] theorem rawRowCrossEq_154 :
    (rawRowMass 154).CrossEq (rawAlpha 154) := by decide
@[simp] theorem rawRowCrossEq_155 :
    (rawRowMass 155).CrossEq (rawAlpha 155) := by decide
@[simp] theorem rawRowCrossEq_156 :
    (rawRowMass 156).CrossEq (rawAlpha 156) := by decide
@[simp] theorem rawRowCrossEq_157 :
    (rawRowMass 157).CrossEq (rawAlpha 157) := by decide
@[simp] theorem rawRowCrossEq_158 :
    (rawRowMass 158).CrossEq (rawAlpha 158) := by decide
@[simp] theorem rawRowCrossEq_159 :
    (rawRowMass 159).CrossEq (rawAlpha 159) := by decide
@[simp] theorem rawRowCrossEq_160 :
    (rawRowMass 160).CrossEq (rawAlpha 160) := by decide
@[simp] theorem rawRowCrossEq_161 :
    (rawRowMass 161).CrossEq (rawAlpha 161) := by decide
@[simp] theorem rawRowCrossEq_162 :
    (rawRowMass 162).CrossEq (rawAlpha 162) := by decide
@[simp] theorem rawRowCrossEq_163 :
    (rawRowMass 163).CrossEq (rawAlpha 163) := by decide
@[simp] theorem rawRowCrossEq_164 :
    (rawRowMass 164).CrossEq (rawAlpha 164) := by decide
@[simp] theorem rawRowCrossEq_165 :
    (rawRowMass 165).CrossEq (rawAlpha 165) := by decide
@[simp] theorem rawRowCrossEq_166 :
    (rawRowMass 166).CrossEq (rawAlpha 166) := by decide
@[simp] theorem rawRowCrossEq_167 :
    (rawRowMass 167).CrossEq (rawAlpha 167) := by decide
@[simp] theorem rawRowCrossEq_168 :
    (rawRowMass 168).CrossEq (rawAlpha 168) := by decide
@[simp] theorem rawRowCrossEq_169 :
    (rawRowMass 169).CrossEq (rawAlpha 169) := by decide
@[simp] theorem rawRowCrossEq_170 :
    (rawRowMass 170).CrossEq (rawAlpha 170) := by decide
@[simp] theorem rawRowCrossEq_171 :
    (rawRowMass 171).CrossEq (rawAlpha 171) := by decide
@[simp] theorem rawRowCrossEq_172 :
    (rawRowMass 172).CrossEq (rawAlpha 172) := by decide
@[simp] theorem rawRowCrossEq_173 :
    (rawRowMass 173).CrossEq (rawAlpha 173) := by decide
@[simp] theorem rawRowCrossEq_174 :
    (rawRowMass 174).CrossEq (rawAlpha 174) := by decide
@[simp] theorem rawRowCrossEq_175 :
    (rawRowMass 175).CrossEq (rawAlpha 175) := by decide
@[simp] theorem rawRowCrossEq_176 :
    (rawRowMass 176).CrossEq (rawAlpha 176) := by decide
@[simp] theorem rawRowCrossEq_177 :
    (rawRowMass 177).CrossEq (rawAlpha 177) := by decide
@[simp] theorem rawRowCrossEq_178 :
    (rawRowMass 178).CrossEq (rawAlpha 178) := by decide
@[simp] theorem rawRowCrossEq_179 :
    (rawRowMass 179).CrossEq (rawAlpha 179) := by decide
@[simp] theorem rawRowCrossEq_180 :
    (rawRowMass 180).CrossEq (rawAlpha 180) := by decide
@[simp] theorem rawRowCrossEq_181 :
    (rawRowMass 181).CrossEq (rawAlpha 181) := by decide
@[simp] theorem rawRowCrossEq_182 :
    (rawRowMass 182).CrossEq (rawAlpha 182) := by decide
@[simp] theorem rawRowCrossEq_183 :
    (rawRowMass 183).CrossEq (rawAlpha 183) := by decide
@[simp] theorem rawRowCrossEq_184 :
    (rawRowMass 184).CrossEq (rawAlpha 184) := by decide
@[simp] theorem rawRowCrossEq_185 :
    (rawRowMass 185).CrossEq (rawAlpha 185) := by decide
@[simp] theorem rawRowCrossEq_186 :
    (rawRowMass 186).CrossEq (rawAlpha 186) := by decide
@[simp] theorem rawRowCrossEq_187 :
    (rawRowMass 187).CrossEq (rawAlpha 187) := by decide
@[simp] theorem rawRowCrossEq_188 :
    (rawRowMass 188).CrossEq (rawAlpha 188) := by decide
@[simp] theorem rawRowCrossEq_189 :
    (rawRowMass 189).CrossEq (rawAlpha 189) := by decide
@[simp] theorem rawRowCrossEq_190 :
    (rawRowMass 190).CrossEq (rawAlpha 190) := by decide
@[simp] theorem rawRowCrossEq_191 :
    (rawRowMass 191).CrossEq (rawAlpha 191) := by decide
@[simp] theorem rawRowCrossEq_192 :
    (rawRowMass 192).CrossEq (rawAlpha 192) := by decide
@[simp] theorem rawRowCrossEq_193 :
    (rawRowMass 193).CrossEq (rawAlpha 193) := by decide
@[simp] theorem rawRowCrossEq_194 :
    (rawRowMass 194).CrossEq (rawAlpha 194) := by decide
@[simp] theorem rawRowCrossEq_195 :
    (rawRowMass 195).CrossEq (rawAlpha 195) := by decide
@[simp] theorem rawRowCrossEq_196 :
    (rawRowMass 196).CrossEq (rawAlpha 196) := by decide
@[simp] theorem rawRowCrossEq_197 :
    (rawRowMass 197).CrossEq (rawAlpha 197) := by decide
@[simp] theorem rawRowCrossEq_198 :
    (rawRowMass 198).CrossEq (rawAlpha 198) := by decide
@[simp] theorem rawRowCrossEq_199 :
    (rawRowMass 199).CrossEq (rawAlpha 199) := by decide
@[simp] theorem rawRowCrossEq_200 :
    (rawRowMass 200).CrossEq (rawAlpha 200) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificate -/
section


/-!
# Kernel-checked finite allocation certificate

This file internalizes the exact rational checker accompanying Section 4 of
the paper.  The finite computations use ordinary kernel reduction through
`decide`; in particular, no native-code decision procedure is used.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

open AllocationEntry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The 211 records as a finite set.  Record-level duplicates are absent. -/
def finiteAllocationEntrySet : Finset AllocationEntry :=
  finiteAllocationEntries.toFinset

/-- The set of the 211 nonzero coordinates. -/
def finiteAllocationSupport : Finset (ℕ × ℕ) :=
  (finiteAllocationEntries.map coordinate).toFinset

/-- The sparse finite array `x^{fin}_{r,q}`.  Every coordinate not listed in
`finiteAllocationSupport` is zero by construction. -/
def finiteAllocation (r q : ℕ) : ℚ :=
  ∑ e ∈ finiteAllocationEntrySet,
    if e.row = r ∧ e.cofactor = q then e.value else 0

/-- A computationally sparse form of a row sum. -/
def finiteRowEntryMass (r : ℕ) : ℚ :=
  ∑ e ∈ finiteAllocationEntrySet,
    if e.row = r then e.value else 0

/-- The paper's finite valuation load, summed over the explicit nonzero
coordinates. -/
def finitePrimeLoad (ℓ : ℕ) : ℚ :=
  ∑ e ∈ finiteAllocationEntrySet,
    (e.cofactor.factorization ℓ : ℚ) * e.value

/-- Since every listed cofactor happens to be prime, this indicator sum is an
efficient exact checker for `finitePrimeLoad`. -/
def finitePrimeIndicatorLoad (ℓ : ℕ) : ℚ :=
  ∑ e ∈ finiteAllocationEntrySet,
    if e.cofactor = ℓ then e.value else 0

/-- A fully computable list form of `finiteRowEntryMass`, used only by the
kernel decision procedure. -/
def finiteRowListMass (r : ℕ) : ℚ :=
  (finiteAllocationRowEntries r |>.map fun e => e.value).sum

/-- A fully computable list form of `finitePrimeIndicatorLoad`. -/
def finitePrimeIndicatorListLoad (ℓ : ℕ) : ℚ :=
  (finiteAllocationPrimeEntries ℓ |>.map fun e => e.value).sum

/-! ## Exact structural checks -/

 abbrev keyLabeled (key : AllocationEntry → ℕ)
    (buckets : List (ℕ × List AllocationEntry)) : Prop :=
  allocationKeyLabeled key buckets

 abbrev innerOutputNodup {β : Type*} (output : AllocationEntry → β)
    (buckets : List (ℕ × List AllocationEntry)) : Prop :=
  allocationInnerOutputNodup output buckets

 theorem keyLabeled_append {key : AllocationEntry → ℕ}
    {left right : List (ℕ × List AllocationEntry)}
    (hleft : keyLabeled key left) (hright : keyLabeled key right) :
    keyLabeled key (left ++ right) := by
  exact List.forall_append.mpr ⟨hleft, hright⟩

 theorem innerOutputNodup_append {β : Type*}
    {output : AllocationEntry → β}
    {left right : List (ℕ × List AllocationEntry)}
    (hleft : innerOutputNodup output left)
    (hright : innerOutputNodup output right) :
    innerOutputNodup output (left ++ right) := by
  exact List.forall_append.mpr ⟨hleft, hright⟩

 theorem flattenBucketsMap_nodup {β : Type*}
    (output : AllocationEntry → β) (key : β → ℕ)
    (buckets : List (ℕ × List AllocationEntry))
    (hkeys : (buckets.map fun bucket => bucket.1).Nodup)
    (hlabeled : keyLabeled (fun e => key (output e)) buckets)
    (hinner : innerOutputNodup output buckets) :
    ((buckets.flatMap fun bucket => bucket.2).map output).Nodup := by
  induction buckets with
  | nil => simp
  | cons bucket buckets ih =>
      rcases bucket with ⟨q, entries⟩
      simp only [List.map_cons, List.nodup_cons] at hkeys
      simp only [keyLabeled, allocationKeyLabeled,
        List.forall_cons] at hlabeled
      simp only [innerOutputNodup, allocationInnerOutputNodup,
        List.forall_cons] at hinner
      simp only [List.flatMap_cons, List.map_append]
      apply List.Nodup.append hinner.1
        (ih hkeys.2 hlabeled.2 hinner.2)
      rw [List.disjoint_left]
      intro x hxEntries hxBuckets
      simp only [List.mem_map] at hxEntries hxBuckets
      obtain ⟨e, heEntries, rfl⟩ := hxEntries
      obtain ⟨e', he'Buckets, hout⟩ := hxBuckets
      simp only [List.mem_flatMap] at he'Buckets
      obtain ⟨bucket, hbucket, he'Bucket⟩ := he'Buckets
      rcases bucket with ⟨q', entries'⟩
      have heLabel :=
        (List.forall_iff_forall_mem.mp hlabeled.1) e heEntries
      have hbucketLabels :=
        (List.forall_iff_forall_mem.mp hlabeled.2)
          (q', entries') hbucket
      have he'Label :=
        (List.forall_iff_forall_mem.mp hbucketLabels) e' he'Bucket
      apply hkeys.1
      simp only [List.mem_map]
      refine ⟨(q', entries'), hbucket, ?_⟩
      calc
        q' = key (output e') := he'Label.symm
        _ = key (output e) := congrArg key hout
        _ = q := heLabel



 theorem indicator_sum_buckets (key : AllocationEntry → ℕ)
    (p : ℕ) (buckets : List (ℕ × List AllocationEntry))
    (hlabeled : keyLabeled key buckets) :
    ((buckets.flatMap fun bucket => bucket.2).map fun e =>
        if key e = p then e.value else 0).sum =
      ((selectPrimeEntries p buckets).map fun e => e.value).sum := by
  induction buckets with
  | nil => simp [selectPrimeEntries]
  | cons bucket buckets ih =>
      rcases bucket with ⟨q, entries⟩
      simp only [keyLabeled, allocationKeyLabeled,
        List.forall_cons] at hlabeled
      have hentries := List.forall_iff_forall_mem.mp hlabeled.1
      have htail := ih hlabeled.2
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      rw [htail]
      by_cases hqp : q = p
      · subst q
        rw [selectPrimeEntries, if_pos rfl]
        change
          (entries.map fun e => if key e = p then e.value else 0).sum +
              ((selectPrimeEntries p buckets).map fun e => e.value).sum =
            ((entries ++ selectPrimeEntries p buckets).map fun e => e.value).sum
        rw [List.map_append, List.sum_append]
        congr 1
        apply congrArg List.sum
        apply List.map_congr_left
        intro e he
        simp [hentries e he]
      · simp only [selectPrimeEntries, if_neg hqp]
        have hzero :
            (entries.map fun e => if key e = p then e.value else 0).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨e, he, rfl⟩ := hx
          simp [hentries e he, hqp]
        rw [hzero, zero_add]

 theorem selectPrimeEntries_map (p : ℕ) (keys : List ℕ)
    (f : ℕ → List AllocationEntry) (hkeys : keys.Nodup) :
    selectPrimeEntries p (keys.map fun q => (q, f q)) =
      if p ∈ keys then f p else [] := by
  induction keys with
  | nil => simp [selectPrimeEntries]
  | cons q keys ih =>
      rw [List.nodup_cons] at hkeys
      simp only [List.map_cons]
      by_cases hqp : q = p
      · subst q
        rw [selectPrimeEntries, if_pos rfl, ih hkeys.2]
        simp [hkeys.1]
      · rw [selectPrimeEntries, if_neg hqp, ih hkeys.2]
        have hpq : p ≠ q := Ne.symm hqp
        simp [hpq]

 theorem selectPrimeEntries_append (p : ℕ)
    (left right : List (ℕ × List AllocationEntry)) :
    selectPrimeEntries p (left ++ right) =
      selectPrimeEntries p left ++ selectPrimeEntries p right := by
  induction left with
  | nil => rfl
  | cons bucket left ih =>
      rcases bucket with ⟨q, entries⟩
      simp only [List.cons_append, selectPrimeEntries]
      split <;> simp [ih]

 theorem rowBlockFlat {b : ℕ} (hb : b ≤ 9) :
    finiteAllocationRowBlockEntries b =
      (finiteAllocationRowBlockBuckets b).flatMap fun bucket => bucket.2 := by
  exact allocationRowBlockFlat hb



 theorem rowLabels {b : ℕ} (hb : b ≤ 9) :
    keyLabeled (fun e => e.row) (finiteAllocationRowBlockBuckets b) := by
  exact allocationRowLabels hb



 theorem rowRanges_eq :
    List.range' 1 200 =
      List.range' 1 20 ++ List.range' 21 20 ++
      List.range' 41 20 ++ List.range' 61 20 ++
      List.range' 81 20 ++ List.range' 101 20 ++
      List.range' 121 20 ++ List.range' 141 20 ++
      List.range' 161 20 ++ List.range' 181 20 := by
  rw [show List.range' 1 200 =
      List.range' 1 20 ++ List.range' 21 180 by
    simpa using (List.range'_append_1 (s := 1) (m := 20) (n := 180)).symm]
  rw [show List.range' 21 180 =
      List.range' 21 20 ++ List.range' 41 160 by
    simpa using (List.range'_append_1 (s := 21) (m := 20) (n := 160)).symm]
  rw [show List.range' 41 160 =
      List.range' 41 20 ++ List.range' 61 140 by
    simpa using (List.range'_append_1 (s := 41) (m := 20) (n := 140)).symm]
  rw [show List.range' 61 140 =
      List.range' 61 20 ++ List.range' 81 120 by
    simpa using (List.range'_append_1 (s := 61) (m := 20) (n := 120)).symm]
  rw [show List.range' 81 120 =
      List.range' 81 20 ++ List.range' 101 100 by
    simpa using (List.range'_append_1 (s := 81) (m := 20) (n := 100)).symm]
  rw [show List.range' 101 100 =
      List.range' 101 20 ++ List.range' 121 80 by
    simpa using (List.range'_append_1 (s := 101) (m := 20) (n := 80)).symm]
  rw [show List.range' 121 80 =
      List.range' 121 20 ++ List.range' 141 60 by
    simpa using (List.range'_append_1 (s := 121) (m := 20) (n := 60)).symm]
  rw [show List.range' 141 60 =
      List.range' 141 20 ++ List.range' 161 40 by
    simpa using (List.range'_append_1 (s := 141) (m := 20) (n := 40)).symm]
  rw [show List.range' 161 40 =
      List.range' 161 20 ++ List.range' 181 20 by
    simpa using (List.range'_append_1 (s := 161) (m := 20) (n := 20)).symm]
  simp only [List.append_assoc]

 def finiteAllocationRowBuckets :
    List (ℕ × List AllocationEntry) :=
  (List.range' 1 200).map fun r => (r, finiteAllocationRowEntries r)

 theorem finiteAllocationRowBuckets_eq_blocks :
    finiteAllocationRowBuckets =
      finiteAllocationRowBlockBuckets 0 ++
      finiteAllocationRowBlockBuckets 1 ++
      finiteAllocationRowBlockBuckets 2 ++
      finiteAllocationRowBlockBuckets 3 ++
      finiteAllocationRowBlockBuckets 4 ++
      finiteAllocationRowBlockBuckets 5 ++
      finiteAllocationRowBlockBuckets 6 ++
      finiteAllocationRowBlockBuckets 7 ++
      finiteAllocationRowBlockBuckets 8 ++
      finiteAllocationRowBlockBuckets 9 := by
  unfold finiteAllocationRowBuckets finiteAllocationRowBlockBuckets
  rw [rowRanges_eq]
  simp only [List.map_append]

 theorem rowCoordinateInnerNodup {b : ℕ} (hb : b ≤ 9) :
    innerOutputNodup coordinate (finiteAllocationRowBlockBuckets b) := by
  exact allocationRowCoordinateInnerNodup hb

 theorem finiteAllocationRowBuckets_labeled :
    keyLabeled (fun e => e.row) finiteAllocationRowBuckets := by
  rw [finiteAllocationRowBuckets_eq_blocks]
  exact keyLabeled_append
    (keyLabeled_append
      (keyLabeled_append
        (keyLabeled_append
          (keyLabeled_append
            (keyLabeled_append
              (keyLabeled_append
                (keyLabeled_append
                  (keyLabeled_append
                    (rowLabels (b := 0) (by omega))
                    (rowLabels (b := 1) (by omega)))
                  (rowLabels (b := 2) (by omega)))
                (rowLabels (b := 3) (by omega)))
              (rowLabels (b := 4) (by omega)))
            (rowLabels (b := 5) (by omega)))
          (rowLabels (b := 6) (by omega)))
        (rowLabels (b := 7) (by omega)))
      (rowLabels (b := 8) (by omega)))
    (rowLabels (b := 9) (by omega))

 theorem finiteAllocationRowBuckets_coordinate_inner_nodup :
    innerOutputNodup coordinate finiteAllocationRowBuckets := by
  rw [finiteAllocationRowBuckets_eq_blocks]
  exact innerOutputNodup_append
    (innerOutputNodup_append
      (innerOutputNodup_append
        (innerOutputNodup_append
          (innerOutputNodup_append
            (innerOutputNodup_append
              (innerOutputNodup_append
                (innerOutputNodup_append
                  (innerOutputNodup_append
                    (rowCoordinateInnerNodup (b := 0) (by omega))
                    (rowCoordinateInnerNodup (b := 1) (by omega)))
                  (rowCoordinateInnerNodup (b := 2) (by omega)))
                (rowCoordinateInnerNodup (b := 3) (by omega)))
              (rowCoordinateInnerNodup (b := 4) (by omega)))
            (rowCoordinateInnerNodup (b := 5) (by omega)))
          (rowCoordinateInnerNodup (b := 6) (by omega)))
        (rowCoordinateInnerNodup (b := 7) (by omega)))
      (rowCoordinateInnerNodup (b := 8) (by omega)))
    (rowCoordinateInnerNodup (b := 9) (by omega))

 theorem finiteAllocationEntries_eq_rowBuckets :
    finiteAllocationEntries =
      (finiteAllocationRowBuckets.flatMap fun bucket => bucket.2) := by
  rw [finiteAllocationEntries, finiteAllocationRowBuckets_eq_blocks]
  simp only [List.flatMap_append]
  rw [← rowBlockFlat (b := 0) (by omega),
    ← rowBlockFlat (b := 1) (by omega),
    ← rowBlockFlat (b := 2) (by omega),
    ← rowBlockFlat (b := 3) (by omega),
    ← rowBlockFlat (b := 4) (by omega),
    ← rowBlockFlat (b := 5) (by omega),
    ← rowBlockFlat (b := 6) (by omega),
    ← rowBlockFlat (b := 7) (by omega),
    ← rowBlockFlat (b := 8) (by omega),
    ← rowBlockFlat (b := 9) (by omega)]

theorem finiteAllocationCoordinates_nodup :
    (finiteAllocationEntries.map coordinate).Nodup := by
  rw [finiteAllocationEntries_eq_rowBuckets]
  apply flattenBucketsMap_nodup coordinate Prod.fst
  · simpa [finiteAllocationRowBuckets] using
      (List.nodup_range' : (List.range' 1 200).Nodup)
  · exact finiteAllocationRowBuckets_labeled
  · exact finiteAllocationRowBuckets_coordinate_inner_nodup

theorem finiteAllocationEntries_nodup :
    finiteAllocationEntries.Nodup :=
  finiteAllocationCoordinates_nodup.of_map coordinate

 theorem selectedRows_eq {r : ℕ} (hr1 : 1 ≤ r) (hr200 : r ≤ 200) :
    finiteAllocationSelectedRowEntries r = finiteAllocationRowEntries r := by
  rw [finiteAllocationSelectedRowEntries,
    selectPrimeEntries_map r (List.range' 1 200)
      finiteAllocationRowEntries List.nodup_range']
  simp only [List.mem_range'_1]
  rw [if_pos (by omega)]

 def rowBlockSelectedEntries (r : ℕ) : List AllocationEntry :=
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 0) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 1) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 2) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 3) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 4) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 5) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 6) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 7) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 8) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 9)

 theorem rowBlockSelectedEntries_eq (r : ℕ) :
    rowBlockSelectedEntries r = finiteAllocationSelectedRowEntries r := by
  unfold rowBlockSelectedEntries finiteAllocationSelectedRowEntries
  rw [rowRanges_eq]
  simp only [List.map_append, selectPrimeEntries_append]
  rfl

 theorem rowBlockIndicatorSum {b r : ℕ} (hb : b ≤ 9) :
    ((finiteAllocationRowBlockEntries b).map fun e =>
        if e.row = r then e.value else 0).sum =
      ((selectPrimeEntries r (finiteAllocationRowBlockBuckets b)).map
        fun e => e.value).sum := by
  rw [rowBlockFlat hb]
  exact indicator_sum_buckets (fun e => e.row) r _ (rowLabels hb)



 theorem finiteRowIndicatorListMass_eq {r : ℕ}
    (hr1 : 1 ≤ r) (hr200 : r ≤ 200) :
    (finiteAllocationEntries.map fun e =>
        if e.row = r then e.value else 0).sum = finiteRowListMass r := by
  calc
    _ = ((rowBlockSelectedEntries r).map fun e => e.value).sum := by
      rw [finiteAllocationEntries]
      simp only [List.map_append, List.sum_append]
      rw [rowBlockIndicatorSum (b := 0) (by omega),
        rowBlockIndicatorSum (b := 1) (by omega),
        rowBlockIndicatorSum (b := 2) (by omega),
        rowBlockIndicatorSum (b := 3) (by omega),
        rowBlockIndicatorSum (b := 4) (by omega),
        rowBlockIndicatorSum (b := 5) (by omega),
        rowBlockIndicatorSum (b := 6) (by omega),
        rowBlockIndicatorSum (b := 7) (by omega),
        rowBlockIndicatorSum (b := 8) (by omega),
        rowBlockIndicatorSum (b := 9) (by omega)]
      simp only [rowBlockSelectedEntries, List.map_append, List.sum_append]
    _ = _ := by
      rw [rowBlockSelectedEntries_eq, selectedRows_eq hr1 hr200]
      rfl



theorem finiteRowEntryMass_eq_list {r : ℕ}
    (hr1 : 1 ≤ r) (hr200 : r ≤ 200) :
    finiteRowEntryMass r = finiteRowListMass r := by
  calc
    finiteRowEntryMass r =
        (finiteAllocationEntries.map fun e =>
          if e.row = r then e.value else 0).sum := by
      simpa [finiteRowEntryMass, finiteAllocationEntrySet] using
        (List.sum_toFinset
          (fun e : AllocationEntry => if e.row = r then e.value else 0)
          finiteAllocationEntries_nodup)
    _ = finiteRowListMass r := finiteRowIndicatorListMass_eq hr1 hr200



theorem RawFraction.add_denominator_pos {a b : RawFraction}
    (ha : 0 < a.denominator) (hb : 0 < b.denominator) :
    0 < (a.add b).denominator := by
  exact Nat.mul_pos ha hb

theorem RawFraction.sum_denominator_pos {α : Type*} (l : List α)
    (f : α → RawFraction) (hf : ∀ x ∈ l, 0 < (f x).denominator) :
    0 < (RawFraction.sum l f).denominator := by
  induction l with
  | nil => simp [RawFraction.sum, RawFraction.zero]
  | cons x xs ih =>
      apply RawFraction.add_denominator_pos
      · exact hf x (by simp)
      · exact ih (fun y hy => hf y (by simp [hy]))

theorem RawFraction.toRat_add {a b : RawFraction}
    (ha : 0 < a.denominator) (hb : 0 < b.denominator) :
    (a.add b).toRat = a.toRat + b.toRat := by
  have ha0 : (a.denominator : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hb0 : (b.denominator : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  simp only [RawFraction.add, RawFraction.toRat, Nat.cast_add, Nat.cast_mul]
  field_simp [ha0, hb0]

theorem RawFraction.sum_toRat {α : Type*} (l : List α)
    (f : α → RawFraction) (hf : ∀ x ∈ l, 0 < (f x).denominator) :
    (RawFraction.sum l f).toRat =
      (l.map fun x => (f x).toRat).sum := by
  induction l with
  | nil => norm_num [RawFraction.sum, RawFraction.zero, RawFraction.toRat]
  | cons x xs ih =>
      have hx : 0 < (f x).denominator := hf x (by simp)
      have hxs : ∀ y ∈ xs, 0 < (f y).denominator :=
        fun y hy => hf y (by simp [hy])
      rw [RawFraction.sum, List.map_cons, List.sum_cons,
        RawFraction.toRat_add hx (RawFraction.sum_denominator_pos xs f hxs),
        ih hxs]

theorem RawFraction.toRat_eq_of_crossEq {a b : RawFraction}
    (ha : 0 < a.denominator) (hb : 0 < b.denominator)
    (hcross : a.CrossEq b) : a.toRat = b.toRat := by
  apply (div_eq_div_iff (by exact_mod_cast (ne_of_gt ha))
    (by exact_mod_cast (ne_of_gt hb))).2
  exact_mod_cast hcross



theorem rawRowMass_denominator_pos (r : ℕ) :
    0 < (rawRowMass r).denominator := by
  apply RawFraction.sum_denominator_pos
  intro e _
  simp [RawFraction.ofEntry]



theorem rawAlpha_denominator_pos (r : ℕ) :
    0 < (rawAlpha r).denominator := by
  simp [rawAlpha]





theorem rawRowMass_toRat (r : ℕ) :
    (rawRowMass r).toRat = finiteRowListMass r := by
  rw [rawRowMass, RawFraction.sum_toRat]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    rfl
  · intro e _
    simp [RawFraction.ofEntry]



theorem rawAlpha_toRat (r : ℕ) :
    (rawAlpha r).toRat = alpha r := by
  norm_num [rawAlpha, RawFraction.toRat, alpha]





theorem finiteAllocationEntrySet_mem_iff {e : AllocationEntry} :
    e ∈ finiteAllocationEntrySet ↔ e ∈ finiteAllocationEntries := by
  simp [finiteAllocationEntrySet]

theorem finiteAllocationEntrySet_valid {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntrySet) : e.Valid :=
  finiteAllocationEntries_valid (finiteAllocationEntrySet_mem_iff.mp he)



theorem finiteAllocationEntry_value_pos {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntrySet) : 0 < e.value := by
  have hvalid := finiteAllocationEntrySet_valid he
  exact div_pos (by exact_mod_cast hvalid.2.2.2.2.1)
    (by positivity)



theorem finiteAllocation_support_valid {r q : ℕ}
    (hrq : (r, q) ∈ finiteAllocationSupport) :
    1 ≤ r ∧ r ≤ 200 ∧ r + 1 ≤ q ∧ q ≤ 2 * r + 1 := by
  simp only [finiteAllocationSupport, List.mem_toFinset, List.mem_map] at hrq
  obtain ⟨e, he, hcoordinate⟩ := hrq
  have hvalid := finiteAllocationEntries_valid he
  have hr : e.row = r := congrArg Prod.fst hcoordinate
  have hq : e.cofactor = q := congrArg Prod.snd hcoordinate
  subst r
  subst q
  exact ⟨hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1⟩

theorem finiteAllocation_eq_zero_of_not_mem {r q : ℕ}
    (hrq : (r, q) ∉ finiteAllocationSupport) :
    finiteAllocation r q = 0 := by
  classical
  rw [finiteAllocation]
  apply Finset.sum_eq_zero
  intro e he
  simp only [ite_eq_right_iff]
  intro hmatch
  exfalso
  apply hrq
  have heList : e ∈ finiteAllocationEntries :=
    finiteAllocationEntrySet_mem_iff.mp he
  simp only [finiteAllocationSupport, List.mem_toFinset, List.mem_map]
  refine ⟨e, heList, ?_⟩
  exact Prod.ext hmatch.1 hmatch.2

 theorem finiteAllocationEntrySet_coordinate_injective
    {e₁ e₂ : AllocationEntry}
    (he₁ : e₁ ∈ finiteAllocationEntrySet)
    (he₂ : e₂ ∈ finiteAllocationEntrySet)
    (hcoord : e₁.coordinate = e₂.coordinate) : e₁ = e₂ := by
  exact List.inj_on_of_nodup_map finiteAllocationCoordinates_nodup
    (finiteAllocationEntrySet_mem_iff.mp he₁)
    (finiteAllocationEntrySet_mem_iff.mp he₂) hcoord

theorem finiteAllocation_eq_entry_value {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntrySet) :
    finiteAllocation e.row e.cofactor = e.value := by
  classical
  rw [finiteAllocation]
  calc
    (∑ e' ∈ finiteAllocationEntrySet,
        if e'.row = e.row ∧ e'.cofactor = e.cofactor then e'.value else 0) =
        (if e.row = e.row ∧ e.cofactor = e.cofactor then e.value else 0) := by
      apply Finset.sum_eq_single e
      · intro e' he' hne
        rw [if_neg]
        intro hmatch
        apply hne
        apply finiteAllocationEntrySet_coordinate_injective he' he
        exact Prod.ext hmatch.1 hmatch.2
      · exact fun hnot => (hnot he).elim
    _ = e.value := by simp

theorem finiteAllocation_pos_of_mem {r q : ℕ}
    (hrq : (r, q) ∈ finiteAllocationSupport) :
    0 < finiteAllocation r q := by
  simp only [finiteAllocationSupport, List.mem_toFinset, List.mem_map] at hrq
  obtain ⟨e, heList, hcoordinate⟩ := hrq
  have he : e ∈ finiteAllocationEntrySet :=
    finiteAllocationEntrySet_mem_iff.mpr heList
  have hr : e.row = r := congrArg Prod.fst hcoordinate
  have hq : e.cofactor = q := congrArg Prod.snd hcoordinate
  rw [← hr, ← hq, finiteAllocation_eq_entry_value he]
  exact finiteAllocationEntry_value_pos he

/-! ## Sparse sums equal the literal coordinate sums -/

 theorem finiteAllocation_weighted_row_sum
    (w : ℕ → ℚ) (r : ℕ) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        w q * finiteAllocation r q) =
      ∑ e ∈ finiteAllocationEntrySet,
        if e.row = r then w e.cofactor * e.value else 0 := by
  classical
  simp_rw [finiteAllocation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases her : e.row = r
  · have hvalid := finiteAllocationEntrySet_valid he
    have hqmem : e.cofactor ∈ Finset.Icc (r + 1) (2 * r + 1) := by
      simp only [Finset.mem_Icc]
      constructor
      · simpa [her] using hvalid.2.2.1
      · simpa [her] using hvalid.2.2.2.1
    rw [Finset.sum_eq_single e.cofactor]
    · simp [her]
    · intro q hq hne
      have hneq : ¬(e.row = r ∧ e.cofactor = q) := by
        intro h
        exact hne h.2.symm
      simp [hneq]
    · exact fun hnot => (hnot hqmem).elim
  · simp [her]

theorem finiteAllocation_row_sum (r : ℕ) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1), finiteAllocation r q) =
      finiteRowEntryMass r := by
  simpa [finiteRowEntryMass] using
    finiteAllocation_weighted_row_sum (fun _ => 1) r







/-! ## Kernel-checked rational identities and inequalities -/


 theorem rawRowCrossEq {r : ℕ} (hr1 : 1 ≤ r) (hr200 : r ≤ 200) :
    (rawRowMass r).CrossEq (rawAlpha r) := by
  by_cases h20 : r ≤ 20
  · interval_cases r <;> simp only [rawRowCrossEq_1, rawRowCrossEq_2, rawRowCrossEq_3, rawRowCrossEq_4, rawRowCrossEq_5, rawRowCrossEq_6, rawRowCrossEq_7, rawRowCrossEq_8, rawRowCrossEq_9, rawRowCrossEq_10, rawRowCrossEq_11, rawRowCrossEq_12, rawRowCrossEq_13, rawRowCrossEq_14, rawRowCrossEq_15, rawRowCrossEq_16, rawRowCrossEq_17, rawRowCrossEq_18, rawRowCrossEq_19, rawRowCrossEq_20]
  by_cases h40 : r ≤ 40
  · interval_cases r <;> simp only [rawRowCrossEq_21, rawRowCrossEq_22, rawRowCrossEq_23, rawRowCrossEq_24, rawRowCrossEq_25, rawRowCrossEq_26, rawRowCrossEq_27, rawRowCrossEq_28, rawRowCrossEq_29, rawRowCrossEq_30, rawRowCrossEq_31, rawRowCrossEq_32, rawRowCrossEq_33, rawRowCrossEq_34, rawRowCrossEq_35, rawRowCrossEq_36, rawRowCrossEq_37, rawRowCrossEq_38, rawRowCrossEq_39, rawRowCrossEq_40]
  by_cases h60 : r ≤ 60
  · interval_cases r <;> simp only [rawRowCrossEq_41, rawRowCrossEq_42, rawRowCrossEq_43, rawRowCrossEq_44, rawRowCrossEq_45, rawRowCrossEq_46, rawRowCrossEq_47, rawRowCrossEq_48, rawRowCrossEq_49, rawRowCrossEq_50, rawRowCrossEq_51, rawRowCrossEq_52, rawRowCrossEq_53, rawRowCrossEq_54, rawRowCrossEq_55, rawRowCrossEq_56, rawRowCrossEq_57, rawRowCrossEq_58, rawRowCrossEq_59, rawRowCrossEq_60]
  by_cases h80 : r ≤ 80
  · interval_cases r <;> simp only [rawRowCrossEq_61, rawRowCrossEq_62, rawRowCrossEq_63, rawRowCrossEq_64, rawRowCrossEq_65, rawRowCrossEq_66, rawRowCrossEq_67, rawRowCrossEq_68, rawRowCrossEq_69, rawRowCrossEq_70, rawRowCrossEq_71, rawRowCrossEq_72, rawRowCrossEq_73, rawRowCrossEq_74, rawRowCrossEq_75, rawRowCrossEq_76, rawRowCrossEq_77, rawRowCrossEq_78, rawRowCrossEq_79, rawRowCrossEq_80]
  by_cases h100 : r ≤ 100
  · interval_cases r <;> simp only [rawRowCrossEq_81, rawRowCrossEq_82, rawRowCrossEq_83, rawRowCrossEq_84, rawRowCrossEq_85, rawRowCrossEq_86, rawRowCrossEq_87, rawRowCrossEq_88, rawRowCrossEq_89, rawRowCrossEq_90, rawRowCrossEq_91, rawRowCrossEq_92, rawRowCrossEq_93, rawRowCrossEq_94, rawRowCrossEq_95, rawRowCrossEq_96, rawRowCrossEq_97, rawRowCrossEq_98, rawRowCrossEq_99, rawRowCrossEq_100]
  by_cases h120 : r ≤ 120
  · interval_cases r <;> simp only [rawRowCrossEq_101, rawRowCrossEq_102, rawRowCrossEq_103, rawRowCrossEq_104, rawRowCrossEq_105, rawRowCrossEq_106, rawRowCrossEq_107, rawRowCrossEq_108, rawRowCrossEq_109, rawRowCrossEq_110, rawRowCrossEq_111, rawRowCrossEq_112, rawRowCrossEq_113, rawRowCrossEq_114, rawRowCrossEq_115, rawRowCrossEq_116, rawRowCrossEq_117, rawRowCrossEq_118, rawRowCrossEq_119, rawRowCrossEq_120]
  by_cases h140 : r ≤ 140
  · interval_cases r <;> simp only [rawRowCrossEq_121, rawRowCrossEq_122, rawRowCrossEq_123, rawRowCrossEq_124, rawRowCrossEq_125, rawRowCrossEq_126, rawRowCrossEq_127, rawRowCrossEq_128, rawRowCrossEq_129, rawRowCrossEq_130, rawRowCrossEq_131, rawRowCrossEq_132, rawRowCrossEq_133, rawRowCrossEq_134, rawRowCrossEq_135, rawRowCrossEq_136, rawRowCrossEq_137, rawRowCrossEq_138, rawRowCrossEq_139, rawRowCrossEq_140]
  by_cases h160 : r ≤ 160
  · interval_cases r <;> simp only [rawRowCrossEq_141, rawRowCrossEq_142, rawRowCrossEq_143, rawRowCrossEq_144, rawRowCrossEq_145, rawRowCrossEq_146, rawRowCrossEq_147, rawRowCrossEq_148, rawRowCrossEq_149, rawRowCrossEq_150, rawRowCrossEq_151, rawRowCrossEq_152, rawRowCrossEq_153, rawRowCrossEq_154, rawRowCrossEq_155, rawRowCrossEq_156, rawRowCrossEq_157, rawRowCrossEq_158, rawRowCrossEq_159, rawRowCrossEq_160]
  by_cases h180 : r ≤ 180
  · interval_cases r <;> simp only [rawRowCrossEq_161, rawRowCrossEq_162, rawRowCrossEq_163, rawRowCrossEq_164, rawRowCrossEq_165, rawRowCrossEq_166, rawRowCrossEq_167, rawRowCrossEq_168, rawRowCrossEq_169, rawRowCrossEq_170, rawRowCrossEq_171, rawRowCrossEq_172, rawRowCrossEq_173, rawRowCrossEq_174, rawRowCrossEq_175, rawRowCrossEq_176, rawRowCrossEq_177, rawRowCrossEq_178, rawRowCrossEq_179, rawRowCrossEq_180]
  · interval_cases r <;> simp only [rawRowCrossEq_181, rawRowCrossEq_182, rawRowCrossEq_183, rawRowCrossEq_184, rawRowCrossEq_185, rawRowCrossEq_186, rawRowCrossEq_187, rawRowCrossEq_188, rawRowCrossEq_189, rawRowCrossEq_190, rawRowCrossEq_191, rawRowCrossEq_192, rawRowCrossEq_193, rawRowCrossEq_194, rawRowCrossEq_195, rawRowCrossEq_196, rawRowCrossEq_197, rawRowCrossEq_198, rawRowCrossEq_199, rawRowCrossEq_200]

 theorem finiteRowListMass_identity {r : ℕ} (hr1 : 1 ≤ r)
    (hr200 : r ≤ 200) : finiteRowListMass r = alpha r := by
  have hcross := rawRowCrossEq hr1 hr200
  calc
    finiteRowListMass r = (rawRowMass r).toRat := (rawRowMass_toRat r).symm
    _ = (rawAlpha r).toRat :=
      RawFraction.toRat_eq_of_crossEq (rawRowMass_denominator_pos r)
        (rawAlpha_denominator_pos r) hcross
    _ = alpha r := rawAlpha_toRat r

theorem finiteAllocation_row_identity {r : ℕ} (hr1 : 1 ≤ r)
    (hr200 : r ≤ 200) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1), finiteAllocation r q) =
      alpha r := by
  rw [finiteAllocation_row_sum r]
  rw [finiteRowEntryMass_eq_list hr1 hr200]
  exact finiteRowListMass_identity hr1 hr200

















/-! ## Literal paper-level certificate -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.Nagura -/
section


/-!
# A finite Nagura certificate and an asymptotic Nagura tail

Nagura's theorem says that every integer `n ≥ 25` has a prime `p` with
`n < p < 6n/5`.  The available assumption-free Mathlib theorem on explicit
prime intervals is Bertrand's postulate.  For the infinite tail we use the
assumption-free prime number theorem exported by `SafePrimeCounting`; the
stronger explicit results in the optional `PrimeNumberTheoremAnd` dependency
are not proof-complete and are deliberately not imported here.

This file proves the Nagura conclusion unconditionally on the complete
finite range `25 ≤ n < 91639`.  The certificate is a chain of actual primes;
successive entries `a,b` satisfy `5b < 6a`, so their covered integer
intervals overlap.  It also proves that the Nagura conclusion holds for all
sufficiently large integers and records the exact reduction of the full
theorem to a concrete tail, together with the transfer from a Nagura witness
to the ratio for consecutive primes.
-/

open Filter Topology

namespace Erdos390.WholePaper

/-- The exact natural-number form of the prime interval used in Section 4. -/
def HasNaguraPrime (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n





















end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.LeastPrimeTail -/
section


/-! # Least-prime routing for the infinite allocation tail -/

namespace Erdos390.WholePaper

noncomputable section

 theorem exists_prime_strictly_above (n : ℕ) :
    ∃ p : ℕ, p.Prime ∧ n < p := by
  obtain ⟨p, hpLower, hpPrime⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, hpPrime, by omega⟩

/-- The least prime strictly larger than `n`. -/
def leastPrimeAbove (n : ℕ) : ℕ :=
  Nat.find (exists_prime_strictly_above n)



theorem lt_leastPrimeAbove (n : ℕ) : n < leastPrimeAbove n :=
  (Nat.find_spec (exists_prime_strictly_above n)).2

theorem leastPrimeAbove_le {n p : ℕ} (hp : p.Prime) (hnp : n < p) :
    leastPrimeAbove n ≤ p := by
  exact Nat.find_min' (exists_prime_strictly_above n) ⟨hp, hnp⟩

/-- Bertrand places the least prime in the allocation range. -/
theorem leastPrimeAbove_le_two_mul {n : ℕ} (hn : 0 < n) :
    leastPrimeAbove n ≤ 2 * n := by
  obtain ⟨p, hpPrime, hnp, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n hn.ne'
  exact (leastPrimeAbove_le hpPrime hnp).trans hpUpper

theorem leastPrimeAbove_mem_allocationRange {r : ℕ} (hr : 1 ≤ r) :
    leastPrimeAbove r ∈ Finset.Icc (r + 1) (2 * r + 1) := by
  exact Finset.mem_Icc.mpr
    ⟨Nat.succ_le_iff.mpr (lt_leastPrimeAbove r),
      (leastPrimeAbove_le_two_mul (by omega)).trans (by omega)⟩



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.InfiniteAllocationTailCore -/
section


/-!
# Finite-support algebra for the least-prime allocation tail

This module contains the part of Lemma 4.2 that is independent of the
large finite certificate.  Keeping that certificate out of this import
chain materially reduces elaboration memory for the reusable tail lemmas.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The least-prime tail used from row `201` onward. -/
def tailAllocation (r q : ℕ) : ℚ :=
  if 201 ≤ r ∧ q = leastPrimeAbove r then alpha r else 0

/-- One row's contribution to the valuation load at `ℓ`. -/
def allocationPrimeRowLoad (x : ℕ → ℕ → ℚ) (ℓ r : ℕ) : ℚ :=
  ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
    (q.factorization ℓ : ℚ) * x r q

/-- The full valuation load of an infinite allocation. -/
def allocationPrimeLoad (x : ℕ → ℕ → ℚ) (ℓ : ℕ) : ℚ :=
  ∑' r : ℕ, allocationPrimeRowLoad x ℓ r

def tailPrimeRowLoad (ℓ r : ℕ) : ℚ :=
  allocationPrimeRowLoad tailAllocation ℓ r

theorem alpha_pos (r : ℕ) : 0 < alpha r := by
  rw [alpha]
  positivity

theorem tailAllocation_nonneg (r q : ℕ) :
    0 ≤ tailAllocation r q := by
  by_cases htail : 201 ≤ r ∧ q = leastPrimeAbove r
  · simp only [tailAllocation, if_pos htail]
    exact (alpha_pos r).le
  · simp [tailAllocation, htail]









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.InfiniteAllocationCore -/
section


/-!
# The exact infinite cofactor array: structural layer

This file splices the 200 finite certificate rows to the least-prime tail.
It proves nonnegativity, the permitted cofactor support, every exact row
identity, and finite-support formulas for each prime load.  The capacity
inequalities are instantiated in `InfiniteAllocation.lean`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The literal infinite array in Lemma 4.2 of the paper. -/
def infiniteAllocation (r q : ℕ) : ℚ :=
  finiteAllocation r q + tailAllocation r q

def finitePrimeRowLoad (ℓ r : ℕ) : ℚ :=
  allocationPrimeRowLoad finiteAllocation ℓ r


theorem finiteAllocation_nonneg (r q : ℕ) :
    0 ≤ finiteAllocation r q := by
  classical
  by_cases hrq : (r, q) ∈ finiteAllocationSupport
  · exact (finiteAllocation_pos_of_mem hrq).le
  · rw [finiteAllocation_eq_zero_of_not_mem hrq]

theorem infiniteAllocation_nonneg (r q : ℕ) :
    0 ≤ infiniteAllocation r q := by
  exact add_nonneg (finiteAllocation_nonneg r q)
    (tailAllocation_nonneg r q)



/-- Every row has exactly the mass `alpha r`. -/
theorem infiniteAllocation_row_identity {r : ℕ} (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        infiniteAllocation r q) = alpha r := by
  classical
  by_cases hr200 : r ≤ 200
  · have hnot201 : ¬201 ≤ r := by omega
    simpa [infiniteAllocation, tailAllocation, hnot201] using
      finiteAllocation_row_identity hr hr200
  · have h201 : 201 ≤ r := by omega
    have hfiniteZero (q : ℕ) : finiteAllocation r q = 0 := by
      apply finiteAllocation_eq_zero_of_not_mem
      intro hrq
      exact hr200 (finiteAllocation_support_valid hrq).2.1
    have hleastMem := leastPrimeAbove_mem_allocationRange hr
    calc
      (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          infiniteAllocation r q) =
          ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
            if q = leastPrimeAbove r then alpha r else 0 := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [infiniteAllocation, hfiniteZero q, zero_add, tailAllocation]
        simp [h201]
      _ = alpha r := by
        rw [Finset.sum_eq_single (leastPrimeAbove r)]
        · simp
        · intro q _hq hqne
          simp [hqne]
        · exact fun hnot ↦ (hnot hleastMem).elim









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraChebyshevIdentity -/
section


/-!
# The finite divisor identity behind Nagura's Chebyshev sum

Nagura's fundamental summatory formula starts by expanding each logarithm as
a divisor sum of the von Mangoldt function.  This file records that exact
finite identity, including the factorial endpoint, independently of any
analytic estimate.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open scoped ArithmeticFunction ArithmeticFunction.zeta

/-- Nagura's finite sum `T(n) = ∑_{m=1}^n psi(n/m)`. -/
noncomputable def naguraChebyshevSum (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc 0 n, Chebyshev.psi ((n / m : ℕ) : ℝ)



/-- The finite divisor sum occurring before Nagura reindexes by multiples. -/
noncomputable def naguraDivisorLogSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    ∑ d ∈ k.divisors, ArithmeticFunction.vonMangoldt d







end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraStirlingCombination -/
section


/-!
# Nagura's explicit Stirling combination

Nagura uses the reciprocal identity

`1 / 2 + 1 / 3 + 1 / 7 + 1 / 43 + 1 / 1806 = 1`

to combine six values of his finite Chebyshev sum.  This file records the
analytic half of that argument: the positive term is bounded by the elementary
factorial estimate, and the five subtracted terms are bounded with Mathlib's
proved Stirling lower bound.
-/

namespace Erdos390.WholePaper

/-- The elementary upper model for `log (n!)`. -/
noncomputable def naguraFactorialLogUpper (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (n : ℝ) + 1

/-- The proved Stirling lower model for `log (n!)`. -/
noncomputable def naguraFactorialLogLower (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
    Real.log (n : ℝ) / 2 + Real.log (2 * Real.pi) / 2

/-- The coefficient of the main linear term after Nagura's reciprocal
identity cancels the `k * log k` terms. -/
noncomputable def naguraMainCoefficient : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 7 +
    Real.log 43 / 43 + Real.log 1806 / 1806

















end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraCombinatorial -/
section


/-!
# The combinatorial half of Nagura's Chebyshev argument

This file expands Nagura's six-term `T` combination into a weighted sum of a
decreasing sequence.  Its prefix weights are explicit floor expressions, so a
finite summation-by-parts identity gives the required lower bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper









/-- Nagura's coefficient attached to the `m`th term of the decreasing
Chebyshev sequence. -/
def naguraWeight (m : ℕ) : ℝ :=
  1 - (if 2 ∣ m then 1 else 0) - (if 3 ∣ m then 1 else 0) -
    (if 7 ∣ m then 1 else 0) - (if 43 ∣ m then 1 else 0) -
      (if 1806 ∣ m then 1 else 0)

/-- The exact prefix sum of Nagura's weights. -/
def naguraWeightPrefix (m : ℕ) : ℝ :=
  (m : ℝ) - (m / 2 : ℕ) - (m / 3 : ℕ) - (m / 7 : ℕ) -
    (m / 43 : ℕ) - (m / 1806 : ℕ)





















end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraLowerCombination -/
section


/-!
# Nagura's lower Chebyshev combination

The denominators `2, 3, 5, 30` give a second periodic weight whose prefix
sums are always zero or one.  Expanding `ψ` into the von Mangoldt function
therefore shows that the resulting factorial-log combination is at most
`ψ(n)`.
-/

open scoped BigOperators ArithmeticFunction

namespace Erdos390.WholePaper

def naguraLowerWeight (m : ℕ) : ℝ :=
  1 - (if 2 ∣ m then 1 else 0) - (if 3 ∣ m then 1 else 0) -
    (if 5 ∣ m then 1 else 0) + (if 30 ∣ m then 1 else 0)

def naguraLowerWeightPrefix (m : ℕ) : ℝ :=
  (m : ℝ) - (m / 2 : ℕ) - (m / 3 : ℕ) - (m / 5 : ℕ) + (m / 30 : ℕ)





/-- The lower weight, packaged as an arithmetic function so the finite
Dirichlet-convolution reindexing can be reused directly. -/
noncomputable def naguraLowerWeightArithmetic : ArithmeticFunction ℝ :=
  ⟨fun m ↦ if m = 0 then 0 else naguraLowerWeight m, by simp⟩





/-- Nagura's factorial-log combination used for the lower bound on `ψ`. -/
noncomputable def naguraLowerChebyshevCombination (n : ℕ) : ℝ :=
  naguraChebyshevSum n - naguraChebyshevSum (n / 2) -
    naguraChebyshevSum (n / 3) - naguraChebyshevSum (n / 5) +
      naguraChebyshevSum (n / 30)





end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraExplicitPsiBounds -/
section


/-!
# Explicit Nagura-style bounds for `ψ` on arithmetic progressions

This file completes the safe factorial/Stirling chain for the lower
`2,3,5,30` combination.  Together with the upper `1806` combination, it gives
fully explicit, unconditional `ψ` estimates at natural endpoints divisible
by the relevant common denominator.
-/

open scoped BigOperators

namespace Erdos390.WholePaper









/-- The main coefficient of Nagura's lower factorial combination. -/
noncomputable def naguraLowerMainCoefficient : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 -
    Real.log 30 / 30























end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraGeneralUpperModel -/
section


/-!
# A floor-uniform upper model for Nagura's first combination

This is the general-integer counterpart of the exact `1806 k` calculation.
For each denominator, `floor (n / d)` is replaced by a real lower endpoint;
all rounding losses remain explicit.
-/

namespace Erdos390.WholePaper

/-- Nagura's first combination at an arbitrary natural endpoint. -/
noncomputable def naguraGeneralUpperCombination (n : ℕ) : ℝ :=
  naguraChebyshevSum n - naguraChebyshevSum (n / 2) -
    naguraChebyshevSum (n / 3) - naguraChebyshevSum (n / 7) -
      naguraChebyshevSum (n / 43) - naguraChebyshevSum (n / 1806)

/-- A real lower model for the Stirling expression at `floor (n / d)`.
The quantity `(n - d + 1) / d` is a lower bound for that floor. -/
noncomputable def naguraFloorFactorialLowerModel (n d : ℕ) : ℝ :=
  let x := (n : ℝ)
  let y := (x - (d : ℝ) + 1) / (d : ℝ)
  y * Real.log y - x / (d : ℝ) + Real.log y / 2 +
    Real.log (2 * Real.pi) / 2



/-- Stirling upper model for the arbitrary-endpoint combination. -/
noncomputable def naguraGeneralUpperModel (n : ℕ) : ℝ :=
  naguraFactorialLogUpper n - naguraFloorFactorialLowerModel n 2 -
    naguraFloorFactorialLowerModel n 3 - naguraFloorFactorialLowerModel n 7 -
      naguraFloorFactorialLowerModel n 43 -
        naguraFloorFactorialLowerModel n 1806



end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraGeneralUpperBound -/
section


/-!
# The general-integer upper estimate in Nagura's Lemma 2

All floor losses from the first combination are bounded uniformly.  The
threshold `20000` is intentionally conservative; the already-certified prime
chain covers the lower finite range needed by the final application.
-/

namespace Erdos390.WholePaper



/-- The preceding logarithm estimate inserted into the real factorial lower
model. -/
noncomputable def naguraFloorFactorialCoarseModel (n d : ℕ) : ℝ :=
  let x := (n : ℝ)
  let δ := (d : ℝ)
  let y := (x - δ + 1) / δ
  let L := Real.log x - Real.log δ - (δ - 1) / (x - δ + 1)
  y * L - x / δ + L / 2 + Real.log (2 * Real.pi) / 2



/-- The arbitrary-endpoint model after replacing each logarithm by its
explicit rational-error lower bound. -/
noncomputable def naguraGeneralUpperCoarseModel (n : ℕ) : ℝ :=
  naguraFactorialLogUpper n - naguraFloorFactorialCoarseModel n 2 -
    naguraFloorFactorialCoarseModel n 3 -
      naguraFloorFactorialCoarseModel n 7 -
        naguraFloorFactorialCoarseModel n 43 -
          naguraFloorFactorialCoarseModel n 1806



/-- The residual rational loss from the five floor operations. -/
noncomputable def naguraUpperRoundingError (x : ℝ) : ℝ :=
  (1 / (x - 1) + 2 / (x - 2) + 6 / (x - 6) +
    42 / (x - 42) + 1805 / (x - 1805)) / 2





















end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraGeneralLowerBound -/
section


/-!
# The general-integer lower estimate in Nagura's Lemma 2

The three negatively signed factorials are evaluated at floors.  Bounding
each floor between `x / d - 1` and `x / d` costs only one additive unit in
the elementary factorial majorant.  The positively signed `n / 30` term
uses the same shifted Stirling minorant as the general upper estimate.
-/

namespace Erdos390.WholePaper

/-- A floor-uniform upper model for `log ((n / d)!)`. -/
noncomputable def naguraFactorialUpperDivCoarseModel (n d : ℕ) : ℝ :=
  let x := (n : ℝ)
  let δ := (d : ℝ)
  x / δ * (Real.log x - Real.log δ) - x / δ +
    (Real.log x - Real.log δ) + 2



/-- A lower model for the arbitrary-endpoint `2,3,5,30` combination. -/
noncomputable def naguraGeneralLowerModel (n : ℕ) : ℝ :=
  naguraFactorialLogLower n - naguraFactorialUpperDivCoarseModel n 2 -
    naguraFactorialUpperDivCoarseModel n 3 -
      naguraFactorialUpperDivCoarseModel n 5 +
        naguraFloorFactorialCoarseModel n 30



/-- The sole rational loss left by the positive `n / 30` floor. -/
noncomputable def naguraLowerRoundingError (x : ℝ) : ℝ :=
  29 / (x - 30 + 1) / 2









end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPsiBridge -/
section


/-!
# The Chebyshev-function bridge in Nagura's argument

This file isolates the assumption-free combinatorial part of Nagura's
explicit proof.  Strict growth of `Chebyshev.theta` across a natural interval
forces a prime in that interval.  Mathlib's proved comparison between
`Chebyshev.psi` and `Chebyshev.theta` then turns a concrete `psi` gap into the
strict natural-number Nagura conclusion.

No explicit estimate for `psi` is assumed globally here.  Proving the concrete
gap in `hasNaguraPrime_of_psi_gap` uniformly is precisely the remaining
effective analytic step.
-/

namespace Erdos390.WholePaper

/-- Largest natural upper endpoint that is certainly strictly below `6n/5`. -/
def naguraStrictUpper (n : ℕ) : ℕ :=
  (6 * n - 1) / 5







end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FinitePrefixAllocationCapacity -/
section


/-!
# Capacity of every fixed prefix of the infinite allocation

The stationary-anchor construction realizes finitely many rows of the exact
infinite allocation.  This file proves that their literal weighted load is
bounded by the already certified full load.  No limiting argument occurs
here; it is finite-sum and summability algebra over the concrete allocation.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The valuation load in rows `1,...,R` of the concrete allocation. -/
def prefixAllocationPrimeLoad (R ℓ : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc 1 R,
    ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
      (q.factorization ℓ : ℚ) * infiniteAllocation r q











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ExactFinitePartition -/
section


/-!
# Exact finite partitions with prescribed part sizes

This module is independent of the asymptotic allocation argument. It turns
finite target counts into actual disjoint Finset parts and an explicit
remainder.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- An exact partition of the source into indexed parts and a remainder. -/
structure ExactFinitePartition {α ι : Type*} [DecidableEq α]
    (source : Finset α) (indices : Finset ι) (count : ι → ℕ) where
  parts : ι → Finset α
  remainder : Finset α
  parts_subset : ∀ i ∈ indices, parts i ⊆ source
  parts_card : ∀ i ∈ indices, (parts i).card = count i
  parts_pairwiseDisjoint : (indices : Set ι).PairwiseDisjoint parts
  remainder_subset : remainder ⊆ source
  part_remainder_disjoint : ∀ i ∈ indices, Disjoint (parts i) remainder
  union_remainder : indices.biUnion parts ∪ remainder = source
  union_card : (indices.biUnion parts).card = ∑ i ∈ indices, count i
  remainder_card :
    remainder.card = source.card - ∑ i ∈ indices, count i





/-- Counts obtained by assigning all non-distinguished targets first and
giving the distinguished coordinate the remaining cardinality. -/
def distinguishedRemainderCount {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (distinguished : ι) (rawCount : ι → ℕ)
    (total : ℕ) (i : ι) : ℕ :=
  if i = distinguished then
    total - ∑ j ∈ indices.erase distinguished, rawCount j
  else rawCount i





/-- The natural floor of a real scale times a target weight. -/
def scaledFloorCount {ι : Type*}
    (scale : ℝ) (weight : ι → ℝ) (i : ι) : ℕ :=
  ⌊scale * weight i⌋₊







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryPrefixRealization -/
section


/-!
# Exact realization of a fixed stationary prefix

For a fixed row, this module realizes every positive coordinate of the
infinite allocation by an actual part of the stationary prime layer.
Non-distinguished coordinates are rounded down at the second-order scale;
one fixed positive coordinate absorbs the complete rounding remainder.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The finite set of strictly positive cofactor coordinates in row r. -/
def infiniteAllocationPositiveSupport (r : ℕ) : Finset ℕ :=
  (Finset.Icc (r + 1) (2 * r + 1)).filter fun q ↦
    0 < infiniteAllocation r q

@[simp]
theorem mem_infiniteAllocationPositiveSupport {r q : ℕ} :
    q ∈ infiniteAllocationPositiveSupport r ↔
      q ∈ Finset.Icc (r + 1) (2 * r + 1) ∧
        0 < infiniteAllocation r q := by
  simp only [infiniteAllocationPositiveSupport, Finset.mem_filter]

/-- Removing the zero coordinates does not change the exact row mass. -/
theorem infiniteAllocationPositiveSupport_sum
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ infiniteAllocationPositiveSupport r,
        infiniteAllocation r q) = alpha r := by
  rw [← infiniteAllocation_row_identity hr]
  apply Finset.sum_subset
  · intro q hq
    exact (mem_infiniteAllocationPositiveSupport.mp hq).1
  · intro q hq hqNotSupport
    have hnotPos : ¬0 < infiniteAllocation r q := by
      intro hpos
      exact hqNotSupport
        (mem_infiniteAllocationPositiveSupport.mpr ⟨hq, hpos⟩)
    exact le_antisymm (not_lt.mp hnotPos)
      (infiniteAllocation_nonneg r q)

theorem infiniteAllocationPositiveSupport_nonempty
    (r : ℕ) (hr : 1 ≤ r) :
    (infiniteAllocationPositiveSupport r).Nonempty := by
  by_contra h
  have hempty : infiniteAllocationPositiveSupport r = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  have hsum := infiniteAllocationPositiveSupport_sum r hr
  rw [hempty] at hsum
  simp only [Finset.sum_empty] at hsum
  exact (alpha_pos r).ne' hsum.symm





/-- The raw floor target before the distinguished coordinate absorbs the
remainder. -/
def stationaryPrefixRawCount (n r q : ℕ) : ℕ :=
  scaledFloorCount (secondOrderScale n)
    (fun j ↦ (infiniteAllocation r j : ℝ)) q

/-- The exact exhaustive target counts in row r. -/
def stationaryPrefixCount
    (n r distinguished q : ℕ) : ℕ :=
  distinguishedRemainderCount (infiniteAllocationPositiveSupport r)
    distinguished (stationaryPrefixRawCount n r)
    (stationaryPrimeLayer n r).card q















/-- An actual exhaustive indexed partition of one stationary layer. -/
structure StationaryPrefixPartition
    (n r distinguished : ℕ) where
  parts : ℕ → Finset ℕ
  parts_subset :
    ∀ q ∈ infiniteAllocationPositiveSupport r,
      parts q ⊆ stationaryPrimeLayer n r
  parts_card :
    ∀ q ∈ infiniteAllocationPositiveSupport r,
      (parts q).card = stationaryPrefixCount n r distinguished q
  parts_pairwiseDisjoint :
    (infiniteAllocationPositiveSupport r : Set ℕ).PairwiseDisjoint parts
  union_parts :
    (infiniteAllocationPositiveSupport r).biUnion parts =
      stationaryPrimeLayer n r





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryPrefixAnchors -/
section


/-!
# Simultaneous fixed-prefix rows and their central anchors

The analytic realization is first made simultaneous over an arbitrary
finite set of fixed rows.  For one realized row, the marked pairs
(cofactor, prime) are then sent to the literal anchor prime times cofactor.
The map is injective once the stationary primes exceed the cofactor range,
and its finite product splits exactly into marker and cofactor products.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



/-- The finite type of marked pairs in one realized stationary row. -/
def stationaryPrefixMarkedPairs
    (r : ℕ) (parts : ℕ → Finset ℕ) :
    Finset (Σ _q : ℕ, ℕ) :=
  (infiniteAllocationPositiveSupport r).sigma parts







/-- Product of their assigned allocation cofactors. -/
def stationaryPrefixCofactorProduct
    (r : ℕ) (parts : ℕ → Finset ℕ) : ℕ :=
  (stationaryPrefixMarkedPairs r parts).prod fun x ↦ x.1















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryPrefixValuationAsymptotic -/
section


/-!
# Valuation asymptotic of the actual fixed-prefix cofactor product

The cofactor product in this file is the literal product of the cofactors
attached to all realized marker primes in rows one through R.  Its exact
factorization is reduced to the actual part cardinalities, whose already
proved limits give the certified finite-prefix allocation load.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section









/-- The product of the actual cofactor products in rows one through R. -/
def stationaryPrefixCofactorProductUpTo
    (R : ℕ)
    (parts :
      {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ) : ℕ :=
  ∏ r : {r // r ∈ Finset.Icc 1 R},
    stationaryPrefixCofactorProduct r.1 (parts r)















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryPrefixCentralCofactorChoice -/
section


/-!
# Actual fixed-prefix cofactor routing at the central-anchor cutoff

An exhaustive family of stationary-row partitions determines a literal
cofactor for every large central prime.  Row-zero primes receive cofactor
one.  A prime in a positive fixed row receives the unique label of the
partition part containing it.  This file proves that the resulting total
function is an admissible large-central cofactor choice and that its honest
large-cofactor product is exactly the previously analyzed fixed-prefix
product.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The finite subtype of positive stationary rows through `R`. -/
abbrev StationaryPrefixRow (R : ℕ) :=
  {r : ℕ // r ∈ Finset.Icc 1 R}

/-- The routing data needed from simultaneous exact prefix partitions. -/
def IsStationaryPrefixPartFamily
    (R n : ℕ)
    (parts : StationaryPrefixRow R → ℕ → Finset ℕ) : Prop :=
  ∀ r : StationaryPrefixRow R,
    (∀ q ∈ infiniteAllocationPositiveSupport r.1,
      parts r q ⊆ stationaryPrimeLayer n r.1) ∧
    (infiniteAllocationPositiveSupport r.1 : Set ℕ).PairwiseDisjoint
      (parts r) ∧
    (infiniteAllocationPositiveSupport r.1).biUnion (parts r) =
      stationaryPrimeLayer n r.1



/-- The total cofactor function read from a realized fixed-prefix
partition.  Its fallback branches are irrelevant once the realization and
cutoff hypotheses hold, but make the definition total for every natural
marker. -/
noncomputable def stationaryPrefixCofactorChoice
    (R n : ℕ)
    (parts : StationaryPrefixRow R → ℕ → Finset ℕ)
    (p : ℕ) : ℕ :=
  if n < p then
    1
  else
    dite (n / p ∈ Finset.Icc 1 R)
      (fun hrow ↦
        dite
          (∃ q ∈ infiniteAllocationPositiveSupport (n / p),
            p ∈ parts ⟨n / p, hrow⟩ q)
          (fun hq ↦ Classical.choose hq)
          (fun _ ↦ 1))
      (fun _ ↦ 1)







/-- All marked `(row, cofactor, prime)` triples in the fixed prefix. -/
def stationaryPrefixMarkedTriples
    (R : ℕ)
    (parts : StationaryPrefixRow R → ℕ → Finset ℕ) :
    Finset (Σ _r : StationaryPrefixRow R, Σ _q : ℕ, ℕ) :=
  (Finset.univ : Finset (StationaryPrefixRow R)).sigma
    (fun r ↦ stationaryPrefixMarkedPairs r.1 (parts r))

@[simp]
theorem mem_stationaryPrefixMarkedTriples
    {R : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    {x : Σ _r : StationaryPrefixRow R, Σ _q : ℕ, ℕ} :
    x ∈ stationaryPrefixMarkedTriples R parts ↔
      x.2.1 ∈ infiniteAllocationPositiveSupport x.1.1 ∧
        x.2.2 ∈ parts x.1 x.2.1 := by
  simp only [stationaryPrefixMarkedTriples,
    stationaryPrefixMarkedPairs, Finset.mem_sigma, Finset.mem_univ,
    true_and]





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorExistence -/
section


/-!
# Eventual existence of the complete central-anchor family

For every `c > C0`, one fixed prefix depth is chosen.  The promotion cost,
actual stationary-prefix allocation, and factorial-tail reserve are then
combined into an honest routed cofactor function and an honest finite set
of central anchors.  The certificate records interval containment, the
exact product identity, and literal divisibility of the anchor divisor into
the upper tail product.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- A canonical positive-support coordinate in every positive row. -/
noncomputable def stationaryPrefixDistinguished (r : ℕ) : ℕ :=
  dite (1 ≤ r)
    (fun hr ↦
      Classical.choose
        (infiniteAllocationPositiveSupport_nonempty r hr))
    (fun _ ↦ 0)



/-- The complete finite object produced by the central-anchor argument at
one `n`.  Besides the exact anchor product, it exposes the fixed prime
support and the quantitative one-third tail reserve needed when later bank
guards modify finitely many prefix cofactors. -/
structure CentralAnchorCertificate (c : ℝ) (R n : ℕ) where
  q : ℕ → ℕ
  anchors : Finset ℕ
  isCofactorChoice :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q
  anchors_eq :
    anchors = fullCentralAnchors n (centralAnchorCutoff R n) q
  anchors_subset : anchors ⊆ Finset.Ioc n (2 * n)
  anchors_prod :
    anchors.prod id =
      Nat.choose (2 * n) n *
        centralAnchorDivisor n (centralAnchorCutoff R n) q
  divisor_prime_support :
    ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ∣ centralAnchorDivisor n (centralAnchorCutoff R n) q →
        ℓ ∈ primesUpTo (2 * R + 1)
  divisor_reserve :
    ∀ ℓ ∈ primesUpTo (2 * R + 1),
      (c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          ((centralAnchorDivisor n
            (centralAnchorCutoff R n) q).factorization ℓ : ℝ) ≤
        (upperTailValuation c n ℓ : ℝ)
  divisor_dvd_tail :
    centralAnchorDivisor n (centralAnchorCutoff R n) q ∣
      centralTailProduct n (upperTailLength c n)



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorGuardedChoice -/
section


/-!
# A concrete guarded modification of routed central cofactors

For a finite set of bank markers, row one uses the literal replacement
cofactor `3`.  Every higher positive carry row uses the first of
`r+1,r+2,r+3` which avoids the two incident bank-state cores.  This file is
pure finite arithmetic: it proves that the modified function is still an
actual routed central-cofactor choice and records the exact hypotheses under
which both incident cores are avoided.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- Modify `q` exactly on `changed`.  Row one has only the legal cofactors
`2,3`, so the bank construction separately guarantees that `3` is not an
incident state core.  Higher rows have the three-candidate replacement from
`BankAnchorGuardsFinite`. -/
def guardedCentralCofactor (n : ℕ) (q left right : ℕ → ℕ)
    (changed : Finset ℕ) (p : ℕ) : ℕ :=
  if p ∈ changed then
    if n / p = 1 then 3
    else prefixReplacementCofactor (n / p) (left p) (right p)
  else q p

@[simp]
theorem guardedCentralCofactor_eq_of_not_mem
    {n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    {p : ℕ} (hp : p ∉ changed) :
    guardedCentralCofactor n q left right changed p = q p := by
  simp [guardedCentralCofactor, hp]

@[simp]
theorem guardedCentralCofactor_eq_three_of_mem_row_one
    {n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    {p : ℕ} (hp : p ∈ changed) (hrow : n / p = 1) :
    guardedCentralCofactor n q left right changed p = 3 := by
  simp [guardedCentralCofactor, hp, hrow]











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperAnchorChangeBudget -/
section


/-!
# The cost of guarding every realized bank marker is negligible

The deliberately coarse global marker bound is `O(yNat²)`.  Since
`yNat² = o(n/log n)`, even changing every realized bank marker which meets
the fixed central prefix consumes only an arbitrarily small fixed fraction
of the central valuation reserve.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- A realization-independent numerical upper bound for all changed bank
markers. -/
def bankPaperAnchorMarkerBudget (n : ℕ) : ℕ :=
  (bankOrdinaryPaperRequests n).card + 8 * bankBottomPaperDemand n











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrecharge -/
section


/-!
# The actual precharged bank state

This module is independent of the eventual path selector.  Its component
index is the already realized global request type: every relevant bottom row
and every ordinary row occurs exactly once.  For each component we expose its
orientation-aware base and alternate states and its actual donor occurrence.

The proofs below use only the explicit component geometry.  In particular,
there is no abstract capacity or compatibility hypothesis: global
injectivity follows from the realized occurrence-set disjointness, and the
donor tail is the literal interval `(2n,M]`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section



namespace BankBottomPaperRealization



end BankBottomPaperRealization

namespace BankPaperRealization

attribute [local instance] Erdos390.WholePaper.BankPaperRealization.bankPaperMarkerRequestDecidableEq

/-! ## Global component data -/



/-- Orientation-aware state occupied after the component move. -/
def prechargeAlternateStateValue
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → ℕ
  | .inl request =>
      R.bottom.toStateValue
        (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.toStateValue request

/-- The actual donor occurrence backing a component. -/
def prechargeDonorValue
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → ℕ
  | .inl request =>
      R.bottom.donorFactor
        (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.donorValue request



theorem prechargeBaseStateValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈
      R.prechargeComponentOccurrences request := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      rw [prechargeBaseStateValue, prechargeComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      cases horientation : bankSignedSlotOrientation fullRequest.1.1 <;>
        simp [BankBottomPaperRealization.fromStateValue,
          fullRequest, horientation]
  | inr request =>
      cases horientation :
          (bankOrdinaryPaperRequestPool n request.1).2
      · simpa only [prechargeBaseStateValue,
          prechargeComponentOccurrences,
          BankOrdinaryPaperRealization.fromStateValue, horientation,
          BankOrdinaryPaperRealization.occurrenceValue_sourceState] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            request .sourceState
      · simpa only [prechargeBaseStateValue,
          prechargeComponentOccurrences,
          BankOrdinaryPaperRealization.fromStateValue, horientation,
          BankOrdinaryPaperRealization.occurrenceValue_targetState] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            request .targetState

theorem prechargeAlternateStateValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeAlternateStateValue request ∈
      R.prechargeComponentOccurrences request := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      rw [prechargeAlternateStateValue, prechargeComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      cases horientation : bankSignedSlotOrientation fullRequest.1.1 <;>
        simp [BankBottomPaperRealization.toStateValue,
          fullRequest, horientation]
  | inr request =>
      cases horientation :
          (bankOrdinaryPaperRequestPool n request.1).2
      · simpa only [prechargeAlternateStateValue,
          prechargeComponentOccurrences,
          BankOrdinaryPaperRealization.toStateValue, horientation,
          BankOrdinaryPaperRealization.occurrenceValue_targetState] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            request .targetState
      · simpa only [prechargeAlternateStateValue,
          prechargeComponentOccurrences,
          BankOrdinaryPaperRealization.toStateValue, horientation,
          BankOrdinaryPaperRealization.occurrenceValue_sourceState] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            request .sourceState

theorem prechargeDonorValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈
      R.prechargeComponentOccurrences request := by
  cases request with
  | inl request =>
      rw [prechargeDonorValue, prechargeComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      simp
  | inr request =>
      simpa only [prechargeDonorValue, prechargeComponentOccurrences,
        BankOrdinaryPaperRealization.occurrenceValue_donor] using
        R.ordinary.occurrenceValue_mem_componentOccurrences request .donor

/-- Actual occurrence sets of different global components are disjoint. -/
theorem prechargeComponentOccurrences_disjoint
    {n M : ℕ} (R : BankPaperRealization n M)
    {request request' : BankPaperMarkerRequest n}
    (hrequest : request ≠ request') :
    Disjoint (R.prechargeComponentOccurrences request)
      (R.prechargeComponentOccurrences request') := by
  cases request with
  | inl bottomRequest =>
      cases request' with
      | inl bottomRequest' =>
          apply R.bottom.componentOccurrences_disjoint_of_request_ne
            R.ordinary.two_mul_n_le_M R.six_le_yNat
            R.three_mul_yNat_le_n
          intro hfull
          apply hrequest
          apply congrArg Sum.inl
          exact bankBottomRelevantRequestToPaperRequest_injective hfull
      | inr ordinaryRequest =>
          exact (R.ordinaryComponent_disjoint_bottomComponent
            ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)).symm
  | inr ordinaryRequest =>
      cases request' with
      | inl bottomRequest =>
          exact R.ordinaryComponent_disjoint_bottomComponent
            ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
      | inr ordinaryRequest' =>
          apply R.ordinary.componentOccurrences_disjoint
          intro hordinary
          exact hrequest (congrArg Sum.inr hordinary)









/-! ## Complete rough signatures -/

/-- Base, alternate, and donor are three tokens in one complete-signature
row.  In a terminal bottom row two of these numerical occurrences may agree. -/
theorem precharge_completeRoughSignature_eq
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
        completeRoughSignature (yNat n)
          (R.prechargeAlternateStateValue request) ∧
      completeRoughSignature (yNat n)
          (R.prechargeAlternateStateValue request) =
        completeRoughSignature (yNat n)
          (R.prechargeDonorValue request) := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hlower := R.bottom.occurrenceValue_completeRoughSignature
        R.six_le_yNat fullRequest .lowerState
      have hupper := R.bottom.occurrenceValue_completeRoughSignature
        R.six_le_yNat fullRequest .upperState
      have hdonor := R.bottom.occurrenceValue_completeRoughSignature
        R.six_le_yNat fullRequest .donor
      have hlower' :
          completeRoughSignature (yNat n)
              (R.bottom.lowerStateFactor fullRequest) =
            completeRoughSignature (yNat n)
              (R.bottom.marker fullRequest) := by
        simpa only [BankBottomPaperRealization.occurrenceValue_lowerState]
          using hlower
      have hupper' :
          completeRoughSignature (yNat n)
              (R.bottom.upperStateFactor fullRequest) =
            completeRoughSignature (yNat n)
              (R.bottom.marker fullRequest) := by
        simpa only [BankBottomPaperRealization.occurrenceValue_upperState]
          using hupper
      have hdonor' :
          completeRoughSignature (yNat n)
              (R.bottom.donorFactor fullRequest) =
            completeRoughSignature (yNat n)
              (R.bottom.marker fullRequest) := by
        simpa only [BankBottomPaperRealization.occurrenceValue_donor]
          using hdonor
      cases horientation : bankSignedSlotOrientation fullRequest.1.1
      · simpa [prechargeBaseStateValue, prechargeAlternateStateValue,
          prechargeDonorValue, BankBottomPaperRealization.fromStateValue,
          BankBottomPaperRealization.toStateValue, fullRequest,
          horientation] using
          ⟨hupper'.trans hlower'.symm,
            hlower'.trans hdonor'.symm⟩
      · simpa [prechargeBaseStateValue, prechargeAlternateStateValue,
          prechargeDonorValue, BankBottomPaperRealization.fromStateValue,
          BankBottomPaperRealization.toStateValue, fullRequest,
          horientation] using
          ⟨hlower'.trans hupper'.symm,
            hupper'.trans hdonor'.symm⟩
  | inr request =>
      have hsignature :=
        R.ordinary.state_donor_completeRoughSignature_eq request
      cases horientation :
          (bankOrdinaryPaperRequestPool n request.1).2
      · simpa only [prechargeBaseStateValue,
          prechargeAlternateStateValue, prechargeDonorValue,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.toStateValue, horientation] using
          hsignature
      · simpa only [prechargeBaseStateValue,
          prechargeAlternateStateValue, prechargeDonorValue,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.toStateValue, horientation] using
          ⟨hsignature.1.symm,
            hsignature.1.trans hsignature.2⟩

theorem prechargeBase_donor_completeRoughSignature_eq
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
      completeRoughSignature (yNat n)
        (R.prechargeDonorValue request) :=
  (R.precharge_completeRoughSignature_eq request).1.trans
    (R.precharge_completeRoughSignature_eq request).2



/-! ## Endpoint and donor injectivity -/

def prechargeEndpointValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    BankPaperPrechargeEndpoint → ℕ
  | .base => R.prechargeBaseStateValue request
  | .alternate => R.prechargeAlternateStateValue request

theorem prechargeEndpointValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n)
    (endpoint : BankPaperPrechargeEndpoint) :
    R.prechargeEndpointValue request endpoint ∈
      R.prechargeComponentOccurrences request := by
  cases endpoint
  · exact R.prechargeBaseStateValue_mem_componentOccurrences request
  · exact R.prechargeAlternateStateValue_mem_componentOccurrences request

/-- Arbitrary state endpoints belonging to different components cannot
collide. -/
theorem prechargeEndpointValue_ne_of_request_ne
    {n M : ℕ} (R : BankPaperRealization n M)
    {request request' : BankPaperMarkerRequest n}
    (hrequest : request ≠ request')
    (endpoint endpoint' : BankPaperPrechargeEndpoint) :
    R.prechargeEndpointValue request endpoint ≠
      R.prechargeEndpointValue request' endpoint' := by
  intro heq
  have hdisjoint := R.prechargeComponentOccurrences_disjoint hrequest
  exact (Finset.disjoint_left.mp hdisjoint)
    (R.prechargeEndpointValue_mem_componentOccurrences request endpoint)
    (by
      rw [heq]
      exact R.prechargeEndpointValue_mem_componentOccurrences
        request' endpoint')







theorem prechargeBaseStateValue_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeBaseStateValue := by
  intro request request' heq
  by_contra hrequest
  exact R.prechargeEndpointValue_ne_of_request_ne
    hrequest .base .base heq



/-- Donors are globally injective even though, within a terminal bottom
component, the donor is literally the same occurrence as one endpoint. -/
theorem prechargeDonorValue_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeDonorValue := by
  intro request request' heq
  by_contra hrequest
  have hdisjoint := R.prechargeComponentOccurrences_disjoint hrequest
  exact (Finset.disjoint_left.mp hdisjoint)
    (R.prechargeDonorValue_mem_componentOccurrences request)
    (by
      rw [heq]
      exact R.prechargeDonorValue_mem_componentOccurrences request')



/-! ## Literal finite states, donor tail, and replacement map -/



def prechargeAlternateState
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  indexedPathState R.prechargeAlternateStateValue

def prechargeDonorSet
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  indexedPathState R.prechargeDonorValue

@[simp] theorem prechargeBaseStateValue_mem_prechargeBaseState
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈ R.prechargeBaseState := by
  simp [prechargeBaseState, indexedPathState]

@[simp] theorem prechargeAlternateStateValue_mem_prechargeAlternateState
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeAlternateStateValue request ∈
      R.prechargeAlternateState := by
  simp [prechargeAlternateState, indexedPathState]

@[simp] theorem prechargeDonorValue_mem_prechargeDonorSet
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ R.prechargeDonorSet := by
  simp [prechargeDonorSet, indexedPathState]



















theorem prechargeDonor_existsUnique_request
    {n M donor : ℕ} (R : BankPaperRealization n M)
    (hdonor : donor ∈ R.prechargeDonorSet) :
    ∃! request : BankPaperMarkerRequest n,
      R.prechargeDonorValue request = donor := by
  rw [prechargeDonorSet, indexedPathState, Finset.mem_image] at hdonor
  obtain ⟨request, _hrequest, hvalue⟩ := hdonor
  refine ⟨request, hvalue, ?_⟩
  intro request' hvalue'
  exact R.prechargeDonorValue_injective
    (hvalue'.trans hvalue.symm)

def requestForPrechargeDonor
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) : BankPaperMarkerRequest n :=
  Classical.choose (R.prechargeDonor_existsUnique_request donor.property)

@[simp] theorem prechargeDonorValue_requestForPrechargeDonor
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) :
    R.prechargeDonorValue (R.requestForPrechargeDonor donor) = donor.1 :=
  (Classical.choose_spec
    (R.prechargeDonor_existsUnique_request donor.property)).1

theorem requestForPrechargeDonor_unique
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet)
    (request : BankPaperMarkerRequest n)
    (hdonor : R.prechargeDonorValue request = donor.1) :
    request = R.requestForPrechargeDonor donor := by
  exact R.prechargeDonorValue_injective
    (hdonor.trans
      (R.prechargeDonorValue_requestForPrechargeDonor donor).symm)

/-- Replace a donor token by the orientation-aware base token of its unique
component. -/
def prechargeDonorToBase
    {n M : ℕ} (R : BankPaperRealization n M) :
    ↑R.prechargeDonorSet → ↑R.prechargeBaseState :=
  fun donor =>
    ⟨R.prechargeBaseStateValue (R.requestForPrechargeDonor donor),
      R.prechargeBaseStateValue_mem_prechargeBaseState _⟩

theorem prechargeDonorToBase_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeDonorToBase := by
  intro donor donor' hbase
  have hrequest : R.requestForPrechargeDonor donor =
      R.requestForPrechargeDonor donor' :=
    R.prechargeBaseStateValue_injective
      (congrArg Subtype.val hbase)
  apply Subtype.ext
  calc
    donor.1 = R.prechargeDonorValue
        (R.requestForPrechargeDonor donor) :=
      (R.prechargeDonorValue_requestForPrechargeDonor donor).symm
    _ = R.prechargeDonorValue
        (R.requestForPrechargeDonor donor') := by rw [hrequest]
    _ = donor'.1 :=
      R.prechargeDonorValue_requestForPrechargeDonor donor'

theorem prechargeDonorToBase_surjective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Surjective R.prechargeDonorToBase := by
  intro base
  have hbaseMem := base.property
  change base.1 ∈ Finset.univ.image R.prechargeBaseStateValue at hbaseMem
  rw [Finset.mem_image] at hbaseMem
  obtain ⟨request, _hrequest, hbase⟩ := hbaseMem
  let donor : ↑R.prechargeDonorSet :=
    ⟨R.prechargeDonorValue request,
      R.prechargeDonorValue_mem_prechargeDonorSet request⟩
  refine ⟨donor, ?_⟩
  apply Subtype.ext
  have hrequestFor : R.requestForPrechargeDonor donor = request := by
    symm
    exact R.requestForPrechargeDonor_unique donor request rfl
  change R.prechargeBaseStateValue
      (R.requestForPrechargeDonor donor) = base.1
  rw [hrequestFor, hbase]

/-- The donor-to-base replacement is a literal bijection of actual finite
token sets. -/
def prechargeDonorBaseEquiv
    {n M : ℕ} (R : BankPaperRealization n M) :
    ↑R.prechargeDonorSet ≃ ↑R.prechargeBaseState :=
  Equiv.ofBijective R.prechargeDonorToBase
    ⟨R.prechargeDonorToBase_injective,
      R.prechargeDonorToBase_surjective⟩

theorem prechargeDonorToBase_completeRoughSignature
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) :
    completeRoughSignature (yNat n)
        (R.prechargeDonorToBase donor).1 =
      completeRoughSignature (yNat n) donor.1 := by
  change completeRoughSignature (yNat n)
      (R.prechargeBaseStateValue (R.requestForPrechargeDonor donor)) =
    completeRoughSignature (yNat n) donor.1
  rw [← R.prechargeDonorValue_requestForPrechargeDonor donor]
  exact R.prechargeBase_donor_completeRoughSignature_eq
    (R.requestForPrechargeDonor donor)

/-! ## Component counts and the base product -/























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalBacking -/
section


/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- The paper's literal exceptional part of `E = (2n,2n+h]`:
`X_{R_y(a)} = 2n / R_y(a) < n ^ deltaStar`, with the comparison made in
the reals exactly as displayed in the paper. -/
def paperExceptionalUpperFactors
    (n h : ℕ) (deltaStar : ℝ) : Finset ℕ :=
  (roughUpperBlock n h).filter fun a ↦
    2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
      (n : ℝ) ^ deltaStar

@[simp]
theorem mem_paperExceptionalUpperFactors
    {n h a : ℕ} {deltaStar : ℝ} :
    a ∈ paperExceptionalUpperFactors n h deltaStar ↔
      a ∈ roughUpperBlock n h ∧
        2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
          (n : ℝ) ^ deltaStar := by
  simp only [paperExceptionalUpperFactors, Finset.mem_filter]



namespace BankPaperRealization

/-- The paper's exhaustive fixed residual class
`G_fix = E_exc \ E_donor`, using the actual globally injective donor set of
the realized bank. -/
def paperFixedExceptionalFactors
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) : Finset ℕ :=
  paperExceptionalUpperFactors n h deltaStar \ R.prechargeDonorSet

@[simp]
theorem mem_paperFixedExceptionalFactors
    {n h a : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : ℝ} :
    a ∈ R.paperFixedExceptionalFactors deltaStar ↔
      a ∈ roughUpperBlock n h ∧
        2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
          (n : ℝ) ^ deltaStar ∧
        a ∉ R.prechargeDonorSet := by
  simp only [paperFixedExceptionalFactors, Finset.mem_sdiff,
    mem_paperExceptionalUpperFactors, and_assoc]























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCommonMultiplierLists -/
section


/-!
# Finite common-multiplier lists for the tangent absorber

This file begins the literal common-list construction of Section 9.  It
defines the integer interval

`(n / v, (2 * n - K * h) / u]`

and applies exactly the five tests appearing in the paper: head
coprimality, the exceptional-row cutoff, exclusion of dedicated rows, and
the two numerical endpoint guards.  The resulting list is finite by
construction.

The uniform positive-density lower bound still needs the paper's reduced
residue-class count and exceptional-row Selberg-sieve estimate.  Everything
around those two analytic inputs is proved here: endpoint location, the
complete-rough-row identity, the exact finite deletion ledger, and the
paper's combinatorial fact that an exhaustive guard set deletes at most two
multipliers per guard.
-/

namespace Erdos390.WholePaper

noncomputable section

/-! ## Literal interval and cleanliness predicates -/

/-- The upper endpoint `2n-Kh` of the broad interval used by the tangent. -/
def tangentBroadUpper (n K h : ℕ) : ℕ :=
  2 * n - K * h

/-- Paper notation `X_{R_y(a)}=2n/R_y(a)`. -/
def tangentRoughScale (n y a : ℕ) : ℕ :=
  2 * n / completeRoughLabel y a

/-- The literal integer common-multiplier interval
`I_uv=(n/v,(2n-Kh)/u]`. -/
def tangentCommonMultiplierInterval
    (n K h u v : ℕ) : Finset ℕ :=
  Finset.Ioc (n / v) (tangentBroadUpper n K h / u)

/-- Multipliers failing the fixed head-coprimality test. -/
def tangentHeadBadMultipliers
    (Phead : ℕ) (multipliers : Finset ℕ) : Finset ℕ :=
  multipliers.filter fun a ↦ ¬Nat.Coprime a Phead

/-- Multipliers in terminal exceptional rough rows, i.e. with
`X_{R_y(a)} < X0`. -/
def tangentExceptionalMultipliers
    (n X0 y : ℕ) (multipliers : Finset ℕ) : Finset ℕ :=
  multipliers.filter fun a ↦ tangentRoughScale n y a < X0

/-- Multipliers whose complete rough label is a fully dedicated row. -/
def tangentDedicatedRowMultipliers
    (y : ℕ) (dedicatedRows multipliers : Finset ℕ) : Finset ℕ :=
  multipliers.filter fun a ↦ completeRoughLabel y a ∈ dedicatedRows

/-- Multipliers whose endpoint at one fixed label hits the exhaustive
numerical guard set. -/
def tangentLabelGuardDeletedMultipliers
    (label : ℕ) (numericalGuards multipliers : Finset ℕ) : Finset ℕ :=
  multipliers.filter fun a ↦ label * a ∈ numericalGuards

/-- Multipliers for which either of the two common-list endpoints is
numerically guarded. -/
def tangentEndpointGuardDeletedMultipliers
    (u v : ℕ) (numericalGuards multipliers : Finset ℕ) : Finset ℕ :=
  tangentLabelGuardDeletedMultipliers u numericalGuards multipliers ∪
    tangentLabelGuardDeletedMultipliers v numericalGuards multipliers

/-- The union of all four deletion classes in the common-list proof.  The
last class incorporates both numerical endpoints. -/
def tangentCommonMultiplierBadSet
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) : Finset ℕ :=
  let interval := tangentCommonMultiplierInterval n K h u v
  tangentHeadBadMultipliers Phead interval ∪
    tangentExceptionalMultipliers n X0 y interval ∪
    tangentDedicatedRowMultipliers y dedicatedRows interval ∪
    tangentEndpointGuardDeletedMultipliers u v numericalGuards interval

/-- The literal clean common list `L^+_{uv}` from Section 9. -/
def tangentCleanCommonMultiplierList
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) : Finset ℕ :=
  (tangentCommonMultiplierInterval n K h u v).filter fun a ↦
    Nat.Coprime a Phead ∧
      X0 ≤ tangentRoughScale n y a ∧
      completeRoughLabel y a ∉ dedicatedRows ∧
      u * a ∉ numericalGuards ∧
      v * a ∉ numericalGuards

@[simp]
theorem mem_tangentCommonMultiplierInterval
    {n K h u v a : ℕ} :
    a ∈ tangentCommonMultiplierInterval n K h u v ↔
      n / v < a ∧ a ≤ tangentBroadUpper n K h / u := by
  simp [tangentCommonMultiplierInterval]

@[simp]
theorem card_tangentCommonMultiplierInterval
    (n K h u v : ℕ) :
    (tangentCommonMultiplierInterval n K h u v).card =
      tangentBroadUpper n K h / u - n / v := by
  simp [tangentCommonMultiplierInterval]

@[simp]
theorem mem_tangentCleanCommonMultiplierList
    {n K h Phead X0 y u v a : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ} :
    a ∈ tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards ↔
      (n / v < a ∧ a ≤ tangentBroadUpper n K h / u) ∧
      Nat.Coprime a Phead ∧
      X0 ≤ tangentRoughScale n y a ∧
      completeRoughLabel y a ∉ dedicatedRows ∧
      u * a ∉ numericalGuards ∧
      v * a ∉ numericalGuards := by
  simp [tangentCleanCommonMultiplierList]

/-! ## Endpoint location and complete rough rows -/









/-! ## Exact finite deletion counts -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPaperNumericalGuards -/
section


/-!
# The literal Section 9 numerical guards and bank-row census

This file instantiates the exhaustive numerical guard family used by the
tangent common lists.  In the notation of the paper it is exactly

`Γ_num = H' ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Here `H'` is the actual guarded central-anchor set, `G_fix` is supplied by
the eventual rough selector, and the last three sets are the already
constructed precharge donor, base-state, and alternate-state sets.  The
global union is bounded directly from these definitions.  For a permitted
pair `u,v`, its lower-endpoint-relevant subfamily has at most two promoted
anchors and two bank states per component; fixed exceptional factors and
donors disappear because they lie strictly above `2n`.

The paper's bank-row census is also made literal.  The nontrivial bank rows
are the realized marker rows, while the fully dedicated set is empty.  Thus
the dedicated-row deletion in `TangentCommonMultiplierLists` is exactly
zero, without an assumed cardinality estimate.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Actual bank rows and the exhaustive five-family guard set -/



/-- Section 9 does not reserve any complete rough row exclusively for the
bank: `D_row = ∅`. -/
def tangentPaperDedicatedRows
    {n M : ℕ} (_R : BankPaperRealization n M) : Finset ℕ :=
  ∅

/-- The paper's exhaustive numerical guard family
`H' ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`. -/
def tangentPaperNumericalGuardSet
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ) : Finset ℕ :=
  certificate.anchors ∪ fixedExceptional ∪ R.prechargeDonorSet ∪
    R.prechargeBaseState ∪ R.prechargeAlternateState





@[simp]
theorem tangentPaperDedicatedRows_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperDedicatedRows.card = 0 := by
  simp [tangentPaperDedicatedRows]



@[simp]
theorem tangentDedicatedRowMultipliers_tangentPaperDedicatedRows
    {n M y : ℕ} (R : BankPaperRealization n M)
    (multipliers : Finset ℕ) :
    tangentDedicatedRowMultipliers y R.tangentPaperDedicatedRows
      multipliers = ∅ := by
  simp [tangentDedicatedRowMultipliers, tangentPaperDedicatedRows]





end BankPaperRealization

/-! ## Only promoted anchors can meet a permitted medium label -/







namespace BankPaperRealization

/-! ## A lossless endpoint-relevant overapproximation and its upper bound -/

/-- A lossless overapproximation of the part of `Γ_num` that could equal one
of the two endpoints in the broad interval.  It may retain guards whose
quotient lies outside the common-multiplier interval.  Under the tail
hypothesis used below, its upper cutoff removes the fixed exceptional and
donor families before counting guards. -/
def tangentPaperPairNumericalGuards
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ) (K h u v : ℕ) : Finset ℕ :=
  (R.tangentPaperNumericalGuardSet certificate fixedExceptional).filter
    fun g ↦ g ≤ tangentBroadUpper n K h ∧ (u ∣ g ∨ v ∣ g)







/-! ## Filtering is lossless for actual endpoint deletion -/











/-! ## The actual deterministic common-list ledger -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger -/
section


/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/

/-- The actual five-family numerical guard set, specialized to the fixed
exceptional set belonging to the realized bank. -/
def roughCanonicalGuardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) : Finset ℕ :=
  R.tangentPaperNumericalGuardSet certificate
    (R.paperFixedExceptionalFactors deltaStar)

/-- The raw lower candidates which survive every numerical guard. -/
def roughCanonicalGuardedCandidateSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) : Finset ℕ :=
  roughRawCandidateSet n h K \
    R.roughCanonicalGuardSet certificate deltaStar

/-- The broad correction pool after deleting all numerical guards. -/
def roughCanonicalGuardedBroadCorrectionPool
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) : Finset ℕ :=
  roughCanonicalBroadCorrectionPool W n h K (yNat n) label \
    R.roughCanonicalGuardSet certificate deltaStar

/-- One complete rough row of the surviving guarded candidates. -/
def roughCanonicalGuardedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) : Finset ℕ :=
  completeRoughRowFiber (yNat n)
    (R.roughCanonicalGuardedCandidateSet certificate deltaStar K) label

/-- The raw coordinates in one row which are removed by the numerical
guards.  This is the paper's local deletion set `D_R`. -/
def roughCanonicalGuardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) : Finset ℕ :=
  completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) label ∩
    R.roughCanonicalGuardSet certificate deltaStar

theorem roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K ⊆
      roughRawCandidateSet n h K := by
  exact Finset.sdiff_subset



theorem roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) :
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label ⊆
      roughCanonicalBroadCorrectionPool W n h K (yNat n) label := by
  exact Finset.sdiff_subset

/-- The guarded broad pool remains in the guarded row.  No nonemptiness or
cardinality lower bound is used. -/
theorem roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) :
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K label := by
  intro a ha
  have haPool := Finset.mem_sdiff.mp ha
  have haRawRow := roughCanonicalBroadCorrectionPool_subset_rawRow
    W n h K (yNat n) label haPool.1
  have haRawData := mem_completeRoughRowFiber.mp haRawRow
  apply mem_completeRoughRowFiber.mpr
  refine ⟨?_, haRawData.2⟩
  exact Finset.mem_sdiff.mpr ⟨haRawData.1, haPool.2⟩









/-! ## The donor/base row-preserving bijection -/

/-- The actual donor-to-base equivalence preserves the integer complete
rough label, not only the vector signature. -/
theorem prechargeDonorBaseEquiv_completeRoughLabel
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) :
    completeRoughLabel (yNat n)
        (R.prechargeDonorBaseEquiv donor).1 =
      completeRoughLabel (yNat n) donor.1 := by
  apply completeRoughSignature_eq_iff_label_eq.mp
  change completeRoughSignature (yNat n)
      (R.prechargeDonorToBase donor).1 =
    completeRoughSignature (yNat n) donor.1
  exact R.prechargeDonorToBase_completeRoughSignature donor

/-- Restrict the actual donor/base equivalence to one complete rough row. -/
def prechargeDonorBaseRowEquiv
    {n M : ℕ} (R : BankPaperRealization n M) (label : ℕ) :
    {donor : ↑R.prechargeDonorSet //
      completeRoughLabel (yNat n) donor.1 = label} ≃
    {base : ↑R.prechargeBaseState //
      completeRoughLabel (yNat n) base.1 = label} :=
  R.prechargeDonorBaseEquiv.subtypeEquiv fun donor ↦ by
    rw [R.prechargeDonorBaseEquiv_completeRoughLabel donor]





/-! ## Upper-tail ownership and the postcharge target -/

/-- A complete rough label is exceptional exactly when its literal real
scale is below the paper cutoff `n ^ deltaStar`.  This is the same strict
comparison used in `paperExceptionalUpperFactors`; it is deliberately not
the rounded natural-number cutoff used later for tangent clean lists. -/
def RoughCanonicalExceptionalLabel
    (n : ℕ) (deltaStar : ℝ) (label : ℕ) : Prop :=
  2 * (n : ℝ) / (label : ℝ) < (n : ℝ) ^ deltaStar

/-- The rows on which the paper performs the nonsmooth correction are the
non-smooth, nonexceptional rows: `label != 1` and
`n ^ deltaStar <= 2n / label`. -/
def RoughCanonicalActiveNonexceptionalLabel
    (n : ℕ) (deltaStar : ℝ) (label : ℕ) : Prop :=
  label ≠ 1 ∧ (n : ℝ) ^ deltaStar ≤ 2 * (n : ℝ) / (label : ℝ)













/-- Integer form of the postcharge quota
`t_R - m_R(G_fix) - m_R(G_bank^0)`. -/
def roughCanonicalPostchargeRowTargetInt
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) : ℤ :=
  (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℤ) -
    (completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) label : ℤ) -
    (completeLabelMultiplicity (yNat n)
      R.prechargeBaseState label : ℤ)

/-- Real form of the same postcharge quota, used by the fractional
correction algebra. -/
def roughCanonicalPostchargeRowTarget
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) : ℝ :=
  (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℝ) -
    (completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) label : ℝ) -
    (completeLabelMultiplicity (yNat n)
      R.prechargeBaseState label : ℝ)









/-! ## Exact local discrepancy ledger -/

/-- Raw row discrepancy before removing the numerical guards. -/
def roughCanonicalRawRowDiscrepancy
    (n h K label : ℕ) (x : ℕ → ℝ) : ℝ :=
  (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℝ) -
    ∑ a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n h K) label, x a

/-- Postcharge discrepancy on the candidates surviving all guards. -/
def roughCanonicalPostchargeRowDiscrepancy
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) : ℝ :=
  R.roughCanonicalPostchargeRowTarget deltaStar label -
    ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
      x a



/-! ## Exact support reduction for the local deletion set -/







/-! ## Explicit remaining finite/analytic obligations -/

/-- A proposed local guard census is deliberately data, not a theorem of
the finite ledger.  The paper only needs a fixed small `budget`. -/
def RoughCanonicalGuardLocalCensusBound
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label budget : ℕ) : Prop :=
  (R.roughCanonicalGuardDeletedRow certificate deltaStar K label).card ≤
    budget

/-- A lower bound for the guarded broad correction pool.  Establishing it
uniformly in active rows is the missing rough-number capacity estimate. -/
def RoughCanonicalGuardedBroadPoolCapacity
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label minimum : ℕ) : Prop :=
  minimum ≤
    (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W K label).card

/-- Capacity of the entire guarded row for its nonnegative postcharge
target.  This does not follow merely from upper-tail ownership. -/
def RoughCanonicalPostchargeRowCapacity
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) : Prop :=
  R.roughCanonicalPostchargeRowTarget deltaStar label ≤
    ((R.roughCanonicalGuardedRow certificate deltaStar K label).card : ℝ)

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/

/-- The fixed Dickman value used as a uniform floor on the full endpoint
range `0 <= u <= 5`. -/
def roughCanonicalPoolDickmanFloor : Real :=
  rho 5





/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/

/-- The real linear density retained in the raw broad pool. -/
def roughCanonicalRawBroadPoolDensity (W : Nat) : Real :=
  roughHeadDensity W * roughCanonicalPoolDickmanFloor / 16











/-! ## Uniform paper-scale choices -/













/-- Intrinsic version of the raw broad surplus.  It is stated for every
complete-rough label, before asking whether that label is already attained
by any lower candidate set. -/
def RoughCanonicalActiveIntrinsicRawBroadSurplus
    (W n h K budget poolMinimum : Nat) (deltaStar : Real) : Prop :=
  forall label, IsCompleteRoughLabel (yNat n) label ->
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      max poolMinimum
          (roughUpperCompleteRoughRowTarget n h (yNat n) label) + budget <=
        (roughCanonicalBroadCorrectionPool W n h K (yNat n) label).card









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperProposition87EndpointSelector -/
section


/-!
# Proposition 8.7 endpoint as an ambient natural-number selector

The bridge is carried out on a tagged active sample, whereas Section 9 uses
one weight function on natural-number coordinates.  This file performs the
finite push-forward exactly.  The ambient selector is the sum of

* every frozen tagged contribution, including a protected contribution on a
  coordinate which may also be active; and
* the endpoint active weight produced by Proposition 8.7.

Thus no disjointness between the protected and active layers is imposed.
The proofs below use only the literal Proposition 8.7 path output.  In
particular, they do not claim the separate complete-rough-row integrality or
outside-band target identities still needed by the Section 9 tangent input.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Backward-compatible literal-mass bridge data -/

/-- Canonical regular-mesh bridge data using the paper's unnormalized active
mass.  The old probability-baseline constructor remains available unchanged;
this is the variant which must be used at the literal Section 8 endpoint. -/
def bankPaperCanonicalActiveMassBridgeData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    BridgeData Head (Fin (M.cellCount + 1)) where
  sampleData := D
  baseline := T.activeMassBaseline q hq
  partition :=
    Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
  lowBand := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M
  referenceHead := referenceHead
  w := delta + eta
  w_pos := hw
  n_gt_one := hn

/-- The literal-mass constructor retains the supplied structured sample. -/
@[simp] theorem bankPaperCanonicalActiveMassBridgeData_sampleData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw).sampleData = D :=
  rfl

/-- The literal-mass constructor stores the scaled canonical allocation. -/
@[simp] theorem bankPaperCanonicalActiveMassBridgeData_baseline
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw).baseline =
        T.activeMassBaseline q hq :=
  rfl

/-- The bridge mass of the literal-mass constructor is the supplied `q_n`. -/
@[simp] theorem bankPaperCanonicalActiveMassBridgeData_q
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw).q = q := by
  exact BridgeData.q_eq_of_baseline_eq_activeMassBaseline
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw)
    T q hq rfl

/-! ## Push-forward to natural-number coordinates -/

/-- Finite natural-number support of the frozen and active tagged layers. -/
def bankPaperProposition87SelectorSupport
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    (B : BridgeData Head Band) (fixedValue : Fixed -> Nat) : Finset Nat :=
  Finset.univ.image fixedValue ∪
    Finset.univ.image B.sampleData.value

/-- The literal ambient selector at one point of the Proposition 8.7 path.
The addition is intentional: a protected frozen summand may occupy the same
clean coordinate as the active bridge. -/
def bankPaperProposition87SelectorAt
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) (t : Real) (a : Nat) : Real :=
  B.ambientCombinedWeight
    (BridgeData.frozenAmbientWeight fixedValue fixedWeight) (path t) a

/-- The natural-number selector at the fitted endpoint. -/
def bankPaperProposition87EndpointSelector
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) : Nat -> Real :=
  bankPaperProposition87SelectorAt B fixedValue fixedWeight path 1













/-! ## Literal marked residual at the pushed-forward endpoint -/

/-- The marked target after adjoining the frozen tagged contribution. -/
def bankPaperProposition87FullMarkedTarget
    {Fixed : Type*} [Fintype Fixed]
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (markedTarget : Nat -> Real) (p : Nat) : Real :=
  (∑ f : Fixed,
    fixedWeight f * ArithmeticModel.valuation p (fixedValue f)) +
      markedTarget p

/-- Target minus the full frozen-plus-active endpoint moment, written on
the actual finite natural-number support. -/
def bankPaperProposition87FullMarkedResidual
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (markedTarget : Nat -> Real)
    (path : Real -> B.ParamSpace) (p : Nat) : Real :=
  bankPaperProposition87FullMarkedTarget
      fixedValue fixedWeight markedTarget p -
    ∑ a ∈ bankPaperProposition87SelectorSupport B fixedValue,
      bankPaperProposition87EndpointSelector
        B fixedValue fixedWeight path a * ArithmeticModel.valuation p a







/-! ## Direct extraction from the literal Proposition 8.7 conclusion -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentFlowAlgebra -/
section


/-!
# Exact algebra of the tangent flow

A tangent request replaces weight at `t * a` by the same weight at `s * a`.
This file defines the simultaneous finite update on actual natural-number
coordinates and proves its exact linear invariants.  In particular, the full
valuation of the common multiplier cancels; no squarefreeness or coprimality
assumption on that multiplier is needed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Real point mass at one natural-number coordinate. -/
def tangentPointMass (b a : ℕ) : ℝ :=
  if a = b then 1 else 0

/-- The signed coordinate change made by finitely many directed requests. -/
def tangentDelta {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (a : ℕ) : ℝ :=
  ∑ e ∈ requests, weight e *
    (tangentPointMass (source e * multiplier e) a -
      tangentPointMass (target e * multiplier e) a)

/-- Apply all tangent requests to a selector. -/
def tangentUpdate {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (a : ℕ) : ℝ :=
  x a + tangentDelta requests source target multiplier weight a





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentStarTransport -/
section


/-!
# Exact finite star transport for tangent residuals

A zero-sum residual on a finite vertex type is transported through one
chosen pivot.  Positive residual leaves its vertex for the pivot; negative
residual is supplied from the pivot.  The construction is literal,
nonnegative, supported on the star, and has exactly the requested
divergence.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Nonnegative directed star flow.  The diagonal test comes first so the
pivot loop is zero. -/
def tangentStarFlow {V : Type*} [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (source target : V) : ℝ :=
  if source = target then 0
  else if target = pivot then max (residual source) 0
  else if source = pivot then max (-residual target) 0
  else 0

/-- Outgoing mass minus incoming mass at one vertex. -/
def tangentFlowDivergence {V : Type*} [Fintype V]
    (flow : V → V → ℝ) (v : V) : ℝ :=
  (∑ w : V, flow v w) - ∑ w : V, flow w v

/-- Total directed traffic of a flow on a finite vertex type. -/
def tangentFlowTraffic {V : Type*} [Fintype V]
    (flow : V → V → ℝ) : ℝ :=
  ∑ source : V, ∑ target : V, flow source target

variable {V : Type*} [DecidableEq V]

/-! ## Pointwise support and sign -/



@[simp]
theorem tangentStarFlow_self
    (pivot : V) (residual : V → ℝ) (v : V) :
    tangentStarFlow pivot residual v v = 0 := by
  simp [tangentStarFlow]







/-! ## Exact outgoing and incoming sums -/

variable [Fintype V]















/-! ## Traffic -/





/-! ## Boundary identities consumed by `TangentFlowAlgebra` -/











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FiniteAsymmetricLocalLemma -/
section


/-!
# The finite asymmetric Lovasz local lemma

This file proves the standard finite asymmetric local lemma directly on a
probability space.  The dependency hypothesis is stated as the exact measure
factorization that the proof uses: a bad event is independent of every finite
intersection of complements indexed by non-neighbors.

The key theorem `finiteAsymmetricLocalLemma_conditionalBound` is the genuine
conditional-probability induction.  For every finite conditioning family not
containing `i`, it proves

`P(A i | all events in the family are avoided) <= x i`

in denominator-free form.  It does not assume this conditional estimate.
The final induction then gives the usual positive product lower bound for the
probability that all bad events are avoided.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The event that every bad event indexed by `s` is avoided. -/
def avoidEvents {I Omega : Type*} (A : I -> Set Omega) (s : Finset I) :
    Set Omega :=
  ⋂ i ∈ s, (A i)ᶜ

@[simp]
theorem avoidEvents_empty {I Omega : Type*} (A : I -> Set Omega) :
    avoidEvents A ∅ = Set.univ := by
  simp [avoidEvents]







/-!
## The conditional-probability induction

For a fixed event `i` and conditioning set `s`, split `s` into the neighbors
of `i` and the non-neighbors of `i`.  Independence removes the latter.  The
strong induction hypothesis is then applied successively while the neighbors
are inserted.  This proves the denominator lower bound required to cancel
the neighborhood product in the asymmetric-LLL hypothesis.
-/



/-!
## Product lower bound and the local lemma
-/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentRequestSplitting -/
section


/-!
# Literal finite splitting of tangent-flow requests

This file formalizes only the algebra in the paper's request splitting.
It assumes concrete nonnegative edge masses and forms explicit `Fin k`
families of equal pieces.  It contains no flow-existence, list-capacity,
or collision-avoidance assertion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Number of requests used to split a nonnegative edge mass. -/
def tangentRequestCount (L sigma f : ℝ) : ℕ :=
  max 1 (Nat.ceil (4 * L * f / sigma))

/-- Common mass of every request obtained from the edge. -/
def tangentRequestPieceMass (L sigma f : ℝ) : ℝ :=
  f / tangentRequestCount L sigma f

@[simp] theorem tangentRequestCount_zero (L sigma : ℝ) :
    tangentRequestCount L sigma 0 = 1 := by
  simp [tangentRequestCount]

















/-- Actual request indices obtained by splitting every edge in a finite set.
For the literal paper support, the caller should take `edges` to consist
exactly of the strictly positive-flow edges; otherwise a zero-flow edge
contributes one harmless zero-mass request because of the totalized `max 1`
definition. -/
abbrev TangentSplitRequest {E : Type*} (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) :=
  Σ e : ↑edges, Fin (tangentRequestCount L sigma (flow e.1))

/-- Underlying directed support edge of a literal split request. -/
def tangentSplitRequestEdge {E : Type*} {edges : Finset E}
    {L sigma : ℝ} {flow : E → ℝ}
    (request : TangentSplitRequest edges L sigma flow) : E :=
  request.1.1

/-- Lift an edge-source label to every request split from that edge. -/
def tangentSplitRequestSource {E P : Type*} {edges : Finset E}
    {L sigma : ℝ} {flow : E → ℝ} (source : E → P) :
    TangentSplitRequest edges L sigma flow → P :=
  fun request ↦ source (tangentSplitRequestEdge request)

/-- Lift an edge-target label to every request split from that edge. -/
def tangentSplitRequestTarget {E P : Type*} {edges : Finset E}
    {L sigma : ℝ} {flow : E → ℝ} (target : E → P) :
    TangentSplitRequest edges L sigma flow → P :=
  fun request ↦ target (tangentSplitRequestEdge request)

/-- The actual finite set of all split requests. -/
def tangentSplitRequests {E : Type*} [DecidableEq E] (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) :
    Finset (TangentSplitRequest edges L sigma flow) :=
  Finset.univ

/-- Weight of one literal split request. -/
def tangentSplitRequestWeight {E : Type*} {edges : Finset E}
    {L sigma : ℝ} {flow : E → ℝ}
    (_request : TangentSplitRequest edges L sigma flow) : ℝ :=
  tangentRequestPieceMass L sigma (flow _request.1.1)









/-- Total number of split requests, as the literal sum of edge counts. -/
def tangentRequestTotal {E : Type*} (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) : ℕ :=
  ∑ e ∈ edges, tangentRequestCount L sigma (flow e)

theorem card_tangentSplitRequest
    {E : Type*} (edges : Finset E) (L sigma : ℝ) (flow : E → ℝ) :
    Fintype.card (TangentSplitRequest edges L sigma flow) =
      tangentRequestTotal edges L sigma flow := by
  classical
  unfold tangentRequestTotal
  simp only [TangentSplitRequest, Fintype.card_sigma, Fintype.card_fin]
  simpa using Finset.sum_attach edges
    (fun e ↦ tangentRequestCount L sigma (flow e))

@[simp] theorem card_tangentSplitRequests
    {E : Type*} [DecidableEq E] (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) :
    (tangentSplitRequests edges L sigma flow).card =
      tangentRequestTotal edges L sigma flow := by
  rw [tangentSplitRequests, Finset.card_univ]
  exact card_tangentSplitRequest edges L sigma flow









/-- The concrete support edges incident to one label. -/
def tangentIncidentEdges {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P) (p : P) : Finset E :=
  edges.filter fun e ↦ source e = p ∨ target e = p

def tangentIncidentRequestCount
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (p : P) : ℕ :=
  tangentRequestTotal (tangentIncidentEdges edges source target p)
    L sigma flow

def tangentIncidentFlowMass
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    (flow : E → ℝ) (p : P) : ℝ :=
  ∑ e ∈ tangentIncidentEdges edges source target p, flow e

def tangentSupportDegree
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P) (p : P) : ℕ :=
  (tangentIncidentEdges edges source target p).card



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCollisionFreeFeasibility -/
section


/-!
# Collision-free tangent updates and coordinate feasibility

The probabilistic part of the tangent construction is used only to produce
requests whose numerical endpoints are all distinct.  This file records the
deterministic consequence for the literal finite update: a used coordinate
receives exactly one signed request, and the paper's endpoint slack gives the
claimed post-move margin.

Importantly, `TangentEndpointsDistinct` below is an explicit input, not a
formalization of the paper's common-list estimate or local-lemma argument.
The final theorem connects that visible input to the actual split requests;
it does not claim to construct collision-free multipliers.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- All source endpoints are distinct, all target endpoints are distinct,
and no source endpoint equals any target endpoint. -/
structure TangentEndpointsDistinct {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) : Prop where
  source_injective : Set.InjOn
    (fun e ↦ source e * multiplier e) requests
  target_injective : Set.InjOn
    (fun e ↦ target e * multiplier e) requests
  source_ne_target : ∀ e ∈ requests, ∀ f ∈ requests,
    source e * multiplier e ≠ target f * multiplier f



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCollisionLocalLemma -/
section


/-!
# The finite collision experiment for tangent requests

This file instantiates the finite asymmetric local lemma with the literal
random experiment used in Section 9.  Every request independently chooses a
uniform element of its own nonempty finite multiplier list.  Bad events are
indexed by two-element sets of requests and say that the two resulting
two-element endpoint sets intersect.  Two bad events are declared dependent
exactly when their request supports intersect.

The paper-facing input is the per-request collision estimate

`sum_{E containing r} P(E) <= 1 / 8`.

It implies, inside this file, both `P(E) <= 1 / 8` and the factor-two
neighborhood estimate `sum_{F in Gamma(E)} P(F) <= 1 / 4`.  Thus the literal
choice `x_E = 2 * P(E)` satisfies the numerical local-lemma inequality via
`TangentLLLNumerics`.  Independence is not assumed: it is derived from the
finite product measure and disjoint coordinate supports.

The last theorem specializes the construction to the actual clean common
lists already defined in `TangentCommonMultiplierLists`.  The two remaining
paper inputs are deliberately visible there: nonemptiness of every clean list
and the `1 / 8` collision-mass estimate.  Those are the analytic common-list
cardinality and collision-count estimates, not another local-lemma premise.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos390.WholePaper

noncomputable section

/-! ## The finite product experiment -/

/-- The choices available to one request are the elements of its own finite
multiplier list.  Using the subtype makes list membership part of the sample
space rather than a conclusion that has to be recovered from a null-set
argument. -/
abbrev TangentMultiplierChoice {Request : Type*}
    (lists : Request → Finset ℕ) (request : Request) :=
  ↑(lists request)

/-- A complete outcome chooses one listed multiplier for every request. -/
abbrev TangentMultiplierOutcome {Request : Type*}
    (lists : Request → Finset ℕ) :=
  ∀ request, TangentMultiplierChoice lists request

/-- The product of the uniform measures on all request lists. -/
def tangentUniformMultiplierMeasure
    {Request : Type*} [Fintype Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty) :
    Measure (TangentMultiplierOutcome lists) := by
  letI : ∀ request, Nonempty (TangentMultiplierChoice lists request) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request)
  exact Measure.pi fun request ↦
    (PMF.uniformOfFintype
      (TangentMultiplierChoice lists request)).toMeasure





/-! ## Collision events and their supports -/

/-- Bad events are indexed by unordered two-element sets of requests. -/
abbrev TangentCollisionIndex (Request : Type*) :=
  {support : Finset Request // support.card = 2}

/-- The two numerical endpoints generated by one request. -/
def tangentRequestEndpointSet {Request : Type*}
    (source target : Request → ℕ) (multiplier : Request → ℕ)
    (request : Request) : Finset ℕ :=
  {source request * multiplier request,
    target request * multiplier request}

/-- Endpoint set for one coordinate of a restricted outcome. -/
def tangentRestrictedEndpointSet
    {Request : Type*} {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (support : Finset Request)
    (outcome : ∀ request : ↑support,
      TangentMultiplierChoice lists request.1)
    (request : ↑support) : Finset ℕ :=
  {source request.1 * (outcome request).1,
    target request.1 * (outcome request).1}

/-- A collision on a two-request support: the two endpoint sets intersect.
The existential form is convenient for restriction to coordinate cylinders
and is equivalent to one of the four endpoint equalities. -/
def tangentCollisionOn
    {Request : Type*} {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (outcome : ∀ request : ↑collision.1,
      TangentMultiplierChoice lists request.1) : Prop :=
  ∃ r s : ↑collision.1, r ≠ s ∧
    ¬Disjoint
      (tangentRestrictedEndpointSet source target collision.1 outcome r)
      (tangentRestrictedEndpointSet source target collision.1 outcome s)

/-- The collision cylinder in the full product sample space. -/
def tangentCollisionEvent
    {Request : Type*} {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) :
    Set (TangentMultiplierOutcome lists) :=
  {outcome | tangentCollisionOn source target collision
    (fun request ↦ outcome request.1)}

/-- Dependency neighborhood of a collision event.  Self-dependency is
excluded, and every other two-request event is adjacent exactly when the two
supports share a request. -/
def tangentCollisionNeighbors
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (collision : TangentCollisionIndex Request) :
    Finset (TangentCollisionIndex Request) :=
  Finset.univ.filter fun other ↦
    other ≠ collision ∧ ¬Disjoint collision.1 other.1

/-- All collision events incident to one fixed request. -/
def tangentIncidentCollisions
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (request : Request) : Finset (TangentCollisionIndex Request) :=
  Finset.univ.filter fun collision ↦ request ∈ collision.1

/-- The union of the request supports used by a finite family of collision
events. -/
def tangentCollisionSupportUnion
    {Request : Type*} [DecidableEq Request]
    (collisions : Finset (TangentCollisionIndex Request)) : Finset Request :=
  collisions.biUnion fun collision ↦ collision.1

theorem tangentCollisionSupport_subset_union
    {Request : Type*} [DecidableEq Request]
    {collisions : Finset (TangentCollisionIndex Request)}
    {collision : TangentCollisionIndex Request}
    (hcollision : collision ∈ collisions) :
    collision.1 ⊆ tangentCollisionSupportUnion collisions := by
  exact Finset.subset_biUnion_of_mem
    (fun event : TangentCollisionIndex Request ↦ event.1) hcollision

/-- Restrict an assignment on a larger finite coordinate set to a smaller
one. -/
def tangentRestrictMultiplierOutcome
    {Request : Type*} {lists : Request → Finset ℕ}
    {small large : Finset Request} (hsubset : small ⊆ large)
    (outcome : ∀ request : ↑large,
      TangentMultiplierChoice lists request.1) :
    ∀ request : ↑small, TangentMultiplierChoice lists request.1 :=
  fun request ↦ outcome ⟨request.1, hsubset request.2⟩

/-- Configurations on the union support which avoid every collision in a
finite family. -/
def tangentAvoidCollisionConfigurations
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collisions : Finset (TangentCollisionIndex Request)) :
    Set (∀ request : ↑(tangentCollisionSupportUnion collisions),
      TangentMultiplierChoice lists request.1) :=
  {outcome | ∀ collision, ∀ hcollision : collision ∈ collisions,
    ¬tangentCollisionOn source target collision
      (tangentRestrictMultiplierOutcome
        (tangentCollisionSupport_subset_union hcollision) outcome)}





/-! ## Product-space dependency factorization -/



/-! ## The literal `1/8`, factor-two, and factor-four bookkeeping -/

/-- Probability of one actual collision event in the uniform product
experiment. -/
def tangentCollisionProbability
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) : ℝ :=
  (tangentUniformMultiplierMeasure lists hlist).real
    (tangentCollisionEvent source target collision)

/-- Total collision probability incident to one request.  This is exactly
the quantity bounded by `B_coll` in Section 9. -/
def tangentRequestCollisionMass
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ) (request : Request) : ℝ :=
  ∑ collision ∈ tangentIncidentCollisions request,
    tangentCollisionProbability lists hlist source target collision











/-! ## The collision-free outcome -/







/-! ## Specialization to the literal clean common lists -/

/-- The actual request-indexed family of clean common lists from Section 9.
The list is indexed by the unordered label pair in paper order
`(max source target, min source target)`; the directed orientation remains
separate and is used only by the signed tangent update. -/
def tangentCleanMultiplierLists
    {Request : Type*}
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    Request → Finset ℕ :=
  fun request ↦ tangentCleanCommonMultiplierList
    n K h Phead X0 y
      (max (source request) (target request))
      (min (source request) (target request))
      dedicatedRows numericalGuards



/-! ## The literal split-request specialization -/

/-- Clean multiplier lists indexed by the actual `Fin`-split requests of the
tangent flow. -/
def tangentSplitCleanMultiplierLists
    {E : Type*} (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ)
    (n K h Phead X0 y : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    TangentSplitRequest edges L sigma flow → Finset ℕ :=
  tangentCleanMultiplierLists n K h Phead X0 y
    (tangentSplitRequestSource source)
    (tangentSplitRequestTarget target)
      dedicatedRows numericalGuards



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCollisionCounting -/
section


/-!
# Counting the tangent collision events

This file is the finite counting layer immediately before the local-lemma
module.  It does three things which are kept separate in the paper's prose.

* It proves that the product of the request-wise uniform laws is the uniform
  law on the finite dependent product.  Consequently an actual collision
  probability is exactly

  `number of colliding configurations / number of all configurations`.

* A two-request collision is covered by the four literal endpoint equations.
  For prime endpoint labels, the equation `p*a=q*b` has at most
  `N/p+1` solutions when `p=q`, and at most `N/(p*q)+1` solutions when
  `p != q`, provided the left endpoint is at most `N`.

* The incident-event sum for one request is reindexed exactly by all other
  requests.  A pairwise cardinality/counting estimate can therefore be
  summed using the two endpoint-label loads of the fixed request and the
  total request count.

No collision-free choice and no bound on a collision probability are assumed
here.  In the clean-list terminal the remaining inputs are request-wise list
cardinality lower bounds and an explicit arithmetic comparison of the finite
counting budget with the paper's shared-label and disjoint-label charges.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos390.WholePaper

noncomputable section

/-! ## The product law is uniform -/

/-- The uniform probability measure on an abstract nonempty finite type.
Keeping the carrier abstract here prevents later cardinality proofs from
unfolding the dependent request/list `Fintype` construction. -/
def tangentFiniteUniformMeasure (α : Type*) [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α]
    (hα : Nonempty α) : Measure α := by
  letI : Fintype α := Fintype.ofFinite α
  letI : Nonempty α := hα
  exact (PMF.uniformOfFintype α).toMeasure



/-- Uniform measure on the whole dependent product, with nonemptiness
installed from the request-wise list proofs. -/
def tangentUniformMultiplierOutcomeMeasure
    {Request : Type*} [Fintype Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty) :
    Measure (TangentMultiplierOutcome lists) := by
  letI : ∀ request, Nonempty (TangentMultiplierChoice lists request) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request)
  exact tangentFiniteUniformMeasure
    (TangentMultiplierOutcome lists) inferInstance

/-- Uniform measure on the dependent product over a finite request support. -/
def tangentUniformMultiplierRestrictionMeasure
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (support : Finset Request) :
    Measure (∀ request : ↑support,
      TangentMultiplierChoice lists request.1) :=
  tangentUniformMultiplierOutcomeMeasure (Request := ↑support)
    (fun request : ↑support ↦ lists request.1)
    (fun request : ↑support ↦ hlist request.1)







/-! ## Exact collision configurations -/

/-- All assignments on the two coordinates supporting one collision. -/
abbrev TangentCollisionConfiguration
    {Request : Type*} {lists : Request → Finset ℕ}
    (collision : TangentCollisionIndex Request) :=
  ∀ request : ↑collision.1,
    TangentMultiplierChoice lists request.1

/-- The colliding assignments on one two-request support. -/
def tangentCollisionConfigurations
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) :
    Finset (TangentCollisionConfiguration (lists := lists) collision) := by
  classical
  exact Finset.univ.filter fun outcome ↦
    tangentCollisionOn source target collision outcome

/-- Number of all assignments on a two-request support. -/
def tangentCollisionChoiceCount
    {Request : Type*} {lists : Request → Finset ℕ}
    (collision : TangentCollisionIndex Request) : ℕ :=
  ∏ request : ↑collision.1, (lists request.1).card



/-! ## Naming the two requests and the four endpoint equations -/

/-- Canonical first request on a two-element collision support. -/
def tangentCollisionFirstRequest
    {Request : Type*} (collision : TangentCollisionIndex Request) :
    ↑collision.1 :=
  (collision.1.equivFinOfCardEq collision.2).symm 0

/-- Canonical second request on a two-element collision support. -/
def tangentCollisionSecondRequest
    {Request : Type*} (collision : TangentCollisionIndex Request) :
    ↑collision.1 :=
  (collision.1.equivFinOfCardEq collision.2).symm 1









/-- Label selected by one endpoint side. -/
def tangentEndpointLabel
    {Request : Type*} (source target : Request → ℕ)
    (side : TangentEndpointSide) (request : Request) : ℕ :=
  match side with
  | .source => source request
  | .target => target request

/-- Numerical endpoint selected by a side in a restricted outcome. -/
def tangentRestrictedEndpointValue
    {Request : Type*} {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    {support : Finset Request}
    (outcome : ∀ request : ↑support,
      TangentMultiplierChoice lists request.1)
    (side : TangentEndpointSide) (request : ↑support) : ℕ :=
  tangentEndpointLabel source target side request.1 *
    (outcome request).1



/-- Configurations satisfying one specified endpoint equation. -/
def tangentEndpointEquationConfigurations
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (leftSide rightSide : TangentEndpointSide) :
    Finset (TangentCollisionConfiguration (lists := lists) collision) := by
  classical
  exact Finset.univ.filter fun outcome ↦
    tangentRestrictedEndpointValue source target outcome leftSide
        (tangentCollisionFirstRequest collision) =
      tangentRestrictedEndpointValue source target outcome rightSide
        (tangentCollisionSecondRequest collision)



/-! ## Raw solutions of `p*a=q*b` -/

/-- Pairs from two lists satisfying one endpoint equation. -/
def tangentEndpointEquationSolutions
    (leftList rightList : Finset ℕ) (leftLabel rightLabel : ℕ) :
    Finset (ℕ × ℕ) :=
  (leftList.product rightList).filter fun pair ↦
    leftLabel * pair.1 = rightLabel * pair.2









/-- Exact integer budget for one endpoint equation in the paper's two
cases: a shared label, or two distinct prime labels. -/
def tangentEndpointEquationBudget (N leftLabel rightLabel : ℕ) : ℕ :=
  if leftLabel = rightLabel then N / leftLabel + 1
  else N / (leftLabel * rightLabel) + 1



/-- Sum of the four literal endpoint-equation budgets for a collision. -/
def tangentCollisionEndpointBudget
    {Request : Type*} (N : ℕ) (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) : ℕ :=
  ∑ leftSide : TangentEndpointSide,
    ∑ rightSide : TangentEndpointSide,
      tangentEndpointEquationBudget N
        (tangentEndpointLabel source target leftSide
          (tangentCollisionFirstRequest collision).1)
        (tangentEndpointLabel source target rightSide
          (tangentCollisionSecondRequest collision).1)

/-- The same four-equation budget written for an ordered pair of requests. -/
def tangentOrderedPairEndpointBudget
    {Request : Type*} (N : ℕ) (source target : Request → ℕ)
    (left right : Request) : ℕ :=
  ∑ leftSide : TangentEndpointSide,
    ∑ rightSide : TangentEndpointSide,
      tangentEndpointEquationBudget N
        (tangentEndpointLabel source target leftSide left)
        (tangentEndpointLabel source target rightSide right)







/-! ## From list cardinalities to pair probabilities -/

/-- Product of request-wise lower cardinalities on a collision support. -/
def tangentCollisionLowerChoiceCount
    {Request : Type*} (lowerCard : Request → ℕ)
    (collision : TangentCollisionIndex Request) : ℕ :=
  ∏ request : ↑collision.1, lowerCard request.1







/-! ## Exact reindexing of an incident-event sum -/

/-- Erasing one member from a two-element collision support leaves a
nonempty singleton. -/
 theorem tangentIncidentErase_nonempty
    {Request : Type*} [DecidableEq Request]
    {request : Request} {collision : TangentCollisionIndex Request}
    (hrequest : request ∈ collision.1) :
    (collision.1.erase request).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem hrequest, collision.2]
  norm_num

/-- The other request in a two-request support containing `request`.  It is
totalized by returning `request` when the incidence premise is false. -/
def tangentIncidentOtherRequest
    {Request : Type*} [DecidableEq Request]
    (request : Request) (collision : TangentCollisionIndex Request) :
    Request :=
  if hrequest : request ∈ collision.1 then
    (tangentIncidentErase_nonempty hrequest).choose
  else request







/-- Collision index attached to two distinct requests. -/
def tangentCollisionIndexOfDistinctRequests
    {Request : Type*} [DecidableEq Request]
    (left right : Request) (hne : left ≠ right) :
    TangentCollisionIndex Request :=
  ⟨{left, right}, Finset.card_pair hne⟩







/-- Totalized collision probability for an ordered pair of requests. -/
def tangentPairCollisionProbability
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ) (left right : Request) : ℝ :=
  if hne : left ≠ right then
    tangentCollisionProbability lists hlist source target
      (tangentCollisionIndexOfDistinctRequests left right hne)
  else 0



/-! ## Request loads and the literal `1/8` terminal -/





/-- Number of requests other than `anchor` incident to `label`. -/
def tangentOtherRequestLabelLoad
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (source target : Request → ℕ) (anchor : Request) (label : ℕ) : ℕ :=
  ((Finset.univ.erase anchor).filter
    (tangentRequestHasLabel source target label)).card

/-- Paper load `k_p`: number of all requests incident to label `p`. -/
def tangentRequestLabelLoad
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (source target : Request → ℕ) (label : ℕ) : ℕ :=
  (Finset.univ.filter
    (tangentRequestHasLabel source target label)).card

/-- Number of other requests. -/
def tangentOtherRequestCount
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (anchor : Request) : ℕ :=
  (Finset.univ.erase anchor).card

/-- Paper total request count `K_req`. -/
def tangentTotalRequestCount (Request : Type*) [Fintype Request] : ℕ :=
  Fintype.card Request













/-- Totalized version of the explicit endpoint-counting quotient for an
ordered pair. -/
def tangentPairEndpointBudgetQuotient
    {Request : Type*} [DecidableEq Request]
    (lowerCard : Request → ℕ) (N : ℕ)
    (source target : Request → ℕ) (left right : Request) : ℝ :=
  if _hne : left ≠ right then
    (tangentOrderedPairEndpointBudget N source target left right : ℝ) /
      (lowerCard left * lowerCard right)
  else 0





/-! ## Specialization to the actual clean common lists -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperSharpCensus -/
section


/-!
# Sharp census for the actual paper bank

The earlier all-marker budget bounded one ordinary core path by its starting
prime and consequently gave `O(yNat²)`.  The constructed path is much
shorter.  Its sources are routed through the literal geometric grid
`Q_j=4(4/3)^j`; every grid fiber has bounded congestion, and only
logarithmically many indices occur below `yNat`.

This file counts the actual sigma-type request family.  It first records the
exact weighted path ledger

`|ordinary requests| = 2 ∑_{p≤y} β_p |coreSources(p)|`,

then bounds every path by an explicit logarithmic grid budget.  Combining
this finite count with the already proved `O(yNat)` beta demand gives the
paper-sized `O(yNat * L)` marker budget.  The only prime-counting input is
the existing audited theorem `bankBottomPaperDemand_isBigO_yNat`, whose
proof uses the safe PNT; no new counting hypothesis is introduced here.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Exact ordinary request ledger -/

/-- The unsigned weighted number of nonterminal ordinary path edges.  The
factor two for the two orientations is deliberately kept outside. -/
def bankOrdinaryWeightedPathDemand (n : ℕ) : ℕ :=
  ∑ p ∈ bankRoundingPrimeSupport n,
    bankRoundingBeta n p * (bankOrdinaryCoreSources p).card



/-! ## A literal logarithmic path budget -/



/-- The sharp literal path budget supplied by the constructed grid census.
The complete small-table segment has at most `17` sources in total.  Above
it, precisely the possible indices `6,...,scaleIndex(yNat)` remain, with at
most two sources at each index. -/
def bankOrdinaryPathComponentBudget (n : ℕ) : ℕ :=
  17 + 2 * (bankOrdinaryScaleIndex (yNat n) - 5)













/-! ## The full actual marker/component census -/

/-- Literal sharp realization-independent budget for all ordinary and
bottom marker components. -/
def bankPaperSharpMarkerBudget (n : ℕ) : ℕ :=
  bankBottomPaperDemand n *
    (2 * bankOrdinaryPathComponentBudget n + 8)





namespace BankPaperRealization





end BankPaperRealization

/-! ## The paper-sized `O(yL)` asymptotic -/









/-! ## Sharp numerical-guard corollaries -/

namespace BankPaperRealization









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentSplitRequestLoads -/
section


/-!
# Actual request loads for the split tangent flow

This file instantiates the abstract collision-counting loads on the literal
request type

`Sigma e : edges, Fin (max 1 (ceil (4 * L * flow e / sigma)))`.

There are no request-count or collision-mass hypotheses below.  The total
load `K_req` is identified with the sum of the edge splitting counts, and
the label load `k_p` is identified with the same sum restricted to edges
incident to `p`.  The ceiling estimates then express both loads in terms of
the actual total/incident flow masses and support census.

The last layer substitutes those proved loads into
`tangentRequestCollisionMass_le_fullLoadBudget`.  It is deliberately
normalized in the paper's form

`K_req / n`, `p * k_p / n`.

For the actual paper guard set, the sharp bank census is recorded alongside
this load calculation.  The only list input retained by the collision
terminal is the exact request-wise cardinality lower bound; no analytic
density estimate is hidden here.

The paper-specialized terminals deliberately retain the following separate
mathematical inputs.  The sharp finite-deletion ledger does **not** itself
prove them.

* `hlowerPos` and `hlower`: a positive exact lower bound for every clean
  request list;
* `hpairArithmetic`: the explicit four-equation quotient comparison with
  the chosen shared/disjoint charges;
* either the literal flow-budget inequality, or proved total-traffic,
  incident-traffic, and support censuses;
* the final displayed flow/census budget inequality `≤ 1/8`.

Thus this module derives request loads from those flow censuses and passes
them to the proved counting/LLL terminal, but does not claim the still
missing analytic list density, earthmover census, or final parameter
arithmetic.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Exact reindexing of split requests -/

/-- Restricting split requests to those incident to one label is equivalent
to first restricting the edge finset and then splitting every retained
edge. -/
def tangentIncidentSplitRequestEquiv
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ) (label : ℕ) :
    {request : TangentSplitRequest edges L sigma flow //
      tangentRequestHasLabel
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) label request} ≃
      TangentSplitRequest
        (tangentIncidentEdges edges source target label) L sigma flow where
  toFun request :=
    ⟨⟨request.1.1.1, Finset.mem_filter.mpr
      ⟨request.1.1.2, by
        simpa only [tangentRequestHasLabel, tangentSplitRequestSource,
          tangentSplitRequestTarget, tangentSplitRequestEdge] using
            request.2⟩⟩, request.1.2⟩
  invFun request :=
    ⟨⟨⟨request.1.1, (Finset.mem_filter.mp request.1.2).1⟩,
        request.2⟩,
      by
        simpa only [tangentRequestHasLabel, tangentSplitRequestSource,
          tangentSplitRequestTarget, tangentSplitRequestEdge] using
            (Finset.mem_filter.mp request.1.2).2⟩
  left_inv request := by
    rcases request with ⟨⟨⟨edge, hedge⟩, index⟩, hlabel⟩
    rfl
  right_inv request := by
    rcases request with ⟨⟨edge, hedge⟩, index⟩
    rfl









/-! ## The literal strictly-positive flow support -/

/-- Paper convention for the directed support: exactly the edges carrying
strictly positive flow. -/
def tangentPositiveFlowEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V → V → ℝ) : Finset (V × V) :=
  Finset.univ.filter fun edge ↦ 0 < flow edge.1 edge.2

/-- Membership in the positive-flow support is exactly strict positivity of
the corresponding directed edge flow. -/
@[simp]
theorem mem_tangentPositiveFlowEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {flow : V → V → ℝ} {edge : V × V} :
    edge ∈ tangentPositiveFlowEdges flow ↔ 0 < flow edge.1 edge.2 := by
  simp [tangentPositiveFlowEdges]



/-! ## The actual total and incident request upper bounds -/

/-- Real upper ledger for the total number of split requests. -/
def tangentSplitTotalRequestUpper
    {E : Type*} (edges : Finset E) (L sigma : ℝ) (flow : E → ℝ) : ℝ :=
  (4 * L / sigma) * (∑ edge ∈ edges, flow edge) + edges.card

/-- Real upper ledger for the number of split requests incident to one
label. -/
def tangentSplitLabelRequestUpper
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (label : P) : ℝ :=
  (4 * L / sigma) *
      tangentIncidentFlowMass edges source target flow label +
    tangentSupportDegree edges source target label











/-! ## Paper normalization `K_req/n` and `p*k_p/n` -/

/-- Proved upper ledger for `K_req/n`. -/
def tangentSplitNormalizedTotalRequestUpper
    {E : Type*} (n : ℕ) (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) : ℝ :=
  tangentSplitTotalRequestUpper edges L sigma flow / n

/-- Proved upper ledger for `p*k_p/n`. -/
def tangentSplitNormalizedLabelRequestUpper
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ) (label : ℕ) : ℝ :=
  (label : ℝ) *
      tangentSplitLabelRequestUpper
        edges source target L sigma flow label / n





/-! ## Substitution of literal flow and support censuses -/

/-- Total request upper bound after substituting a proved traffic bound and
an edge-support census. -/
def tangentSplitCensusTotalRequestUpper
    (L sigma totalTraffic : ℝ) (supportCount : ℕ) : ℝ :=
  (4 * L / sigma) * totalTraffic + supportCount

/-- Label request upper bound after substituting a proved incident-traffic
bound and the global support census.  The global census is valid because an
incident support is a filter of the edge support. -/
def tangentSplitCensusLabelRequestUpper
    (L sigma : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount label : ℕ) : ℝ :=
  (4 * L / sigma) * incidentTraffic label + supportCount









/-! ## Substitution in the full collision-load budget -/

/-- The fully expanded flow-side budget for one split request.  The two
coefficients are the constants in the pair estimate

`P(E_rs) ≤ disjointCoefficient/n`

plus `sharedCoefficient*p/n` for each shared endpoint label `p`. -/
def tangentSplitNormalizedCollisionFlowBudget
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (request : TangentSplitRequest edges L sigma flow) : ℝ :=
  tangentSplitNormalizedTotalRequestUpper n edges L sigma flow *
      disjointCoefficient +
    tangentSplitNormalizedLabelRequestUpper
        n edges source target L sigma flow
          (tangentSplitRequestSource source request) *
      sharedCoefficient +
    tangentSplitNormalizedLabelRequestUpper
        n edges source target L sigma flow
          (tangentSplitRequestTarget target request) *
      sharedCoefficient

/-- Paper-normalized collision budget after substituting literal total
traffic, incident traffic, and support bounds. -/
def tangentSplitNormalizedCollisionCensusBudget
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {flow : E → ℝ}
    (L sigma totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (request : TangentSplitRequest edges L sigma flow) : ℝ :=
  (tangentSplitCensusTotalRequestUpper
      L sigma totalTraffic supportCount / n) * disjointCoefficient +
    (((tangentSplitRequestSource (P := ℕ) source request : ℕ) : ℝ) *
        tangentSplitCensusLabelRequestUpper L sigma incidentTraffic
          supportCount (tangentSplitRequestSource source request) / n) *
      sharedCoefficient +
    (((tangentSplitRequestTarget (P := ℕ) target request : ℕ) : ℝ) *
        tangentSplitCensusLabelRequestUpper L sigma incidentTraffic
          supportCount (tangentSplitRequestTarget target request) / n) *
      sharedCoefficient







/-! ## Exact clean-list counting plus the proved load ledger -/











/-! ## The actual sharp paper bank and row census -/

namespace BankPaperRealization







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPairArithmetic -/
section


/-!
# Finite arithmetic for tangent collision pairs

This file discharges the finite four-endpoint part of the
`hpairArithmetic` contract in `TangentSplitRequestLoads`.  It separates two
layers.

* Four per-equation bounds are assembled into the paper's one disjoint charge
  and two possible shared-label charges.  Distinct endpoints on the right
  request ensure that each left label can create at most one shared equation.
* A paper-scale specialization derives the per-equation bounds from a supplied
  effective list-density inequality

  `density * n <= lowerCard(request) * endpointLabel(request, side)`.

The specialization uses only `tangentBroadUpper n K h <= 2*n`, prime-label
positivity, and explicit hypotheses saying that every endpoint is at most a
cutoff whose first and second powers are at most `n`.  It yields the concrete
coefficients `12 / density^2` and `3 / density^2`.

No clean-list density estimate or cutoff asymptotic is proved here.  In a
paper application those are precisely the inputs needed to establish the
displayed effective-density and cutoff inequalities.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Coefficients and elementary endpoint budgets -/

/-- Disjoint-label coefficient obtained from four endpoint equations, the
broad factor `2`, and the integer-division `+1` loss. -/
def tangentDensityDisjointCoefficient (density : ℝ) : ℝ :=
  12 / density ^ 2

/-- Shared-label coefficient obtained from one matching endpoint equation. -/
def tangentDensitySharedCoefficient (density : ℝ) : ℝ :=
  3 / density ^ 2











/-! ## Assembly of four endpoint equations -/





/-! ## Effective-density bounds for one endpoint equation -/





/-! ## Paper-scale pair arithmetic -/





/-! ## The literal `1/8` coefficient arithmetic -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentStarSplitRequestBridge -/
section


/-!
# Star-transport bridge to the paper split-request terminal

The current post-Saias development does not yet expose one literal finite
type of medium-prime residual coordinates.  This file therefore keeps a
finite vertex type `V`, an injective prime-label map, and its zero-sum
residual explicit.  It does not assert selector or collision existence.

For those honest inputs, the already-proved star transport is restricted to
its strictly positive directed support.  The restriction preserves its
factorization boundary, has the prescribed residual divergence, has total
and every label-incident traffic bounded by the residual `ℓ¹` mass, and has
at most twice as many support edges as vertices.  These proved censuses are
then supplied to
`tangentPaperSplitEndpointsDistinct_of_normalizedCensusBudget`.

The final theorem leaves visible exactly the estimates that a literal
post-Saias instantiation must still provide: zero residual mass in the
chosen band, injective prime labels and their cutoff bounds, a sharp enough
per-label incident-traffic estimate, clean-list cardinality/density, and the
displayed residual-`ℓ¹` collision smallness.
No selector, local earthmover estimate, or collision-free multiplier is
fabricated outside the existing terminal.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal positive star support and its census quantities -/

/-- Strictly positive directed edges of the star transport. -/
def tangentStarPositiveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) : Finset (V × V) :=
  tangentPositiveFlowEdges (tangentStarFlow pivot residual)

/-- Natural-number source label on a star edge. -/
def tangentStarEdgeSource
    {V : Type*} (label : V → ℕ) (edge : V × V) : ℕ :=
  label edge.1

/-- Natural-number target label on a star edge. -/
def tangentStarEdgeTarget
    {V : Type*} (label : V → ℕ) (edge : V × V) : ℕ :=
  label edge.2

/-- Actual mass carried by one directed star edge. -/
def tangentStarEdgeFlow
    {V : Type*} [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (edge : V × V) : ℝ :=
  tangentStarFlow pivot residual edge.1 edge.2









/-- Membership in the positive star support is equivalent to strict positivity
of the corresponding star-edge flow. -/
@[simp]
theorem mem_tangentStarPositiveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {pivot : V} {residual : V → ℝ} {edge : V × V} :
    edge ∈ tangentStarPositiveEdges pivot residual ↔
      0 < tangentStarEdgeFlow pivot residual edge := by
  simp [tangentStarPositiveEdges, tangentStarEdgeFlow]















/-! ## Boundary preservation through positive support and request splitting -/







/-! ## Conditional paper connector -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge -/
section


/-!
# Literal canonical residual for the selector-to-tangent handoff

The canonical Saias reduction currently stops at a selector continuation: it
does not yet construct the pre-tangent rounded selector.  This file removes
the *generic residual* ambiguity without asserting that missing construction.

For a supplied selector `x`, the residual coordinate at a medium prime is
defined literally as

`valuation(selectorTailTarget) - valuation(x)`.

The two remaining selector inputs are named explicitly.  The post-rounding
prime-band balance says that these coordinates sum to zero, while prime-band
support says that the selector already has the target valuation at every
prime outside the band.  Neither fact follows merely from
`roughCanonicalRawRowQuotaError`: that quantity is a complete-rough row quota
error, not a prime-coordinate valuation identity.

From those inputs, the finite prime residual has zero total mass and its
positive star split requests have exactly the valuation deficit required by
`tangentUpdate_valuation_eq_target`.  The final theorem also retains the
all-row integrality input verbatim.  It does not claim that clean common
multipliers, feasibility of the tangent update, or the selector itself have
already been constructed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal selector deficit and its finite prime domain -/

/-- The actual finite vertex type used by the canonical tangent star: the
natural primes in the paper band `W < p <= yNat n`. -/
abbrev BankPaperCanonicalTangentPrime (n W : ℕ) :=
  ↥(primeBand n W)

/-- The natural-number label of a canonical tangent vertex. -/
def bankPaperCanonicalTangentPrimeLabel
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) : ℕ :=
  p.1

/-- The literal valuation still missing from a supplied selector: target
valuation minus its current weighted valuation. -/
def bankPaperCanonicalSelectorValuationDeficit
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) (q : ℕ) : ℝ :=
  ((certificate.selectorTailTarget R fixed).factorization q : ℝ) -
    ∑ a ∈ candidates, x a * (a.factorization q : ℝ)

/-- Restriction of the literal selector deficit to the finite medium-prime
vertex type consumed by the star transport. -/
def bankPaperCanonicalTangentResidual
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (p : BankPaperCanonicalTangentPrime n W) : ℝ :=
  bankPaperCanonicalSelectorValuationDeficit
    R certificate fixed candidates x p.1

/-- Exact post-rounding balance needed from the missing selector stage.  It
is deliberately an input proposition, not a consequence attributed to the
analytic complete-rough row quota error. -/
def BankPaperCanonicalPostRoundingPrimeBandBalance
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) : Prop :=
  ∑ p ∈ primeBand n W,
      bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates x p = 0

/-- Outside the tangent prime band, a prime valuation must already agree
with the residual selector target.  Non-prime coordinates vanish
automatically and therefore are not included in this premise. -/
def BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ q, q.Prime → q ∉ primeBand n W →
    bankPaperCanonicalSelectorValuationDeficit
      R certificate fixed candidates x q = 0

/-- Literal all-complete-rough-row integrality input expected from the
rounded selector. -/
def BankPaperCanonicalSelectorRowIntegral
    (n : ℕ) (candidates : Finset ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ label ∈ completeRoughLabelSet (yNat n) candidates,
    ∃ k : ℤ,
      ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
        x a = (k : ℝ)

/-! ## Prime-label geometry and exact residual algebra -/















/-! ## Instantiation of the star split-request boundary -/





end

end Erdos390.WholePaper

end


