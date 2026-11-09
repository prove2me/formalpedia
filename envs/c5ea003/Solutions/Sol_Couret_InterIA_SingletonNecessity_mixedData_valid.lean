-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.mixedData_valid
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:13:07.128288+00:00
-- url     : https://prove2.me/submissions/3b819d56-d79a-495a-8560-8d59e5c47c9e

import Definitions.Def_Couret_MatchingCertificateData_656be71337d8
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk0_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk10_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk11_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk12_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk13_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk14_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk15_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk16_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk17_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk18_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk19_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk1_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk20_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk21_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk22_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk23_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk24_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk25_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk26_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk27_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk28_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk29_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk2_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk30_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk31_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk32_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk33_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk34_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk35_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk36_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk37_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk38_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk39_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk3_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk40_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk41_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk42_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk43_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk44_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk45_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk46_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk47_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk48_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk49_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk4_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk50_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk51_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk52_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk53_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk54_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk55_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk56_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk57_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk58_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk59_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk5_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk60_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk61_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk62_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk63_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk64_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk65_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk66_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk67_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk68_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk69_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk6_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk70_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk71_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk72_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk73_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk74_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk75_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk76_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk77_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk78_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk7_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk8_valid
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk9_valid
import Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874

set_option autoImplicit false

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

namespace Couret.InterIA.SingletonNecessity























































































































































































































































































































































































theorem p2m_local_mixedData_valid : mixedData.all (valid true) = true := by

  simp only [mixedData, List.all_flatten, List.all_cons, List.all_nil, mixedChunk0_valid, mixedChunk1_valid, mixedChunk2_valid, mixedChunk3_valid, mixedChunk4_valid, mixedChunk5_valid, mixedChunk6_valid, mixedChunk7_valid, mixedChunk8_valid, mixedChunk9_valid, mixedChunk10_valid, mixedChunk11_valid, mixedChunk12_valid, mixedChunk13_valid, mixedChunk14_valid, mixedChunk15_valid, mixedChunk16_valid, mixedChunk17_valid, mixedChunk18_valid, mixedChunk19_valid, mixedChunk20_valid, mixedChunk21_valid, mixedChunk22_valid, mixedChunk23_valid, mixedChunk24_valid, mixedChunk25_valid, mixedChunk26_valid, mixedChunk27_valid, mixedChunk28_valid, mixedChunk29_valid, mixedChunk30_valid, mixedChunk31_valid, mixedChunk32_valid, mixedChunk33_valid, mixedChunk34_valid, mixedChunk35_valid, mixedChunk36_valid, mixedChunk37_valid, mixedChunk38_valid, mixedChunk39_valid, mixedChunk40_valid, mixedChunk41_valid, mixedChunk42_valid, mixedChunk43_valid, mixedChunk44_valid, mixedChunk45_valid, mixedChunk46_valid, mixedChunk47_valid, mixedChunk48_valid, mixedChunk49_valid, mixedChunk50_valid, mixedChunk51_valid, mixedChunk52_valid, mixedChunk53_valid, mixedChunk54_valid, mixedChunk55_valid, mixedChunk56_valid, mixedChunk57_valid, mixedChunk58_valid, mixedChunk59_valid, mixedChunk60_valid, mixedChunk61_valid, mixedChunk62_valid, mixedChunk63_valid, mixedChunk64_valid, mixedChunk65_valid, mixedChunk66_valid, mixedChunk67_valid, mixedChunk68_valid, mixedChunk69_valid, mixedChunk70_valid, mixedChunk71_valid, mixedChunk72_valid, mixedChunk73_valid, mixedChunk74_valid, mixedChunk75_valid, mixedChunk76_valid, mixedChunk77_valid, mixedChunk78_valid, Bool.and_self]

end Couret.InterIA.SingletonNecessity
































































































theorem solution : @Eq.{1} Bool
  (@List.all.{0} Couret.InterIA.SingletonNecessity.Certificate Couret.InterIA.SingletonNecessity.mixedData
    (Couret.InterIA.SingletonNecessity.valid Bool.true))
  Bool.true := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_mixedData_valid

