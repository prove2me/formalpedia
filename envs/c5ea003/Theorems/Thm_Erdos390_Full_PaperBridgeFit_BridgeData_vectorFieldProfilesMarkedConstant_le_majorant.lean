-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_vectorFieldProfilesMarkedConstant_le_majorant
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.vectorFieldProfilesMarkedConstant_le_majorant
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:19:48.230841+00:00
-- url     : https://prove2.me/theorems/aa966a27-7419-461a-adbd-ccb400281f1d
-- title:
--   Deterministic majorant for the marked vector-field constant
-- statement:
--   For bridge data with W>1, assume H,K≥0; 0≤Eprofile≤1 and Eprofile H≤1; CF,Cprod,CKernel≥0; 0≤R≤Rmax; 0≤Cmarked≤1 and Cmarked H≤1; 0<γfloor≤γnuisance; CinvOrd,Tband,Tslow,Creg≥0 and Vlower>0. Then the source-defined marked vector-field profile constant is bounded by the majorant that replaces the varying error factors and nuisance gap by these fixed bounds. This is a deterministic inequality with no limiting hypothesis.
--
--   $$\operatorname{vectorFieldProfilesMarkedConstant}(H,K,E_{\rm profile},C_F,C_{\rm prod},C_{\rm Kernel},R,C_{\rm marked},\gamma_{\rm nuisance},C_{\rm invOrd},T_{\rm band},T_{\rm slow},V_{\rm lower},C_{\rm reg})\le\operatorname{vectorFieldProfilesMarkedMajorant}(K,C_F,C_{\rm prod},C_{\rm Kernel},R_{\max},\gamma_{\rm floor},C_{\rm invOrd},T_{\rm band},T_{\rm slow},V_{\rm lower},C_{\rm reg}).$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperProposition87MarkedProfilesMajorant.lean#L45-L224

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.vectorFieldProfilesMarkedConstant_le_majorant :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  {H K Eprofile CF Cprod CKernel R Rmax Cmarked gammaNuisance gammaFloor CinvOrd Tband Tslow Vlower Creg : Real},
  LE.le.{0} (0 : Real) H →
    LE.le.{0} (0 : Real) K →
      LE.le.{0} (0 : Real) Eprofile →
        LE.le.{0} Eprofile (1 : Real) →
          LE.le.{0} (HMul.hMul.{0, 0, 0} Eprofile H) (1 : Real) →
            LE.le.{0} (0 : Real) CF →
              LE.le.{0} (0 : Real) Cprod →
                LE.le.{0} (0 : Real) CKernel →
                  LE.le.{0} (0 : Real) R →
                    LE.le.{0} R Rmax →
                      LE.le.{0} (0 : Real) Cmarked →
                        LE.le.{0} Cmarked (1 : Real) →
                          LE.le.{0} (HMul.hMul.{0, 0, 0} Cmarked H) (1 : Real) →
                            LT.lt.{0} (0 : Real) gammaFloor →
                              LT.lt.{0} (0 : Real) gammaNuisance →
                                LE.le.{0} gammaFloor gammaNuisance →
                                  LE.le.{0} (0 : Real) CinvOrd →
                                    LE.le.{0} (0 : Real) Tband →
                                      LE.le.{0} (0 : Real) Tslow →
                                        LT.lt.{0} (0 : Real) Vlower →
                                          LE.le.{0} (0 : Real) Creg →
                                            LT.lt.{0} (1 : Nat)
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                                              LE.le.{0}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFieldProfilesMarkedConstant.{u_1,
                                                    u_2}
                                                  B H K Eprofile CF Cprod CKernel R Cmarked gammaNuisance CinvOrd Tband
                                                  Tslow Vlower Creg)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFieldProfilesMarkedMajorant.{u_1,
                                                    u_2}
                                                  B K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband Tslow Vlower Creg) := by sorry
