-- Prove2me | Definitions.Def_erdos390_remaining_analytic_propositions_004
-- name    : erdos390_remaining_analytic_propositions_004
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T16:27:05.740841+00:00
-- url     : https://prove2.me/theorems/4207cbbc-a818-4419-90ae-7a6fe6a42a9a
-- title:
--   Analytic construction propositions, part 4
-- statement:
--   Named propositions for the remaining analytic and finite construction estimates in the Erdős 390 central-anchor proof. Each name expands to the complete quantified statement, including every hypothesis and universe parameter. These definitions introduce no assertion of the propositions; their proofs are submitted separately. This part includes the following source declarations: forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference, exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall, exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted, exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted, exists_uniform_movingPrefix_divInd_centered_bound, exists_uniform_rawCell_valuation_prefix_bound, exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted, exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate, bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial, bankPaperCanonicalBalancedRawSmoothRowDiscrepancy_isBigO, bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack, bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput, eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs, eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget, eventually_canonicalDistributedSectionNineCleanListLower_absorbed, eventually_roughCanonicalBalancedNonsmoothBounds, eventually_roughCanonicalUniformGuardedPostchargeCorrectionDensityBound, eventually_roughCanonicalUniformRawRowCorrectionDensityBound, exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion, exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_final_payload_cutoff_certificates
import Definitions.Def_erdos390_source_bank_interface
import Mathlib
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_MediumPNT
universe u_1 u_2
set_option maxRecDepth 10000
set_option maxHeartbeats 0

noncomputable def Erdos390.RemainingAnalyticGoal004_001 : Prop :=
∀ (r : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
    @Exists.{1} Nat fun (W₀ : Nat) =>
      ∀ (W : Nat),
        @LE.le.{0} Nat instLENat W₀ W →
          ∀ {delta eta : Real}
            (hdelta :
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                delta)
            (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {Head : Type u_1} [inst : Fintype.{u_1} Head]
            [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head]
            (Phead : Head → Erdos390.Full.HeadPattern.Pattern),
            (∀ (h : Head) (p : Nat),
                Iff
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Phead h).primes
                    p)
                  (And (Nat.Prime p) (@LE.le.{0} Nat instLENat p W))) →
              ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real),
                (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (I.lower sigma)) →
                  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                      @LE.le.{0} Real Real.instLE (I.upper sigma) Cmax) →
                    ∀ (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank)
                      (Acoef Aphys : Real),
                      @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Acoef →
                        @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Aphys →
                          @Filter.Eventually.{0} Nat
                            (fun (n : Nat) =>
                              ∀
                                (B :
                                  @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    inst inst_1
                                    (Fin.fintype
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (instDecidableEqFin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
                                @Eq.{1} Nat
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        inst inst_1
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (instDecidableEqFin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        B))
                                    n →
                                  @Eq.{1} Nat
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          inst inst_1
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          B))
                                      W →
                                    ∀
                                      (hsep :
                                        @LT.lt.{0} Nat instLTNat
                                          (Erdos390.Full.ArithmeticModel.physicalBound
                                            (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                inst inst_1
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                B)))
                                          (Erdos390.Full.ArithmeticModel.physicalBound
                                            (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                inst inst_1
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                B))))
                                      (hremaining :
                                        ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                          @Finset.Nonempty.{0} Nat
                                            (@SDiff.sdiff.{0} (Finset.{0} Nat)
                                              (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head Phead I
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    inst inst_1
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    B))
                                                c)
                                              (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    inst inst_1
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    B))
                                                Cprom Cbank
                                                (ledger
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      inst inst_1
                                                      (Fin.fintype
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (instDecidableEqFin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      B)))))),
                                      @Eq.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head inst)
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            inst inst_1
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            B)
                                          (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Head inst Phead I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                inst inst_1
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                inst inst_1
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                B))
                                            Cprom Cbank
                                            (ledger
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  inst inst_1
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (instDecidableEqFin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  B)))
                                            hsep hremaining) →
                                        (@Exists.{0}
                                            (@Ne.{1} Nat
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  inst inst_1
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (instDecidableEqFin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  B))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                            fun
                                              (hWne :
                                                @Ne.{1} Nat
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      inst inst_1
                                                      (Fin.fintype
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (instDecidableEqFin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      B))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                                            @Exists.{0}
                                              (@Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    inst inst_1
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    inst inst_1
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    B)))
                                              fun
                                                (S :
                                                  @Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head
                                                      inst
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                        (Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        inst inst_1
                                                        (Fin.fintype
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        (instDecidableEqFin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        B))
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head
                                                      inst
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                        (Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        inst inst_1
                                                        (Fin.fintype
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        (instDecidableEqFin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        B))) =>
                                              @Eq.{1}
                                                (@Erdos390.Full.ArithmeticBandGeometry.Partition.{0}
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      inst inst_1
                                                      (Fin.fintype
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (instDecidableEqFin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      B))
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      inst inst_1
                                                      (Fin.fintype
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (instDecidableEqFin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      B))
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} Head
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  inst inst_1
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (instDecidableEqFin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  B)
                                                (@Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta
                                                  eta M
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      inst inst_1
                                                      (Fin.fintype
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (instDecidableEqFin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      B))
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} Head
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      inst inst_1
                                                      (Fin.fintype
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (instDecidableEqFin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      B))
                                                  hdelta
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} Head
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    inst inst_1
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    B)
                                                  hWne S)) →
                                          @Eq.{1} Real
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} Head
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                inst inst_1
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                B)
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                delta eta) →
                                            ∀
                                              (xi :
                                                @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} Head
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  inst inst_1
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (instDecidableEqFin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  B),
                                              (∀
                                                  (p :
                                                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head
                                                        inst
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                          Head
                                                          (Fin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          inst inst_1
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          B))
                                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head
                                                        inst
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                          Head
                                                          (Fin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          inst inst_1
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          B))),
                                                  @LE.le.{0} Real Real.instLE
                                                    (@abs.{0} Real Real.lattice Real.instAddGroup
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1,
                                                            0}
                                                        Head
                                                        (Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        inst inst_1
                                                        (Fin.fintype
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        (instDecidableEqFin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        B xi p))
                                                    Acoef) →
                                                @LE.le.{0}
                                                    ((fun
                                                          (x :
                                                            @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, 0} Head
                                                              (Fin
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              inst inst_1
                                                              (Fin.fintype
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              (instDecidableEqFin
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              B) =>
                                                        Real)
                                                      (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{0, u_1}
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, 0}
                                                          Head
                                                          (Fin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          inst inst_1
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          B)
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, 0}
                                                          Head
                                                          (Fin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          inst inst_1
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          B)))
                                                    Real.instLE
                                                    (@abs.{0}
                                                      ((fun
                                                            (x :
                                                              @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, 0}
                                                                Head
                                                                (Fin
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                      delta eta M)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1)))))
                                                                inst inst_1
                                                                (Fin.fintype
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                      delta eta M)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1)))))
                                                                (instDecidableEqFin
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                      delta eta M)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1)))))
                                                                B) =>
                                                          Real)
                                                        (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{0, u_1}
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, 0}
                                                            Head
                                                            (Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            inst inst_1
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            B)
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, 0}
                                                            Head
                                                            (Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            inst inst_1
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            B)))
                                                      Real.lattice Real.instAddGroup
                                                      (@WithLp.ofLp.{u_1}
                                                        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                                ENNReal.instAddCommMonoidWithOne))
                                                            (@Nat.instAtLeastTwoHAddOfNat
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))
                                                              (@Nat.instNeZeroSucc
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                  (instOfNatNat (nat_lit 0)))))))
                                                        ((i :
                                                            @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, 0} Head
                                                              (Fin
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              inst inst_1
                                                              (Fin.fintype
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              (instDecidableEqFin
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              B) →
                                                          (fun
                                                                (x :
                                                                  @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1,
                                                                        0}
                                                                    Head
                                                                    (Fin
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat)
                                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                          delta eta M)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                          (instOfNatNat (nat_lit 1)))))
                                                                    inst inst_1
                                                                    (Fin.fintype
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat)
                                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                          delta eta M)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                          (instOfNatNat (nat_lit 1)))))
                                                                    (instDecidableEqFin
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat)
                                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                          delta eta M)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                          (instOfNatNat (nat_lit 1)))))
                                                                    B) =>
                                                              Real)
                                                            i)
                                                        xi
                                                        (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{0, u_1}
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, 0}
                                                            Head
                                                            (Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            inst inst_1
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            B)
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, 0}
                                                            Head
                                                            (Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            inst inst_1
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            B))))
                                                    Aphys →
                                                  ∀
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))),
                                                    @LE.le.{0} Real Real.instLE
                                                      (@abs.{0} Real Real.lattice Real.instAddGroup
                                                        (@HSub.hSub.{0, 0, 0} Real Real Real
                                                          (@instHSub.{0} Real Real.instSub)
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.normalizedBandCovarianceRow.{u_1,
                                                                0}
                                                            Head
                                                            (Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            inst inst_1
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            B inst_2 xi
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.slowScore.{u_1, 0}
                                                              Head
                                                              (Fin
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              inst inst_1
                                                              (Fin.fintype
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              (instDecidableEqFin
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount
                                                                    delta eta M)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              B)
                                                            i)
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.referenceSlowRow.{u_1,
                                                                0}
                                                            Head
                                                            (Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            inst inst_1
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            B i)))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) r
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} Head
                                                            (Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            inst inst_1
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            B))
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0}
                                                          Head
                                                          (Fin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          inst inst_1
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          B i)))
                            (@Filter.atTop.{0} Nat Nat.instPreorder)

noncomputable def Erdos390.RemainingAnalyticGoal004_002 : Prop :=
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real), @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) U → (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) (I.lower sigma)) → (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Real _ (I.upper sigma) U) → ∀ (Cprom Cbank : Nat) (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W : Nat), @LT.lt.{0} Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 1) _) W → (∀ (h : Head) (p : Nat), @Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ (P h).primes p → @LE.le.{0} Nat _ p W) → ∀ (a : NNReal), @Exists.{1} (Nat → Real) fun (epsilon : Nat → Real) => And (∀ (n : Nat), @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) (epsilon n)) (And (@Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => @HMul.hMul.{0, 0, 0} Real Real Real _ (epsilon n) (Real.log (Erdos390.Full.Scale.L n))) (@Filter.atTop.{0} Nat _) (@nhds.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _))) (@Exists.{1} Nat fun (N₀ : Nat) => ∀ {Band : Type u_2} [inst_3 : Fintype.{u_2} Band] [inst_4 : DecidableEq.{u_2 + 1} Band] (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band _ _ _ _) (z : @Subtype.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) fun (x : @Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) => @Membership.mem.{u_1, u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) (@Submodule.{0, u_1} Real (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) _ _ _) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} Head Band _ _ _ _ B) x), @Membership.mem.{u_1, u_1} (@Subtype.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) fun (x : @Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) => @Membership.mem.{u_1, u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) (@Submodule.{0, u_1} Real (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) _ _ _) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} Head Band _ _ _ _ B) x) (Set.{u_1} (@Subtype.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) fun (x : @Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) => @Membership.mem.{u_1, u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) (@Submodule.{0, u_1} Real (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) _ _ _) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} Head Band _ _ _ _ B) x)) _ (@Metric.closedBall.{u_1} (@Subtype.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) fun (x : @Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) => @Membership.mem.{u_1, u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) (@Submodule.{0, u_1} Real (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) _ _ _) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} Head Band _ _ _ _ B) x) _ (@OfNat.ofNat.{u_1} (@Subtype.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) fun (x : @Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) => @Membership.mem.{u_1, u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) (@Submodule.{0, u_1} Real (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) _ _ _) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} Head Band _ _ _ _ B) x) (nat_lit 0) _) (↑a : Real)) z → @LE.le.{0} Nat _ N₀ (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) → @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) W → ∀ (hsep : @LT.lt.{0} Nat _ (Erdos390.Full.ArithmeticModel.physicalBound (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B))) (Erdos390.Full.ArithmeticModel.physicalBound (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)))) (hremaining : ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head), @Finset.Nonempty.{0} Nat (@SDiff.sdiff.{0} (Finset.{0} Nat) _ (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) c) (@Erdos390.Full.PaperGuardCensus.Ledger.guards (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) Cprom Cbank (G (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)))))), @Eq.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head _) (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B) (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Head _ P I (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) Cprom Cbank (G (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B))) hsep hremaining) → ∀ (c : Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band _ _ _ _ B)) (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B))), @LE.le.{0} Real _ (@abs.{0} Real _ _ (@Erdos390.Full.FiniteProbability.covariance.{u_1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} Head Band _ _ _ _ B _ (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, max (u_1 + 1) (u_2 + 1)} (@ContinuousLinearEquiv.{0, 0, u_1, max u_1 u_2} Real Real _ _ (@RingHom.id.{0} Real _) (@RingHom.id.{0} Real _) _ _ (@Subtype.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) fun (x : @Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) => @Membership.mem.{u_1, u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) (@Submodule.{0, u_1} Real (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) _ _ _) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} Head Band _ _ _ _ B) x) _ _ (@Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band _ _ _ _ B) _ _ _ _) (@Subtype.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) fun (x : @Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) => @Membership.mem.{u_1, u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) (@Submodule.{0, u_1} Real (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) _ _ _) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} Head Band _ _ _ _ B) x) (fun (x : @Subtype.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) fun (x : @Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) => @Membership.mem.{u_1, u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) (@Submodule.{0, u_1} Real (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveAmbient.{u_1, u_2} Head Band _ _ _ _ B) _ _ _) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} Head Band _ _ _ _ B) x) => @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band _ _ _ _ B) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} Head Band _ _ _ _ B) z)) (fun (m : @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) => @WithLp.ofLp.{u_1} (@OfNat.ofNat.{0} ENNReal (nat_lit 2) _) ((i : Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band _ _ _ _ B)) → (fun (x : Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1} (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band _ _ _ _ B)) => Real) i) (@Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1, u_2} Head Band _ _ _ _ B _ m) c) fun (m : @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) => Erdos390.Full.ArithmeticModel.valuation (@Subtype.val.{1} Nat (fun (p : Nat) => @Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ (Erdos390.Full.ArithmeticModel.primeBand (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B))) p) p) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B) m))) (@HMul.hMul.{0, 0, 0} Real Real Real _ (epsilon (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B))) (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) (@Nat.cast.{0} Real _ (@Subtype.val.{1} Nat (fun (p : Nat) => @Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ (Erdos390.Full.ArithmeticModel.primeBand (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band _ _ _ _ B))) p) p))))))

noncomputable def Erdos390.RemainingAnalyticGoal004_003 : Prop :=
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head]
  (P : Head → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals)
  (Cprom Cbank : Nat) (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) W →
    (∀ (h : Head) (q : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (P h).primes q →
          @LE.le.{0} Nat instLENat q W) →
      ∀ (Acoef : Real),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Acoef →
          @Exists.{1} (Nat → Real) fun (epsilon : Nat → Real) =>
            And
              (∀ (n : Nat),
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (epsilon n))
              (And
                (@Filter.Tendsto.{0, 0} Nat Real
                  (fun (n : Nat) =>
                    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (epsilon n)
                      (Real.log (Erdos390.Full.Scale.L n)))
                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                  (@nhds.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                (@Exists.{1} Nat fun (N₀ : Nat) =>
                  ∀ {Band : Type u_2} [inst_3 : Fintype.{u_2} Band] [inst_4 : DecidableEq.{u_2 + 1} Band]
                    (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band inst inst_1 inst_3 inst_4)
                    (xi :
                      @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band inst inst_1 inst_3 inst_4
                        B),
                    @LE.le.{0} Nat instLENat N₀
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_3
                            inst_4 B)) →
                      @Eq.{1} Nat
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_3
                              inst_4 B))
                          W →
                        (∀
                            (p :
                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_3 inst_4 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_3 inst_4 B))),
                            @LE.le.{0} Real Real.instLE
                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} Head Band
                                  inst inst_1 inst_3 inst_4 B xi p))
                              Acoef) →
                          ∀
                            (hsep :
                              @LT.lt.{0} Nat instLTNat
                                (Erdos390.Full.ArithmeticModel.physicalBound
                                  (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_3 inst_4 B)))
                                (Erdos390.Full.ArithmeticModel.physicalBound
                                  (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_3 inst_4 B))))
                            (hremaining :
                              ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                @Finset.Nonempty.{0} Nat
                                  (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                    (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B))
                                      c)
                                    (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B))
                                      Cprom Cbank
                                      (G
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_3 inst_4 B)))))),
                            @Eq.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head inst)
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_3 inst_4 B)
                                (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Head inst P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_3 inst_4 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_3 inst_4 B))
                                  Cprom Cbank
                                  (G
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_3 inst_4 B)))
                                  hsep hremaining) →
                              ∀
                                (p :
                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_3 inst_4 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_3 inst_4 B)))
                                (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (k : Nat),
                                @LE.le.{0} Real Real.instLE
                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                    (@Erdos390.Full.FiniteProbability.covariance.{0}
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B)
                                        c)
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleAtFintype.{u_1} Head
                                        inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B)
                                        c)
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} Head Band inst
                                        inst_1 inst_3 inst_4 B inst_2 xi c)
                                      (fun
                                          (m :
                                            @Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_3 inst_4 B)
                                              c) =>
                                        Erdos390.Full.ArithmeticModel.valuation
                                          (@Subtype.val.{1} Nat
                                            (fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                (Erdos390.Full.ArithmeticModel.primeBand
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                      Band inst inst_1 inst_3 inst_4 B))
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                      Band inst inst_1 inst_3 inst_4 B)))
                                                p)
                                            p)
                                          (@Subtype.val.{1} Nat
                                            (fun (m : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                                                  Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_3 inst_4 B)
                                                  c)
                                                m)
                                            m))
                                      fun
                                        (m :
                                          @Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_3 inst_4 B)
                                            c) =>
                                      @ite.{1} Real
                                        (@LE.le.{0} Nat instLENat
                                          (@Subtype.val.{1} Nat
                                            (fun (m : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                                                  Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_3 inst_4 B)
                                                  c)
                                                m)
                                            m)
                                          k)
                                        ((@Subtype.val.{1} Nat
                                              (fun (m : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                                                    Head inst
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                      Band inst inst_1 inst_3 inst_4 B)
                                                    c)
                                                  m)
                                              m).decLe
                                          k)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (epsilon
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B)))
                                    (@Nat.cast.{0} Real Real.instNatCast
                                      (@Subtype.val.{1} Nat
                                        (fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            (Erdos390.Full.ArithmeticModel.primeBand
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_3 inst_4 B))
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_3 inst_4 B)))
                                            p)
                                        p)))))

noncomputable def Erdos390.RemainingAnalyticGoal004_004 : Prop :=
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head]
  (P : Head → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals)
  (Cprom Cbank : Nat) (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) W →
    (∀ (h : Head) (p : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (P h).primes p →
          @LE.le.{0} Nat instLENat p W) →
      ∀ (Acoef : Real),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Acoef →
          @Exists.{1} Real fun (Aval : Real) =>
            And
              (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                Aval)
              (@Exists.{1} (Nat → Real) fun (epsilon : Nat → Real) =>
                And
                  (∀ (n : Nat),
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (epsilon n))
                  (And
                    (@Filter.Tendsto.{0, 0} Nat Real
                      (fun (n : Nat) =>
                        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (epsilon n)
                          (Real.log (Erdos390.Full.Scale.L n)))
                      (@Filter.atTop.{0} Nat Nat.instPreorder)
                      (@nhds.{0} Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                    (@Exists.{1} Nat fun (N₀ : Nat) =>
                      ∀ {Band : Type u_2} [inst_3 : Fintype.{u_2} Band] [inst_4 : DecidableEq.{u_2 + 1} Band]
                        (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band inst inst_1 inst_3 inst_4)
                        (xi :
                          @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band inst inst_1 inst_3
                            inst_4 B),
                        @LE.le.{0} Nat instLENat N₀
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_3 inst_4 B)) →
                          @Eq.{1} Nat
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_3 inst_4 B))
                              W →
                            (∀
                                (p :
                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_3 inst_4 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_3 inst_4 B))),
                                @LE.le.{0} Real Real.instLE
                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} Head
                                      Band inst inst_1 inst_3 inst_4 B xi p))
                                  Acoef) →
                              ∀
                                (hsep :
                                  @LT.lt.{0} Nat instLTNat
                                    (Erdos390.Full.ArithmeticModel.physicalBound
                                      (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B)))
                                    (Erdos390.Full.ArithmeticModel.physicalBound
                                      (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B))))
                                (hremaining :
                                  ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                    @Finset.Nonempty.{0} Nat
                                      (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_3 inst_4 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_3 inst_4 B))
                                          Cprom Cbank
                                          (G
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_3 inst_4 B)))))),
                                @Eq.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head inst)
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_3 inst_4 B)
                                    (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Head inst P I
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B))
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_3 inst_4 B))
                                      Cprom Cbank
                                      (G
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_3 inst_4 B)))
                                      hsep hremaining) →
                                  ∀
                                    (p :
                                      Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_3 inst_4 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_3 inst_4 B))),
                                    And
                                      (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                        @LE.le.{0} Real Real.instLE
                                          (@Erdos390.Full.FiniteProbability.expect.{0}
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_3 inst_4 B)
                                              c)
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleAtFintype.{u_1}
                                              Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_3 inst_4 B)
                                              c)
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} Head Band
                                              inst inst_1 inst_3 inst_4 B inst_2 xi c)
                                            fun
                                              (m :
                                                @Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head
                                                  inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_3 inst_4 B)
                                                  c) =>
                                            Erdos390.Full.ArithmeticModel.valuation
                                              (@Subtype.val.{1} Nat
                                                (fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    (Erdos390.Full.ArithmeticModel.primeBand
                                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head
                                                        inst
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          Head Band inst inst_1 inst_3 inst_4 B))
                                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head
                                                        inst
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          Head Band inst inst_1 inst_3 inst_4 B)))
                                                    p)
                                                p)
                                              (@Subtype.val.{1} Nat
                                                (fun (m : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                                                      Head inst
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        Head Band inst inst_1 inst_3 inst_4 B)
                                                      c)
                                                    m)
                                                m))
                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                            Aval
                                            (@Nat.cast.{0} Real Real.instNatCast
                                              (@Subtype.val.{1} Nat
                                                (fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    (Erdos390.Full.ArithmeticModel.primeBand
                                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head
                                                        inst
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          Head Band inst inst_1 inst_3 inst_4 B))
                                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head
                                                        inst
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          Head Band inst inst_1 inst_3 inst_4 B)))
                                                    p)
                                                p))))
                                      (∀ (c c' : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                        @LE.le.{0} Real Real.instLE
                                          (@abs.{0} Real Real.lattice Real.instAddGroup
                                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (@Erdos390.Full.FiniteProbability.expect.{0}
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head
                                                  inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_3 inst_4 B)
                                                  c)
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleAtFintype.{u_1}
                                                  Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_3 inst_4 B)
                                                  c)
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} Head
                                                  Band inst inst_1 inst_3 inst_4 B inst_2 xi c)
                                                fun
                                                  (m :
                                                    @Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                                      Head inst
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        Head Band inst inst_1 inst_3 inst_4 B)
                                                      c) =>
                                                Erdos390.Full.ArithmeticModel.valuation
                                                  (@Subtype.val.{1} Nat
                                                    (fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        (Erdos390.Full.ArithmeticModel.primeBand
                                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            Head inst
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                              Head Band inst inst_1 inst_3 inst_4 B))
                                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            Head inst
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                              Head Band inst inst_1 inst_3 inst_4 B)))
                                                        p)
                                                    p)
                                                  (@Subtype.val.{1} Nat
                                                    (fun (m : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                                                          Head inst
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                            Head Band inst inst_1 inst_3 inst_4 B)
                                                          c)
                                                        m)
                                                    m))
                                              (@Erdos390.Full.FiniteProbability.expect.{0}
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head
                                                  inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_3 inst_4 B)
                                                  c')
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleAtFintype.{u_1}
                                                  Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_3 inst_4 B)
                                                  c')
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} Head
                                                  Band inst inst_1 inst_3 inst_4 B inst_2 xi c')
                                                fun
                                                  (m :
                                                    @Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                                      Head inst
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        Head Band inst inst_1 inst_3 inst_4 B)
                                                      c') =>
                                                Erdos390.Full.ArithmeticModel.valuation
                                                  (@Subtype.val.{1} Nat
                                                    (fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        (Erdos390.Full.ArithmeticModel.primeBand
                                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            Head inst
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                              Head Band inst inst_1 inst_3 inst_4 B))
                                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            Head inst
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                              Head Band inst inst_1 inst_3 inst_4 B)))
                                                        p)
                                                    p)
                                                  (@Subtype.val.{1} Nat
                                                    (fun (m : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                                                          Head inst
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                            Head Band inst inst_1 inst_3 inst_4 B)
                                                          c')
                                                        m)
                                                    m))))
                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                            (epsilon
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_3 inst_4 B)))
                                            (@Nat.cast.{0} Real Real.instNatCast
                                              (@Subtype.val.{1} Nat
                                                (fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    (Erdos390.Full.ArithmeticModel.primeBand
                                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head
                                                        inst
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          Head Band inst inst_1 inst_3 inst_4 B))
                                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head
                                                        inst
                                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          Head Band inst inst_1 inst_3 inst_4 B)))
                                                    p)
                                                p)))))))

noncomputable def Erdos390.RemainingAnalyticGoal004_005 : Prop :=
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A C : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      ∃ K,
        And (LT.lt.{0} (0 : Real) K)
          (∃ N₀,
            ∀ {n k d : Nat},
              LE.le.{0} N₀ n →
                LT.lt.{0} (Erdos390.Full.ArithmeticModel.physicalBound A n) k →
                  LE.le.{0} k (Erdos390.Full.ArithmeticModel.physicalBound C n) →
                    LT.lt.{0} (0 : Nat) d →
                      LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                        Membership.mem.{0, 0}
                            (Nat.smoothNumbers (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (1 : Nat)))
                            d →
                          Nat.Coprime d (Erdos390.Full.HeadPattern.Pattern.modulus P) →
                            have S :=
                              Erdos390.Full.StructuredCells.structuredCell P
                                (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                (Erdos390.Full.ArithmeticModel.yNat n);
                            LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0}
                                  (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S fun m =>
                                    HMul.hMul.{0, 0, 0} (Erdos390.Full.ArithmeticModel.divInd d m)
                                      (ite.{1} (LE.le.{0} m k) (1 : Real) (0 : Real)))
                                  (HMul.hMul.{0, 0, 0}
                                    (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                                      (Erdos390.Full.ArithmeticModel.divInd d))
                                    (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S fun m =>
                                      ite.{1} (LE.le.{0} m k) (1 : Real) (0 : Real)))))
                              (HDiv.hDiv.{0, 0, 0} K (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n))))

noncomputable def Erdos390.RemainingAnalyticGoal004_006 : Prop :=
∀ (H : Erdos390.Full.HeadPattern.Pattern) {A C : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      LT.lt.{0} (0 : Real) C →
        ∀ (W : Nat),
          LT.lt.{0} (1 : Nat) W →
            (∀ (q : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes H) q → LE.le.{0} q W) →
              ∃ (K : Real),
                And (LT.lt.{0} (0 : Real) K)
                  (∃ (G : Real),
                    And (LT.lt.{0} (0 : Real) G)
                      (∃ (N₀ : Nat),
                        ∀ {n k p : Nat},
                          LE.le.{0} N₀ n →
                            LT.lt.{0} (Erdos390.Full.ArithmeticModel.physicalBound A n) k →
                              LE.le.{0} k (Erdos390.Full.ArithmeticModel.physicalBound C n) →
                                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                  ∀
                                    (hS :
                                      Finset.Nonempty.{0}
                                        (Erdos390.Full.StructuredCells.structuredCell H
                                          (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                          (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                          (Erdos390.Full.ArithmeticModel.yNat n))),
                                    LE.le.{0}
                                      (abs.{0}
                                        (Erdos390.Full.FiniteProbability.covariance.{0}
                                          (Erdos390.Full.FiniteProbability.uniformOnFinset.{0}
                                            (Erdos390.Full.StructuredCells.structuredCell H
                                              (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                              (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                              (Erdos390.Full.ArithmeticModel.yNat n))
                                            hS)
                                          (fun
                                              (m :
                                                ↥(Erdos390.Full.StructuredCells.structuredCell H
                                                    (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                                    (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                                    (Erdos390.Full.ArithmeticModel.yNat n))) =>
                                            Erdos390.Full.ArithmeticModel.valuation p (↑m : Nat))
                                          fun
                                            (m :
                                              ↥(Erdos390.Full.StructuredCells.structuredCell H
                                                  (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                                  (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                                  (Erdos390.Full.ArithmeticModel.yNat n))) =>
                                          ite.{1} (LE.le.{0} (↑m : Nat) k) (1 : Real) (0 : Real)))
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0}
                                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) K)
                                            (Erdos390.Full.Scale.L n))
                                          (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)))
                                        (HDiv.hDiv.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) G)
                                            (HPow.hPow.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0}
                                                (Erdos390.Full.PaperPrimePowerTailLedger.cutoffScale W)
                                                (Erdos390.Full.Scale.L n))
                                              (2 : Nat)))
                                          (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p : Real) (2 : Nat))
                                            (HPow.hPow.{0, 0, 0} (↑(Erdos390.Full.ArithmeticModel.yNat n) : Real)
                                              (2 : Nat)))))))

noncomputable def Erdos390.RemainingAnalyticGoal004_007 : Prop :=
∀ (H : Erdos390.Full.HeadPattern.Pattern) {A C : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A →
    @LT.lt.{0} Real Real.instLT A C →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        ∀ (B : Real) (W : Nat),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) W →
              (∀ (q : Nat),
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H.primes q →
                    @LE.le.{0} Nat instLENat q W) →
                @Exists.{1} (Nat → Real) fun (epsilon : Nat → Real) =>
                  And
                    (@Filter.Tendsto.{0, 0} Nat Real
                      (fun (n : Nat) =>
                        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (epsilon n)
                          (Real.log (Erdos390.Full.Scale.L n)))
                      (@Filter.atTop.{0} Nat Nat.instPreorder)
                      (@nhds.{0} Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                    (@Exists.{1} Nat fun (N₀ : Nat) =>
                      ∀ {n k p : Nat} (eta : Nat → Real),
                        @LE.le.{0} Nat instLENat N₀ n →
                          @LT.lt.{0} Nat instLTNat (Erdos390.Full.ArithmeticModel.physicalBound A n) k →
                            @LE.le.{0} Nat instLENat k (Erdos390.Full.ArithmeticModel.physicalBound C n) →
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                (∀ (q : Nat),
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (eta q))
                                        B) →
                                  let S :=
                                    Erdos390.Full.StructuredCells.structuredCell H
                                      (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                      (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                      (Erdos390.Full.ArithmeticModel.yNat n);
                                  ∀ (hS : @Finset.Nonempty.{0} Nat S),
                                    @LE.le.{0} Real Real.instLE
                                      (@abs.{0} Real Real.lattice Real.instAddGroup
                                        (@Erdos390.Full.FiniteProbability.covariance.{0}
                                          (@Subtype.{1} Nat fun (x : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              S x)
                                          (@Finset.Subtype.fintype.{0} Nat S)
                                          (@Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                                            (@Subtype.{1} Nat fun (x : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                S x)
                                            (@Finset.Subtype.fintype.{0} Nat S)
                                            (@Erdos390.Full.FiniteProbability.uniformOnFinset.{0} Nat S hS)
                                            fun
                                              (m :
                                                @Subtype.{1} Nat fun (x : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    S x) =>
                                            Erdos390.Full.ValuationScoreDomination.valuationScore
                                              (Erdos390.Full.ArithmeticModel.primeBand n W) eta
                                              (Erdos390.Full.Scale.L n)
                                              (@Subtype.val.{1} Nat
                                                (fun (x : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    S x)
                                                m))
                                          (fun
                                              (m :
                                                @Subtype.{1} Nat fun (x : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    S x) =>
                                            Erdos390.Full.ArithmeticModel.valuation p
                                              (@Subtype.val.{1} Nat
                                                (fun (x : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    S x)
                                                m))
                                          fun
                                            (m :
                                              @Subtype.{1} Nat fun (x : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  S x) =>
                                          @ite.{1} Real
                                            (@LE.le.{0} Nat instLENat
                                              (@Subtype.val.{1} Nat
                                                (fun (x : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    S x)
                                                m)
                                              k)
                                            ((@Subtype.val.{1} Nat
                                                  (fun (x : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      S x)
                                                  m).decLe
                                              k)
                                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                            (@OfNat.ofNat.{0} Real (nat_lit 0)
                                              (@Zero.toOfNat0.{0} Real Real.instZero))))
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (epsilon n) (@Nat.cast.{0} Real Real.instNatCast p)))

noncomputable def Erdos390.RemainingAnalyticGoal004_008 : Prop :=
∀ {Cell : Type u_1} [Fintype.{u_1} Cell] (H : Cell → Erdos390.Full.HeadPattern.Pattern) (A C : Cell → Real)
  (Cmax : Real),
  (∀ (c : Cell), LT.lt.{0} (0 : Real) (A c)) →
    (∀ (c : Cell), LT.lt.{0} (A c) (C c)) →
      (∀ (c : Cell), LT.lt.{0} (0 : Real) (C c)) →
        (∀ (c : Cell), LE.le.{0} (C c) Cmax) →
          ∀ (W : Nat),
            LT.lt.{0} (1 : Nat) W →
              (∀ (c : Cell) (p : Nat),
                  Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (H c)) p → LE.le.{0} p W) →
                ∀ (B : Real),
                  LE.le.{0} (0 : Real) B →
                    ∃ (epsilon : Nat → Real),
                      And (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon n))
                        (And
                          (Filter.Tendsto.{0, 0}
                            (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n)))
                            Filter.atTop.{0} (nhds.{0} (0 : Real)))
                          (∃ (N₀ : Nat),
                            ∀ {n p : Nat} (eta : Nat → Real),
                              LE.le.{0} N₀ n →
                                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                  (∀ (z : Nat),
                                      Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) z →
                                        LE.le.{0} (abs.{0} (eta z)) B) →
                                    have S := fun (c : Cell) =>
                                      Erdos390.Full.StructuredCells.structuredCell (H c)
                                        (Erdos390.Full.ArithmeticModel.physicalBound (A c) n)
                                        (Erdos390.Full.ArithmeticModel.physicalBound (C c) n)
                                        (Erdos390.Full.ArithmeticModel.yNat n);
                                    ∀ (hS : ∀ (c : Cell), Finset.Nonempty.{0} (S c)) (c c' : Cell),
                                      LE.le.{0}
                                        (abs.{0}
                                          (HSub.hSub.{0, 0, 0}
                                            (Erdos390.Full.FiniteProbability.expect.{0}
                                              (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                                                (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} (S c) (hS c))
                                                fun (m : ↥(S c)) =>
                                                Erdos390.Full.ValuationScoreDomination.valuationScore
                                                  (Erdos390.Full.ArithmeticModel.primeBand n W) eta
                                                  (Erdos390.Full.Scale.L n) ↑m)
                                              fun (m : ↥(S c)) => Erdos390.Full.ArithmeticModel.valuation p ↑m)
                                            (Erdos390.Full.FiniteProbability.expect.{0}
                                              (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                                                (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} (S c') (hS c'))
                                                fun (m : ↥(S c')) =>
                                                Erdos390.Full.ValuationScoreDomination.valuationScore
                                                  (Erdos390.Full.ArithmeticModel.primeBand n W) eta
                                                  (Erdos390.Full.Scale.L n) ↑m)
                                              fun (m : ↥(S c')) => Erdos390.Full.ArithmeticModel.valuation p ↑m)))
                                        (HDiv.hDiv.{0, 0, 0} (epsilon n) ↑p)))

noncomputable def Erdos390.RemainingAnalyticGoal004_009 : Prop :=
∀ (depth W K0 poolMinimum : Nat) {c deltaStar beta : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      LT.lt.{0} deltaStar (1 : Real) →
        ∀ (fixed bankBase candidates : Nat → Finset.{0} Nat) (initialSelector : Nat → Nat → Real),
          (∀ᶠ (n : Nat) in Filter.atTop.{0},
              Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalTopFrozenBalancedInitialRealization depth W K0
                n c deltaStar beta (fixed n) (bankBase n) (candidates n) (initialSelector n)) →
            Erdos390.WholePaper.BankPaperCanonicalActualSelectorMassEstimate c fixed bankBase candidates initialSelector

noncomputable def Erdos390.RemainingAnalyticGoal004_010 : Prop :=
∀ (W K0 : Nat) {c beta : Real},
  LT.lt.{0} (0 : Real) c →
    Asymptotics.IsBigO.{0, 0, 0} Filter.atTop.{0}
      (fun n =>
        Erdos390.WholePaper.BankPaperRealization.roughCanonicalRawRowDiscrepancy n
          (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (1 : Nat)
          (Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalBalancedRawWeight W K0 c beta n))
      fun n => HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.secondOrderScale n) (Erdos390.Full.Scale.L n)

noncomputable def Erdos390.RemainingAnalyticGoal004_011 : Prop :=
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {P : Finset.{0} Nat} (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _) {c : Real} {depth K0 : Nat} (R : Erdos390.WholePaper.BankPaperRealization (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))))) (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R depth)) (deltaStar alpha beta sigma : Real) (_radius : NNReal) (Cpost : Real) (endpoint : Nat → Real) (hdelta : @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) delta) (hWtwo : @LE.le.{0} Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 2) _) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (S : @Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (hpartition : @Eq.{1} (@Erdos390.Full.ArithmeticBandGeometry.Partition.{0} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _) (@Erdos390.Full.PaperBridgeFit.BridgeData.partition.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (@Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_1 delta eta M P B hWtwo a) S)) (r0 rho tangentConstant N density : Real) (hrho : @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) rho) (hratio : @LT.lt.{0} Real _ (@HPow.hPow.{0, 0, 0} Real Nat Real _ rho (@OfNat.ofNat.{0} Nat (nat_lit 3) _)) r0) (htangent : @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) tangentConstant) (hN : @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) N) (hscaleDom : @LE.le.{0} Real _ (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@HMul.hMul.{0, 0, 0} Real Real Real _ Cpost (@Erdos390.Full.PaperBridgeFit.BridgeData.q.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@HMul.hMul.{0, 0, 0} Real Real Real _ tangentConstant N) (Real.log (Erdos390.Full.ArithmeticModel.y (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))))) (hMertens : @LE.le.{0} Nat _ Erdos390.Full.PrimeBandQuadrature.fullReciprocalSumUniformCutoff (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (hPNT : Erdos390.WholePaper.TangentFixedRatioPrimeCountLower (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) rho) (hprime : Erdos390.WholePaper.TangentFixedRatioPrimeIntervalOccupied (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) rho) (hTwo : ∀ (k : Fin (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)), @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 2) _) (Erdos390.Full.RegularMeshPrimeCutoffs.scalePoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.RegularRelativeMesh.Mesh.lower delta eta M k))) (Hmoment : @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.MomentReady delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_1 delta eta M P B hWtwo a) S)) (HselectorPartition : @Erdos390.WholePaper.BankPaperCanonicalRoundedSelectorTangentInput.{0} c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R depth) R certificate (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) R deltaStar) (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R depth) R certificate deltaStar (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _))) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ (@Erdos390.Full.ArithmeticBandGeometry.Partition.band.{0} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.partition.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.WholePaper.bankPaperCanonicalRatioCellIndex delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_1 delta eta M P B hWtwo a) S rho) (@Erdos390.WholePaper.bankPaperCanonicalActualP87PointwiseUpper.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B (@Erdos390.Full.PaperBridgeFit.BridgeData.q.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) Cpost) (@Erdos390.WholePaper.tangentRatioCellTailPointwiseUpper.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ (@Erdos390.WholePaper.bankPaperCanonicalActualP87PointwiseUpper.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B (@Erdos390.Full.PaperBridgeFit.BridgeData.q.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) Cpost) (@Erdos390.Full.ArithmeticBandGeometry.Partition.band.{0} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.partition.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.WholePaper.bankPaperCanonicalRatioCellIndex delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_1 delta eta M P B hWtwo a) S rho)) endpoint) (Hslack : @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalGuardedEndpointSlackConstruction c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) R certificate deltaStar (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) alpha beta (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma endpoint) (hKh : @LE.le.{0} Nat _ (@HMul.hMul.{0, 0, 0} Nat Nat Nat _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (hdensity : @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) density) (hsigma : @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) sigma) (hscale : @Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real _ (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) N) (@Nat.cast.{0} Real _ (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) (hchargeDvd : @Dvd.dvd.{0} Nat _ (@Erdos390.WholePaper.BankPaperRealization.selectorTailCharge (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) R deltaStar)) (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R depth) certificate)) (hfixedComponents : @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNineFixedComponentCollisionFree c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) R deltaStar) (hmain : @LE.le.{0} Real _ (Erdos390.WholePaper.tangentDistributedPaperMainBudget (Erdos390.WholePaper.bankPaperCanonicalRatioCellTrafficConstant rho) (Erdos390.WholePaper.bankPaperCanonicalRatioCellIncidentConstant rho) tangentConstant (@HAdd.hAdd.{0, 0, 0} Real Real Real _ delta (@Erdos390.Full.RegularRelativeMesh.Mesh.ratio delta eta M)) sigma) (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@HPow.hPow.{0, 0, 0} Real Nat Real _ density (@OfNat.ofNat.{0} Nat (nat_lit 2) _)) (@OfNat.ofNat.{0} Real (nat_lit 48) _))) (herror : @LE.le.{0} Real _ (Erdos390.WholePaper.tangentDistributedPaperErrorBudget (@Erdos390.WholePaper.bankPaperCanonicalRatioCellTrafficErrorCoefficient delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) rho tangentConstant) (Erdos390.WholePaper.bankPaperCanonicalRatioCellIncidentErrorCoefficient (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) rho tangentConstant) sigma) (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@HPow.hPow.{0, 0, 0} Real Nat Real _ density (@OfNat.ofNat.{0} Nat (nat_lit 2) _)) (@OfNat.ofNat.{0} Real (nat_lit 96) _))) (hceiling : @LE.le.{0} Real _ (Erdos390.WholePaper.tangentDistributedPaperCeilingBudget (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.Full.ArithmeticModel.yNat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (@Erdos390.WholePaper.tangentDistributedSupportCount.{0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) _)) (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@HPow.hPow.{0, 0, 0} Real Nat Real _ density (@OfNat.ofNat.{0} Nat (nat_lit 2) _)) (@OfNat.ofNat.{0} Real (nat_lit 96) _)))
  (hlowerPos :
    let flow := @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow delta eta M c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) R certificate deltaStar (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_2 delta eta M P B c depth K0 R certificate deltaStar hWtwo a) S rho endpoint;
    ∀ (request : @Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma), @LT.lt.{0} Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 0) _) (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma density request))
  (hlower :
    let flow := @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow delta eta M c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) R certificate deltaStar (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_2 delta eta M P B c depth K0 R certificate deltaStar hWtwo a) S rho endpoint;
    ∀ (request : @Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma), @LE.le.{0} Nat _ (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma density request) (@Finset.card.{0} Nat (@Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0} (Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) (@Erdos390.WholePaper.tangentPositiveFlowEdges.{0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) _ _ flow) (@Erdos390.WholePaper.tangentStarEdgeSource.{0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (@Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) (@Erdos390.WholePaper.tangentStarEdgeTarget.{0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (@Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma (fun (edge : Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) => flow (@Prod.fst.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) edge) (@Prod.snd.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) edge)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (Erdos390.WholePaper.roughHeadModulus (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (Erdos390.Full.ArithmeticModel.yNat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (@Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) R depth) R certificate (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) R deltaStar)) request)))
  (hlowerScale :
    let flow := @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow delta eta M c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) R certificate deltaStar (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_2 delta eta M P B c depth K0 R certificate deltaStar hWtwo a) S rho endpoint;
    ∀ (request : @Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma) (side : Erdos390.WholePaper.TangentEndpointSide), @LE.le.{0} Real _ (@HMul.hMul.{0, 0, 0} Real Real Real _ density (@Nat.cast.{0} Real _ (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)))) (@HMul.hMul.{0, 0, 0} Real Real Real _ (@Nat.cast.{0} Real _ (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma density request)) (@Nat.cast.{0} Real _ (@Erdos390.WholePaper.tangentEndpointLabel.{0} (@Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma) (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma) (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) flow (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma) side request)))),
  And (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNineFinalPayload c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) R certificate deltaStar endpoint (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow delta eta M c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) R certificate deltaStar (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_2 delta eta M P B c depth K0 R certificate deltaStar hWtwo a) S rho endpoint) (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) sigma) (@Erdos390.WholePaper.TangentRatioCellGeometry.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) (@Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B))) (@Erdos390.WholePaper.bankPaperCanonicalExponentBandOf delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_2 delta eta M P B c depth K0 R certificate deltaStar hWtwo a) S) (@Erdos390.WholePaper.bankPaperCanonicalRatioCellIndex delta eta M (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) hdelta (@Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B) (fun (a : @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ B)) (@OfNat.ofNat.{0} Nat (nat_lit 0) _)) => @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_2 delta eta M P B c depth K0 R certificate deltaStar hWtwo a) S rho) r0)

noncomputable def Erdos390.RemainingAnalyticGoal004_012 : Prop :=
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {P : Finset.{0} Nat}
  (Patterns : Erdos390.Full.PaperHeadSimplex.Tag P → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cprom Cbank : Nat)
  (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) {c : Real} (depth W K0 E Ntail : Nat)
  (F : Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily c depth Ntail)
  (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor physicalEtaFloor postMarginFloor Cmass density :
    Real)
  (logY Lambda0 mFrozen qTilde : Nat → Real) (rho sigma Cinitial : Real) (radius : NNReal) (CP87 : Real)
  (hdelta :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta)
  (B :
    Nat →
      @Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
          @Option.instDecidableEq.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (fun
                (a b :
                  @Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
              @Subtype.instDecidableEq.{1} Nat
                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                instDecidableEqNat a b)
            a b)
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (instDecidableEqFin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
      P Patterns I Cprom Cbank G c depth W K0 E Ntail F deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density logY Lambda0 mFrozen qTilde delta eta M hdelta B →
    @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
        P Patterns I Cprom Cbank G c depth W K0 deltaStar betaProt betaAct mu logY Lambda0 mFrozen qTilde Cinitial →
      @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
          delta eta M P Patterns I Cprom Cbank G c depth W K0 deltaStar betaProt betaAct postMarginFloor Cmass density
          (Erdos390.WholePaper.bankPaperCanonicalSmoothFinalActiveMassFamily mu logY Lambda0 mFrozen qTilde) Cinitial
          radius CP87 hdelta →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            Cinitial →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (↑radius : Real) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                CP87 →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  c →
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W →
                  @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) deltaStar →
                    @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) betaProt →
                      @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) betaAct →
                        @LE.le.{0} Real Real.instLE
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) betaProt betaAct)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) c
                              (Erdos390.WholePaper.roughHeadDensity W)) →
                          @LE.le.{0} Real Real.instLE
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (Erdos390.WholePaper.roughHeadDensity W))
                              (@Nat.cast.{0} Real Real.instNatCast
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                            @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Cmass →
                              @LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) density →
                                @LT.lt.{0} Real Real.instLT
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) sigma →
                                  @LE.le.{0} Real Real.instLE sigma betaProt →
                                    @LE.le.{0} Nat instLENat
                                        Erdos390.Full.RegularMeshPrimeCutoffs.canonicalActualMomentCutoff W →
                                      @Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
                                        delta eta M P B c depth K0 deltaStar rho sigma CP87 hdelta

noncomputable def Erdos390.RemainingAnalyticGoal004_013 : Prop :=
∀ {P : Finset.{0} Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  (hprime :
    ∀ (p : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p →
        Nat.Prime p)
  (E : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) E →
    ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals),
      (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (I.lower sigma)) →
        (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
            @LT.lt.{0} Real Real.instLT (I.upper sigma)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
          ∀ (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank)
            (depth W K : Nat) {c betaAct marginFloor deltaStar betaProt : Real},
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  betaAct →
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    marginFloor →
                  @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) betaProt →
                    @HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat)
                        (Erdos390.WholePaper.primesUpTo W) P →
                      ∀ (mFrozen qTilde A0 : Nat → Real),
                        Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedger
                            (fun (n : Nat) =>
                              Erdos390.WholePaper.bankPaperCanonicalRawSmoothBaseMass W n
                                (Erdos390.WholePaper.upperTailLength c n) K betaAct)
                            qTilde A0 →
                          @Filter.Eventually.{0} Nat
                            (fun (n : Nat) =>
                              ∀
                                (B :
                                  @Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (@Finset.Subtype.fintype.{0} Nat P))
                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                      @Option.instDecidableEq.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (fun
                                            (a b :
                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p) =>
                                          @Subtype.instDecidableEq.{1} Nat
                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P)
                                            instDecidableEqNat a b)
                                        a b)
                                    inst inst_1),
                                @Eq.{1} Nat
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                        (@instFintypeOption.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (@Finset.Subtype.fintype.{0} Nat P))
                                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                          @Option.instDecidableEq.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (fun
                                                (a b :
                                                  @Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p) =>
                                              @Subtype.instDecidableEq.{1} Nat
                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P)
                                                instDecidableEqNat a b)
                                            a b)
                                        inst inst_1 B))
                                    n →
                                  @Eq.{1} Nat
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@instFintypeOption.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (@Finset.Subtype.fintype.{0} Nat P))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                            @Option.instDecidableEq.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (fun
                                                  (a b :
                                                    @Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p) =>
                                                @Subtype.instDecidableEq.{1} Nat
                                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P)
                                                  instDecidableEqNat a b)
                                              a b)
                                          inst inst_1 B))
                                      W →
                                    ∀
                                      (hsep :
                                        @LT.lt.{0} Nat instLTNat
                                          (Erdos390.Full.ArithmeticModel.physicalBound
                                            (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                (@instFintypeOption.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                  @Option.instDecidableEq.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (fun
                                                        (a b :
                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p) =>
                                                      @Subtype.instDecidableEq.{1} Nat
                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P)
                                                        instDecidableEqNat a b)
                                                    a b)
                                                inst inst_1 B)))
                                          (Erdos390.Full.ArithmeticModel.physicalBound
                                            (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                (@instFintypeOption.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                  @Option.instDecidableEq.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (fun
                                                        (a b :
                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p) =>
                                                      @Subtype.instDecidableEq.{1} Nat
                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P)
                                                        instDecidableEqNat a b)
                                                    a b)
                                                inst inst_1 B))))
                                      (hremaining :
                                        ∀
                                          (cell :
                                            Erdos390.Full.PaperBridgeFit.Cell.{0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)),
                                          @Finset.Nonempty.{0} Nat
                                            (@SDiff.sdiff.{0} (Finset.{0} Nat)
                                              (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                              (@Erdos390.Full.PaperGuardCensus.rawCell.{0}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                (Erdos390.Full.PaperHeadSimplex.pattern P hprime E) I
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                cell)
                                              (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                Cprom Cbank
                                                (ledger
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B)))))),
                                      @Eq.{1}
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P)))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                              @Option.instDecidableEq.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (fun
                                                    (a b :
                                                      @Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p) =>
                                                  @Subtype.instDecidableEq.{1} Nat
                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P)
                                                    instDecidableEqNat a b)
                                                a b)
                                            inst inst_1 B)
                                          (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (Erdos390.Full.PaperHeadSimplex.pattern P hprime E) I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                (@instFintypeOption.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                  @Option.instDecidableEq.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (fun
                                                        (a b :
                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p) =>
                                                      @Subtype.instDecidableEq.{1} Nat
                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P)
                                                        instDecidableEqNat a b)
                                                    a b)
                                                inst inst_1 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                (@instFintypeOption.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                  @Option.instDecidableEq.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (fun
                                                        (a b :
                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p) =>
                                                      @Subtype.instDecidableEq.{1} Nat
                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P)
                                                        instDecidableEqNat a b)
                                                    a b)
                                                inst inst_1 B))
                                            Cprom Cbank
                                            (ledger
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                (@instFintypeOption.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                    @Option.instDecidableEq.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (fun
                                                          (a b :
                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p) =>
                                                        @Subtype.instDecidableEq.{1} Nat
                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P)
                                                          instDecidableEqNat a b)
                                                      a b)
                                                  inst inst_1 B)))
                                            hsep hremaining) →
                                        ∀
                                          (R :
                                            Erdos390.WholePaper.BankPaperRealization
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                (@instFintypeOption.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                    @Option.instDecidableEq.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (fun
                                                          (a b :
                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p) =>
                                                        @Subtype.instDecidableEq.{1} Nat
                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P)
                                                          instDecidableEqNat a b)
                                                      a b)
                                                  inst inst_1 B))
                                              (Erdos390.WholePaper.upperEndpoint
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                (Erdos390.WholePaper.upperTailLength c
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B)))))
                                          (certificate :
                                            Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                (@instFintypeOption.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                    @Option.instDecidableEq.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (fun
                                                          (a b :
                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p) =>
                                                        @Subtype.instDecidableEq.{1} Nat
                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P)
                                                          instDecidableEqNat a b)
                                                      a b)
                                                  inst inst_1 B))
                                              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                (Erdos390.WholePaper.upperEndpoint
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B))
                                                  (Erdos390.WholePaper.upperTailLength c
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                        (@instFintypeOption.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (@Finset.Subtype.fintype.{0} Nat P))
                                                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                          @Option.instDecidableEq.{0}
                                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p)
                                                            (fun
                                                                (a b :
                                                                  @Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p) =>
                                                              @Subtype.instDecidableEq.{1} Nat
                                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P)
                                                                instDecidableEqNat a b)
                                                            a b)
                                                        inst inst_1 B))))
                                                R)
                                              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                (Erdos390.WholePaper.upperEndpoint
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B))
                                                  (Erdos390.WholePaper.upperTailLength c
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                        (@instFintypeOption.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (@Finset.Subtype.fintype.{0} Nat P))
                                                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                          @Option.instDecidableEq.{0}
                                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p)
                                                            (fun
                                                                (a b :
                                                                  @Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p) =>
                                                              @Subtype.instDecidableEq.{1} Nat
                                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P)
                                                                instDecidableEqNat a b)
                                                            a b)
                                                        inst inst_1 B))))
                                                R)
                                              (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                (Erdos390.WholePaper.upperEndpoint
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B))
                                                  (Erdos390.WholePaper.upperTailLength c
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                        (@instFintypeOption.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (@Finset.Subtype.fintype.{0} Nat P))
                                                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                          @Option.instDecidableEq.{0}
                                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p)
                                                            (fun
                                                                (a b :
                                                                  @Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p) =>
                                                              @Subtype.instDecidableEq.{1} Nat
                                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P)
                                                                instDecidableEqNat a b)
                                                            a b)
                                                        inst inst_1 B))))
                                                R depth)),
                                          @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalBridgeGuardAgreement
                                              c depth
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                (@instFintypeOption.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                    @Option.instDecidableEq.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (fun
                                                          (a b :
                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p) =>
                                                        @Subtype.instDecidableEq.{1} Nat
                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P)
                                                          instDecidableEqNat a b)
                                                      a b)
                                                  inst inst_1 B))
                                              (Erdos390.WholePaper.upperTailLength c
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B)))
                                              Cprom Cbank
                                              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                (Erdos390.WholePaper.upperEndpoint
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B))
                                                  (Erdos390.WholePaper.upperTailLength c
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                        (@instFintypeOption.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (@Finset.Subtype.fintype.{0} Nat P))
                                                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                          @Option.instDecidableEq.{0}
                                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p)
                                                            (fun
                                                                (a b :
                                                                  @Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p) =>
                                                              @Subtype.instDecidableEq.{1} Nat
                                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P)
                                                                instDecidableEqNat a b)
                                                            a b)
                                                        inst inst_1 B))))
                                                R)
                                              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                (Erdos390.WholePaper.upperEndpoint
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B))
                                                  (Erdos390.WholePaper.upperTailLength c
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                        (@instFintypeOption.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (@Finset.Subtype.fintype.{0} Nat P))
                                                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                          @Option.instDecidableEq.{0}
                                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p)
                                                            (fun
                                                                (a b :
                                                                  @Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p) =>
                                                              @Subtype.instDecidableEq.{1} Nat
                                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P)
                                                                instDecidableEqNat a b)
                                                            a b)
                                                        inst inst_1 B))))
                                                R)
                                              (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B))
                                                (Erdos390.WholePaper.upperEndpoint
                                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B))
                                                  (Erdos390.WholePaper.upperTailLength c
                                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                        (@instFintypeOption.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (@Finset.Subtype.fintype.{0} Nat P))
                                                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                          @Option.instDecidableEq.{0}
                                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p)
                                                            (fun
                                                                (a b :
                                                                  @Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p) =>
                                                              @Subtype.instDecidableEq.{1} Nat
                                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P)
                                                                instDecidableEqNat a b)
                                                            a b)
                                                        inst inst_1 B))))
                                                R depth)
                                              (ledger
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B)))
                                              R certificate deltaStar →
                                            ∀
                                              (T :
                                                @Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0}
                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                  (@instFintypeOption.{0}
                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P p)
                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                      @Option.instDecidableEq.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (fun
                                                            (a b :
                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p) =>
                                                          @Subtype.instDecidableEq.{1} Nat
                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P)
                                                            instDecidableEqNat a b)
                                                        a b)
                                                    inst inst_1 B)),
                                              @LE.le.{0} Real Real.instLE marginFloor
                                                  (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{0}
                                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                    (@instFintypeOption.{0}
                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p)
                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                      (@instFintypeOption.{0}
                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p)
                                                        (@Finset.Subtype.fintype.{0} Nat P))
                                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                        @Option.instDecidableEq.{0}
                                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                (@Finset.instSetLike.{0} Nat))
                                                              P p)
                                                          (fun
                                                              (a b :
                                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p) =>
                                                            @Subtype.instDecidableEq.{1} Nat
                                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P)
                                                              instDecidableEqNat a b)
                                                          a b)
                                                      inst inst_1 B)
                                                    T) →
                                                ∀ (fixed : Finset.{0} Nat) (alpha betaTotal : Real),
                                                  @Eq.{1} Real (mFrozen n)
                                                      (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenSmoothFrozenMass.{u_1}
                                                        P Band inst inst_1 B c depth K R certificate deltaStar betaProt
                                                        alpha) →
                                                    @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt.{u_1}
                                                        P Band inst inst_1 B c depth K R certificate fixed T deltaStar
                                                        betaProt alpha betaTotal (qTilde n) →
                                                      @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSelectorSourceState
                                                        c depth
                                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                          (@instFintypeOption.{0}
                                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p)
                                                            (@Finset.Subtype.fintype.{0} Nat P))
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                            (@instFintypeOption.{0}
                                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p)
                                                              (@Finset.Subtype.fintype.{0} Nat P))
                                                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                              @Option.instDecidableEq.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (fun
                                                                    (a b :
                                                                      @Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p) =>
                                                                  @Subtype.instDecidableEq.{1} Nat
                                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P)
                                                                    instDecidableEqNat a b)
                                                                a b)
                                                            inst inst_1 B))
                                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                          (@instFintypeOption.{0}
                                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                  (@Finset.instSetLike.{0} Nat))
                                                                P p)
                                                            (@Finset.Subtype.fintype.{0} Nat P))
                                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                            (@instFintypeOption.{0}
                                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p)
                                                              (@Finset.Subtype.fintype.{0} Nat P))
                                                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                              @Option.instDecidableEq.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (fun
                                                                    (a b :
                                                                      @Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p) =>
                                                                  @Subtype.instDecidableEq.{1} Nat
                                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P)
                                                                    instDecidableEqNat a b)
                                                                a b)
                                                            inst inst_1 B))
                                                        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (@instFintypeOption.{0}
                                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p)
                                                              (@Finset.Subtype.fintype.{0} Nat P))
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                  u_1}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                @Option.instDecidableEq.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (fun
                                                                      (a b :
                                                                        @Subtype.{1} Nat fun (p : Nat) =>
                                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P p) =>
                                                                    @Subtype.instDecidableEq.{1} Nat
                                                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P)
                                                                      instDecidableEqNat a b)
                                                                  a b)
                                                              inst inst_1 B))
                                                          (Erdos390.WholePaper.upperEndpoint
                                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                    u_1}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                  @Option.instDecidableEq.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (fun
                                                                        (a b :
                                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P p) =>
                                                                      @Subtype.instDecidableEq.{1} Nat
                                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P)
                                                                        instDecidableEqNat a b)
                                                                    a b)
                                                                inst inst_1 B))
                                                            (Erdos390.WholePaper.upperTailLength c
                                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                      u_1}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                    @Option.instDecidableEq.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (fun
                                                                          (a b :
                                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                                              @Membership.mem.{0, 0} Nat
                                                                                (Finset.{0} Nat)
                                                                                (@SetLike.instMembership.{0, 0}
                                                                                  (Finset.{0} Nat) Nat
                                                                                  (@Finset.instSetLike.{0} Nat))
                                                                                P p) =>
                                                                        @Subtype.instDecidableEq.{1} Nat
                                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P)
                                                                          instDecidableEqNat a b)
                                                                      a b)
                                                                  inst inst_1 B))))
                                                          R)
                                                        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (@instFintypeOption.{0}
                                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p)
                                                              (@Finset.Subtype.fintype.{0} Nat P))
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                  u_1}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                @Option.instDecidableEq.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (fun
                                                                      (a b :
                                                                        @Subtype.{1} Nat fun (p : Nat) =>
                                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P p) =>
                                                                    @Subtype.instDecidableEq.{1} Nat
                                                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P)
                                                                      instDecidableEqNat a b)
                                                                  a b)
                                                              inst inst_1 B))
                                                          (Erdos390.WholePaper.upperEndpoint
                                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                    u_1}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                  @Option.instDecidableEq.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (fun
                                                                        (a b :
                                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P p) =>
                                                                      @Subtype.instDecidableEq.{1} Nat
                                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P)
                                                                        instDecidableEqNat a b)
                                                                    a b)
                                                                inst inst_1 B))
                                                            (Erdos390.WholePaper.upperTailLength c
                                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                      u_1}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                    @Option.instDecidableEq.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (fun
                                                                          (a b :
                                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                                              @Membership.mem.{0, 0} Nat
                                                                                (Finset.{0} Nat)
                                                                                (@SetLike.instMembership.{0, 0}
                                                                                  (Finset.{0} Nat) Nat
                                                                                  (@Finset.instSetLike.{0} Nat))
                                                                                P p) =>
                                                                        @Subtype.instDecidableEq.{1} Nat
                                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P)
                                                                          instDecidableEqNat a b)
                                                                      a b)
                                                                  inst inst_1 B))))
                                                          R)
                                                        (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (@instFintypeOption.{0}
                                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p)
                                                              (@Finset.Subtype.fintype.{0} Nat P))
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                  u_1}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                @Option.instDecidableEq.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (fun
                                                                      (a b :
                                                                        @Subtype.{1} Nat fun (p : Nat) =>
                                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P p) =>
                                                                    @Subtype.instDecidableEq.{1} Nat
                                                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P)
                                                                      instDecidableEqNat a b)
                                                                  a b)
                                                              inst inst_1 B))
                                                          (Erdos390.WholePaper.upperEndpoint
                                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                    u_1}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                  @Option.instDecidableEq.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (fun
                                                                        (a b :
                                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P p) =>
                                                                      @Subtype.instDecidableEq.{1} Nat
                                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P)
                                                                        instDecidableEqNat a b)
                                                                    a b)
                                                                inst inst_1 B))
                                                            (Erdos390.WholePaper.upperTailLength c
                                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                      u_1}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                    @Option.instDecidableEq.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (fun
                                                                          (a b :
                                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                                              @Membership.mem.{0, 0} Nat
                                                                                (Finset.{0} Nat)
                                                                                (@SetLike.instMembership.{0, 0}
                                                                                  (Finset.{0} Nat) Nat
                                                                                  (@Finset.instSetLike.{0} Nat))
                                                                                P p) =>
                                                                        @Subtype.instDecidableEq.{1} Nat
                                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P)
                                                                          instDecidableEqNat a b)
                                                                      a b)
                                                                  inst inst_1 B))))
                                                          R depth)
                                                        R certificate fixed
                                                        (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet
                                                          c depth
                                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (@instFintypeOption.{0}
                                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                    (@Finset.instSetLike.{0} Nat))
                                                                  P p)
                                                              (@Finset.Subtype.fintype.{0} Nat P))
                                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                  u_1}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                @Option.instDecidableEq.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (fun
                                                                      (a b :
                                                                        @Subtype.{1} Nat fun (p : Nat) =>
                                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P p) =>
                                                                    @Subtype.instDecidableEq.{1} Nat
                                                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P)
                                                                      instDecidableEqNat a b)
                                                                  a b)
                                                              inst inst_1 B))
                                                          (Erdos390.WholePaper.upperTailLength c
                                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                    u_1}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                  @Option.instDecidableEq.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (fun
                                                                        (a b :
                                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P p) =>
                                                                      @Subtype.instDecidableEq.{1} Nat
                                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P)
                                                                        instDecidableEqNat a b)
                                                                    a b)
                                                                inst inst_1 B)))
                                                          (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                    u_1}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                  @Option.instDecidableEq.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (fun
                                                                        (a b :
                                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P p) =>
                                                                      @Subtype.instDecidableEq.{1} Nat
                                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P)
                                                                        instDecidableEqNat a b)
                                                                    a b)
                                                                inst inst_1 B))
                                                            (Erdos390.WholePaper.upperEndpoint
                                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                      u_1}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                    @Option.instDecidableEq.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (fun
                                                                          (a b :
                                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                                              @Membership.mem.{0, 0} Nat
                                                                                (Finset.{0} Nat)
                                                                                (@SetLike.instMembership.{0, 0}
                                                                                  (Finset.{0} Nat) Nat
                                                                                  (@Finset.instSetLike.{0} Nat))
                                                                                P p) =>
                                                                        @Subtype.instDecidableEq.{1} Nat
                                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P)
                                                                          instDecidableEqNat a b)
                                                                      a b)
                                                                  inst inst_1 B))
                                                              (Erdos390.WholePaper.upperTailLength c
                                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                        u_1}
                                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                    (@instFintypeOption.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                      @Option.instDecidableEq.{0}
                                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P p)
                                                                        (fun
                                                                            (a b :
                                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                                @Membership.mem.{0, 0} Nat
                                                                                  (Finset.{0} Nat)
                                                                                  (@SetLike.instMembership.{0, 0}
                                                                                    (Finset.{0} Nat) Nat
                                                                                    (@Finset.instSetLike.{0} Nat))
                                                                                  P p) =>
                                                                          @Subtype.instDecidableEq.{1} Nat
                                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P)
                                                                            instDecidableEqNat a b)
                                                                        a b)
                                                                    inst inst_1 B))))
                                                            R)
                                                          (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                    u_1}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                  @Option.instDecidableEq.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (fun
                                                                        (a b :
                                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P p) =>
                                                                      @Subtype.instDecidableEq.{1} Nat
                                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P)
                                                                        instDecidableEqNat a b)
                                                                    a b)
                                                                inst inst_1 B))
                                                            (Erdos390.WholePaper.upperEndpoint
                                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                      u_1}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                    @Option.instDecidableEq.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (fun
                                                                          (a b :
                                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                                              @Membership.mem.{0, 0} Nat
                                                                                (Finset.{0} Nat)
                                                                                (@SetLike.instMembership.{0, 0}
                                                                                  (Finset.{0} Nat) Nat
                                                                                  (@Finset.instSetLike.{0} Nat))
                                                                                P p) =>
                                                                        @Subtype.instDecidableEq.{1} Nat
                                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P)
                                                                          instDecidableEqNat a b)
                                                                      a b)
                                                                  inst inst_1 B))
                                                              (Erdos390.WholePaper.upperTailLength c
                                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                        u_1}
                                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                    (@instFintypeOption.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                      @Option.instDecidableEq.{0}
                                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P p)
                                                                        (fun
                                                                            (a b :
                                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                                @Membership.mem.{0, 0} Nat
                                                                                  (Finset.{0} Nat)
                                                                                  (@SetLike.instMembership.{0, 0}
                                                                                    (Finset.{0} Nat) Nat
                                                                                    (@Finset.instSetLike.{0} Nat))
                                                                                  P p) =>
                                                                          @Subtype.instDecidableEq.{1} Nat
                                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P)
                                                                            instDecidableEqNat a b)
                                                                        a b)
                                                                    inst inst_1 B))))
                                                            R)
                                                          (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (@instFintypeOption.{0}
                                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                                      (@Finset.instSetLike.{0} Nat))
                                                                    P p)
                                                                (@Finset.Subtype.fintype.{0} Nat P))
                                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                    u_1}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                  @Option.instDecidableEq.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (fun
                                                                        (a b :
                                                                          @Subtype.{1} Nat fun (p : Nat) =>
                                                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P p) =>
                                                                      @Subtype.instDecidableEq.{1} Nat
                                                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P)
                                                                        instDecidableEqNat a b)
                                                                    a b)
                                                                inst inst_1 B))
                                                            (Erdos390.WholePaper.upperEndpoint
                                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (@instFintypeOption.{0}
                                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P p)
                                                                  (@Finset.Subtype.fintype.{0} Nat P))
                                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                      u_1}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                    @Option.instDecidableEq.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (fun
                                                                          (a b :
                                                                            @Subtype.{1} Nat fun (p : Nat) =>
                                                                              @Membership.mem.{0, 0} Nat
                                                                                (Finset.{0} Nat)
                                                                                (@SetLike.instMembership.{0, 0}
                                                                                  (Finset.{0} Nat) Nat
                                                                                  (@Finset.instSetLike.{0} Nat))
                                                                                P p) =>
                                                                        @Subtype.instDecidableEq.{1} Nat
                                                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P)
                                                                          instDecidableEqNat a b)
                                                                      a b)
                                                                  inst inst_1 B))
                                                              (Erdos390.WholePaper.upperTailLength c
                                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                  (@instFintypeOption.{0}
                                                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                          Nat (@Finset.instSetLike.{0} Nat))
                                                                        P p)
                                                                    (@Finset.Subtype.fintype.{0} Nat P))
                                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0,
                                                                        u_1}
                                                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                                                    (@instFintypeOption.{0}
                                                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p)
                                                                      (@Finset.Subtype.fintype.{0} Nat P))
                                                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                                      @Option.instDecidableEq.{0}
                                                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                            (@SetLike.instMembership.{0, 0}
                                                                              (Finset.{0} Nat) Nat
                                                                              (@Finset.instSetLike.{0} Nat))
                                                                            P p)
                                                                        (fun
                                                                            (a b :
                                                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                                                @Membership.mem.{0, 0} Nat
                                                                                  (Finset.{0} Nat)
                                                                                  (@SetLike.instMembership.{0, 0}
                                                                                    (Finset.{0} Nat) Nat
                                                                                    (@Finset.instSetLike.{0} Nat))
                                                                                  P p) =>
                                                                          @Subtype.instDecidableEq.{1} Nat
                                                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                              (@SetLike.instMembership.{0, 0}
                                                                                (Finset.{0} Nat) Nat
                                                                                (@Finset.instSetLike.{0} Nat))
                                                                              P)
                                                                            instDecidableEqNat a b)
                                                                        a b)
                                                                    inst inst_1 B))))
                                                            R depth)
                                                          R certificate deltaStar K)
                                                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedSourceSelector.{u_1}
                                                          P Band inst inst_1 B c depth K R certificate T deltaStar
                                                          betaProt alpha betaTotal (qTilde n)))
                            (@Filter.atTop.{0} Nat Nat.instPreorder)

noncomputable def Erdos390.RemainingAnalyticGoal004_014 : Prop :=
∀ {P : Finset.{0} Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band] (Patterns : Erdos390.Full.PaperHeadSimplex.Tag P → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cprom Cbank : Nat) (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (depth W K0 : Nat) {c deltaStar betaProt betaAct sigma : Real}, @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) c → @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) deltaStar → @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) betaProt → @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) betaAct → @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) sigma → @LE.le.{0} Real _ sigma betaProt → @LE.le.{0} Real _ (@HAdd.hAdd.{0, 0, 0} Real Real Real _ betaProt betaAct) (@HDiv.hDiv.{0, 0, 0} Real Real Real _ c (Erdos390.WholePaper.roughHeadDensity W)) → @LE.le.{0} Real _ (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) (Erdos390.WholePaper.roughHeadDensity W)) (@Nat.cast.{0} Real _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _))) → @LE.le.{0} Nat _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ (@HMul.hMul.{0, 0, 0} Nat Nat Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 2) _) depth) (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) W → @Filter.Eventually.{0} Nat (fun (n : Nat) => ∀ (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _), @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) n → @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) W → ∀ (hcanonicalSep : @LT.lt.{0} Nat _ (Erdos390.Full.ArithmeticModel.physicalBound (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) (Erdos390.Full.ArithmeticModel.physicalBound (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) (hremaining : ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)), @Finset.Nonempty.{0} Nat (@SDiff.sdiff.{0} (Finset.{0} Nat) _ (@Erdos390.Full.PaperGuardCensus.rawCell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) Patterns I (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) cell) (@Erdos390.Full.PaperGuardCensus.Ledger.guards (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) Cprom Cbank (G (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))))), @Eq.{1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _) (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B) (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ Patterns I (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) Cprom Cbank (G (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) hcanonicalSep hremaining) → ∀ (R : Erdos390.WholePaper.BankPaperRealization (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))))) (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R depth)) (T : @Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (qTilde : Real), @Eq.{1} Real qTilde (@Erdos390.WholePaper.bankPaperCanonicalGuardedSmoothBaseMass c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R depth) R certificate deltaStar (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) betaAct) → ∀ (hprime : ∀ (p : Nat), @Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ P p → Nat.Prime p) (Rhead : Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) (Kphysical : Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget I) (hlo : ∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign), @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B) sign) (Erdos390.Full.ArithmeticModel.physicalBound (I.lower sign) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) (hhi : ∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign), @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B) sign) (Erdos390.Full.ArithmeticModel.physicalBound (I.upper sign) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))), @Eq.{1} (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) T (@Erdos390.Full.PaperBridgeFit.BridgeData.barycentricTargetOfPaperData.{u_1} P Band _ _ B I hlo hhi Rhead Kphysical) → @Eq.{1} Real qTilde (@Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.activeMass P Rhead) → @Eq.{1} (Erdos390.Full.PaperHeadSimplex.Tag P → Erdos390.Full.HeadPattern.Pattern) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.pattern.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.Full.PaperHeadSimplex.pattern P hprime (@Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.exponent P Rhead)) → @HasSubset.Subset.{0} (Finset.{0} Nat) _ (Erdos390.WholePaper.primesUpTo (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) P → @Erdos390.Full.PaperBridgeFit.StructuredSampleData.HeadPatternsSeparated.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B) → (∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) (I.lower sign)) → (∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Real _ (I.upper sign) (@OfNat.ofNat.{0} Real (nat_lit 2) _)) → (∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Nat _ (Erdos390.Full.ArithmeticModel.physicalBound (I.upper sign) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) (@HSub.hSub.{0, 0, 0} Nat Nat Nat _ (@HMul.hMul.{0, 0, 0} Nat Nat Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 2) _) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))))) → @LE.le.{0} Nat _ (@HMul.hMul.{0, 0, 0} Nat Nat Nat _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) → (∀ (m : @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)), Not (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardSet c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R depth) R certificate deltaStar) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B) m))) → (∀ (p : @Subtype.{1} Nat fun (p : Nat) => @Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ P p), @LE.le.{0} Nat _ (@Subtype.val.{1} Nat (fun (p : Nat) => @Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ P p) p) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) → @Eq.{1} Real (@Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.target P Rhead p) (@Nat.cast.{0} Real _ (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat _) Nat (fun (x : Nat) => Nat) _ (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R depth) certificate R (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) R deltaStar)).factorization (@Subtype.val.{1} Nat (fun (p : Nat) => @Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ P p) p)))) → @Dvd.dvd.{0} Nat _ (@Erdos390.WholePaper.BankPaperRealization.selectorTailCharge (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) R deltaStar)) (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)))) R depth) certificate) → @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt.{u_1} P Band _ _ B c depth (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) R certificate (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B))) R deltaStar) T deltaStar betaProt (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band _ _ _ _ B c K0 betaProt betaAct) (@HAdd.hAdd.{0, 0, 0} Real Real Real _ betaProt betaAct) qTilde) (@Filter.atTop.{0} Nat _)

noncomputable def Erdos390.RemainingAnalyticGoal004_015 : Prop :=
∀ (W K : Nat) {c r0 deltaStar : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r0 →
      @LT.lt.{0} Real Real.instLT r0
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            deltaStar →
          @LT.lt.{0} Real Real.instLT deltaStar
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 18)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 18) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))))) →
            @LT.lt.{0} Real Real.instLT
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 80)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78)))))))
                    Erdos390.WholePaper.tangentSelbergCanonicalMainConstant)
                  deltaStar)
                (Erdos390.WholePaper.tangentPaperHeadGap W r0) →
              @Filter.Eventually.{0} Nat
                (fun (n : Nat) =>
                  ∀ (depth : Nat) (left right : Nat → Nat) (changed : Finset.{0} Nat)
                    (R :
                      Erdos390.WholePaper.BankPaperRealization n
                        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
                    (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n left right changed)
                    (fixedExceptional : Finset.{0} Nat) {Band : Type u_1} [inst : Fintype.{u_1} Band]
                    [inst_1 : DecidableEq.{u_1 + 1} Band] (lastCell : Band → Nat)
                    (residual : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Real)
                    (bandOf : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Band)
                    (cellIndex : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Nat) (L sigma : Real),
                    @HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat) fixedExceptional
                        (@Finset.Ioc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                          (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n))) →
                      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) depth)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            W →
                          @LT.lt.{0} Nat instLTNat (Erdos390.Full.ArithmeticModel.yNat n)
                              (Erdos390.WholePaper.centralAnchorCutoff depth n) →
                            @Erdos390.WholePaper.TangentRatioCellGeometry.{0, u_1}
                                (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                (@Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel n W) bandOf cellIndex r0 →
                              And
                                (∀
                                  (request :
                                    @Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest n W
                                      (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                        (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                        (@Finset.Subtype.fintype.{0} Nat (Erdos390.Full.ArithmeticModel.primeBand n W))
                                        inst inst_1 lastCell residual bandOf cellIndex)
                                      L sigma),
                                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                    (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard n W
                                      (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                        (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                        (@Finset.Subtype.fintype.{0} Nat (Erdos390.Full.ArithmeticModel.primeBand n W))
                                        inst inst_1 lastCell residual bandOf cellIndex)
                                      L sigma (Erdos390.WholePaper.tangentPaperCleanListDensity W r0) request))
                                (And
                                  (∀
                                    (request :
                                      @Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest n W
                                        (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                          (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                          (@Finset.Subtype.fintype.{0} Nat
                                            (Erdos390.Full.ArithmeticModel.primeBand n W))
                                          inst inst_1 lastCell residual bandOf cellIndex)
                                        L sigma),
                                    @LE.le.{0} Nat instLENat
                                      (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard n W
                                        (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                          (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                          (@Finset.Subtype.fintype.{0} Nat
                                            (Erdos390.Full.ArithmeticModel.primeBand n W))
                                          inst inst_1 lastCell residual bandOf cellIndex)
                                        L sigma (Erdos390.WholePaper.tangentPaperCleanListDensity W r0) request)
                                      (@Finset.card.{0} Nat
                                        (@Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0}
                                          (Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                            (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W))
                                          (@Erdos390.WholePaper.tangentPositiveFlowEdges.{0}
                                            (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                            (@Finset.Subtype.fintype.{0} Nat
                                              (Erdos390.Full.ArithmeticModel.primeBand n W))
                                            (fun (a b : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) =>
                                              @Subtype.instDecidableEq.{1} Nat
                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  (Erdos390.Full.ArithmeticModel.primeBand n W))
                                                instDecidableEqNat a b)
                                            (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                              (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                              (@Finset.Subtype.fintype.{0} Nat
                                                (Erdos390.Full.ArithmeticModel.primeBand n W))
                                              inst inst_1 lastCell residual bandOf cellIndex))
                                          (@Erdos390.WholePaper.tangentStarEdgeSource.{0}
                                            (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                            (@Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel n W))
                                          (@Erdos390.WholePaper.tangentStarEdgeTarget.{0}
                                            (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                            (@Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel n W))
                                          L sigma
                                          (fun
                                              (edge :
                                                Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                                  (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                            @Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                              (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                              (@Finset.Subtype.fintype.{0} Nat
                                                (Erdos390.Full.ArithmeticModel.primeBand n W))
                                              inst inst_1 lastCell residual bandOf cellIndex
                                              (@Prod.fst.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                                (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) edge)
                                              (@Prod.snd.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                                (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) edge))
                                          n K (Erdos390.WholePaper.upperTailLength c n)
                                          (Erdos390.WholePaper.roughHeadModulus W)
                                          (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                                          (Erdos390.Full.ArithmeticModel.yNat n)
                                          (@Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows n
                                            (Erdos390.WholePaper.upperEndpoint n
                                              (Erdos390.WholePaper.upperTailLength c n))
                                            R)
                                          (@Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet c
                                            depth n
                                            (Erdos390.WholePaper.upperEndpoint n
                                              (Erdos390.WholePaper.upperTailLength c n))
                                            left right changed R certificate fixedExceptional)
                                          request)))
                                  (∀
                                    (request :
                                      @Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest n W
                                        (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                          (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                          (@Finset.Subtype.fintype.{0} Nat
                                            (Erdos390.Full.ArithmeticModel.primeBand n W))
                                          inst inst_1 lastCell residual bandOf cellIndex)
                                        L sigma)
                                    (side : Erdos390.WholePaper.TangentEndpointSide),
                                    @LE.le.{0} Real Real.instLE
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (Erdos390.WholePaper.tangentPaperCleanListDensity W r0)
                                        (@Nat.cast.{0} Real Real.instNatCast n))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@Nat.cast.{0} Real Real.instNatCast
                                          (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard n W
                                            (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                              (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                              (@Finset.Subtype.fintype.{0} Nat
                                                (Erdos390.Full.ArithmeticModel.primeBand n W))
                                              inst inst_1 lastCell residual bandOf cellIndex)
                                            L sigma (Erdos390.WholePaper.tangentPaperCleanListDensity W r0) request))
                                        (@Nat.cast.{0} Real Real.instNatCast
                                          (@Erdos390.WholePaper.tangentEndpointLabel.{0}
                                            (@Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest n W
                                              (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                                (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                                (@Finset.Subtype.fintype.{0} Nat
                                                  (Erdos390.Full.ArithmeticModel.primeBand n W))
                                                inst inst_1 lastCell residual bandOf cellIndex)
                                              L sigma)
                                            (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource n W
                                              (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                                (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                                (@Finset.Subtype.fintype.{0} Nat
                                                  (Erdos390.Full.ArithmeticModel.primeBand n W))
                                                inst inst_1 lastCell residual bandOf cellIndex)
                                              L sigma)
                                            (@Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget n W
                                              (@Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1}
                                                (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) Band
                                                (@Finset.Subtype.fintype.{0} Nat
                                                  (Erdos390.Full.ArithmeticModel.primeBand n W))
                                                inst inst_1 lastCell residual bandOf cellIndex)
                                              L sigma)
                                            side request))))))
                (@Filter.atTop.{0} Nat Nat.instPreorder)

noncomputable def Erdos390.RemainingAnalyticGoal004_016 : Prop :=
∀ (W K0 : Nat) {c deltaStar betaProt betaAct sigma : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      LT.lt.{0} (0 : Real) betaAct →
        LE.le.{0} sigma betaProt →
          ∀ᶠ (n : Nat) in Filter.atTop.{0},
            ∀ (depth : Nat)
              (R :
                Erdos390.WholePaper.BankPaperRealization n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
              (certificate :
                Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
                  (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
                  (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                  (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth)),
              LE.le.{0} (Erdos390.WholePaper.centralAnchorCutoffThreshold depth) n →
                LT.lt.{0} (Erdos390.Full.ArithmeticModel.yNat n) (Erdos390.WholePaper.centralAnchorCutoff depth n) →
                  Erdos390.WholePaper.BankPaperRealization.RoughCanonicalBalancedNonsmoothBounds R certificate deltaStar
                    W K0 betaProt betaAct sigma

noncomputable def Erdos390.RemainingAnalyticGoal004_017 : Prop :=
∀ (W K0 : Nat) {c beta deltaStar : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        ∀ (depth : Nat)
          (R :
            Erdos390.WholePaper.BankPaperRealization n
              (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
          (certificate :
            Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
              (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
              (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
              (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth)),
          LE.le.{0} (Erdos390.WholePaper.centralAnchorCutoffThreshold depth) n →
            LT.lt.{0} (Erdos390.Full.ArithmeticModel.yNat n) (Erdos390.WholePaper.centralAnchorCutoff depth n) →
              ∀ (label : Nat),
                Membership.mem.{0, 0}
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalActiveRawCorrectionLabels n
                      (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) deltaStar)
                    label →
                  LE.le.{0}
                    (abs.{0}
                      (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedPostchargeCorrectionDensity R
                        certificate deltaStar W (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) label
                        (Erdos390.WholePaper.roughHeadBalancedAlpha W n (Erdos390.WholePaper.upperTailLength c n)
                          (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta (Erdos390.Full.Scale.L n))
                        beta (Erdos390.Full.Scale.L n)))
                    (HDiv.hDiv.{0, 0, 0}
                      (Erdos390.WholePaper.BankPaperRealization.roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
                        W K0 c beta)
                      (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))))

noncomputable def Erdos390.RemainingAnalyticGoal004_018 : Prop :=
∀ (W K0 : Nat) {c beta deltaStar : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalUniformRawRowCorrectionDensityBound W n
          (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) deltaStar
          (Erdos390.WholePaper.roughHeadBalancedAlpha W n (Erdos390.WholePaper.upperTailLength c n)
            (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta (Erdos390.Full.Scale.L n))
          beta (Erdos390.Full.Scale.L n)
          (HDiv.hDiv.{0, 0, 0}
            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalUniformRawRowCorrectionDensityConstant W K0 c beta)
            (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))))

noncomputable def Erdos390.RemainingAnalyticGoal004_019 : Prop :=
∀ {c : Real}, @LT.lt.{0} Real _ Erdos390.WholePaper.C0 c → ∀ (depth : Nat), @LE.le.{0} Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 201) _) depth → @Exists.{1} Nat fun (W0 : Nat) => ∀ (W : Nat), @LE.le.{0} Nat _ W0 W → @LE.le.{0} Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 2) _) W → @LE.le.{0} Nat _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ (@HMul.hMul.{0, 0, 0} Nat Nat Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 2) _) depth) (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) W → @LE.le.{0} Nat _ Erdos390.Full.PrimeBandQuadrature.fullReciprocalSumUniformCutoff W → @LE.le.{0} Nat _ Erdos390.Full.RegularMeshPrimeCutoffs.canonicalActualMomentCutoff W → ∀ (r0 deltaStar : Real), @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) r0 → @LT.lt.{0} Real _ r0 (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@OfNat.ofNat.{0} Real (nat_lit 3) _) (@OfNat.ofNat.{0} Real (nat_lit 2) _)) → Erdos390.WholePaper.IsPaperCombinedTangentDeltaStar c W r0 deltaStar → Erdos390.WholePaper.BankPaperCombinedChargeTerminalAtDepth c deltaStar depth → Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion c depth W r0 deltaStar

noncomputable def Erdos390.RemainingAnalyticGoal004_020 : Prop :=
∀ {c : Real}, @LT.lt.{0} Real _ Erdos390.WholePaper.C0 c → @Exists.{1} Nat fun (depth : Nat) => @Exists.{1} Nat fun (W : Nat) => @Exists.{1} Real fun (r0 : Real) => @Exists.{1} Real fun (deltaStar : Real) => And (@LE.le.{0} Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 201) _) depth) (And (@LE.le.{0} Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 2) _) W) (And (@LE.le.{0} Nat _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ (@HMul.hMul.{0, 0, 0} Nat Nat Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 2) _) depth) (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) W) (And (@LE.le.{0} Nat _ Erdos390.Full.PrimeBandQuadrature.fullReciprocalSumUniformCutoff W) (And (@LE.le.{0} Nat _ Erdos390.Full.RegularMeshPrimeCutoffs.canonicalActualMomentCutoff W) (And (@LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) r0) (And (@LT.lt.{0} Real _ r0 (@HDiv.hDiv.{0, 0, 0} Real Real Real _ (@OfNat.ofNat.{0} Real (nat_lit 3) _) (@OfNat.ofNat.{0} Real (nat_lit 2) _))) (And (Erdos390.WholePaper.IsPaperCombinedTangentDeltaStar c W r0 deltaStar) (And (Erdos390.WholePaper.BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) (Erdos390.WholePaper.BankPaperCanonicalDistributedSectionNineTerminalAtDepth c deltaStar depth)))))))))


