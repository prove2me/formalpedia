-- Prove2me | Definitions.Def_erdos390_remaining_analytic_propositions_001
-- name    : erdos390_remaining_analytic_propositions_001
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T16:43:10.115654+00:00
-- url     : https://prove2.me/theorems/5731d1f3-dcf9-4c9a-8bae-ba6aba591b90
-- title:
--   Analytic construction propositions, part 1
-- statement:
--   Named propositions for the remaining analytic and finite construction estimates in the Erdős 390 central-anchor proof. Each name expands to the complete quantified statement, including every hypothesis and universe parameter. These definitions introduce no assertion of the propositions; their proofs are submitted separately. This part includes the following source declarations: exists_boxIndependent_fixedFiniteMixture_primePower_transfer, sigmaMixture_primePowerTransferBounds_of_common_profiles, exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos, exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate, exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate, boxIndependent_canonicalRaw_actualWeightedRow, boxIndependent_canonicalRaw_fullSharp, boxIndependent_canonicalRaw_nonstepPower_inputs, canonical_proposition87, exists_boxIndependent_actual_component_signed_profiles, exists_boxIndependent_actual_medium_signed_profiles, exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse, exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse, exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice, exists_cutoff_eventually_canonical_ordinary_perturbation_rows.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_nonstep_certificate
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_source_bank_interface
import Mathlib
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_MediumPNT
universe u_1 u_2 u_3
set_option maxRecDepth 10000
set_option maxHeartbeats 0



noncomputable def Erdos390.RemainingAnalyticGoal001_001 : Prop :=
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] (H : Cell → Erdos390.Full.HeadPattern.Pattern) (A C : Cell → Real) (Cmax : Real),
  (∀ (c : Cell), LT.lt.{0} (0 : Real) (A c)) →
    (∀ (c : Cell), LT.lt.{0} (A c) (C c)) →
      (∀ (c : Cell), LT.lt.{0} (0 : Real) (C c)) →
        LT.lt.{0} (0 : Real) Cmax →
          ∀ (hC_le : ∀ (c : Cell), LE.le.{0} (C c) Cmax),
            And (LT.lt.{0} (0 : Real) Erdos390.Full.FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant)
              (∀ (W : Nat),
                LT.lt.{0} (1 : Nat) W →
                  (∀ (c : Cell) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (H c)) p → LE.le.{0} p W) →
                    ∀ (B : Real),
                      LE.le.{0} (0 : Real) B →
                        ∃ (epsilon_BW : Nat → Real),
                          And (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon_BW n))
                            (And (Filter.Tendsto.{0, 0} epsilon_BW Filter.atTop.{0} (nhds.{0} (0 : Real)))
                              (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon_BW n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                                (∃ (N₀ : Nat),
                                  ∀ {n : Nat} (eta : Nat → Real),
                                    LE.le.{0} N₀ n →
                                      (∀ (z : Nat), Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) z → LE.le.{0} (abs.{0} (eta z)) B) →
                                        let S : (c : Cell) → Finset.{0} Nat := fun (c : Cell) =>
                                          Erdos390.Full.StructuredCells.structuredCell (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n) (Erdos390.Full.ArithmeticModel.physicalBound (C c) n)
                                            (Erdos390.Full.ArithmeticModel.yNat n);
                                        And (∀ (c : Cell), Finset.Nonempty.{0} (S c))
                                          (∀ (hS : ∀ (c : Cell), Finset.Nonempty.{0} (S c)) (weight : Erdos390.Full.FiniteProbability.{u_1} Cell),
                                            have law :
                                              (c : Cell) →
                                                Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{0}
                                                  (↥(Erdos390.Full.StructuredCells.structuredCell (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n)
                                                      (Erdos390.Full.ArithmeticModel.physicalBound (C c) n) (Erdos390.Full.ArithmeticModel.yNat n)))
                                                  (Erdos390.Full.ArithmeticModel.physicalBound Cmax n) :=
                                              fun (c : Cell) =>
                                              Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.widen.{0}
                                                (Erdos390.Full.StructuredCellValuationLaw.valuationTilt (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n)
                                                  (Erdos390.Full.ArithmeticModel.physicalBound (C c) n) (Erdos390.Full.ArithmeticModel.yNat n) (hS c) (Erdos390.Full.ArithmeticModel.primeBand n W) eta
                                                  (Erdos390.Full.Scale.L n))
                                                (Erdos390.Full.FixedFiniteMixtureFullUniform.physicalBound_mono (hC_le c) n);
                                            Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_1}
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_1, 0} (Omega := fun (c : Cell) =>
                                                ↥(Erdos390.Full.StructuredCells.structuredCell (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n)
                                                    (Erdos390.Full.ArithmeticModel.physicalBound (C c) n) (Erdos390.Full.ArithmeticModel.yNat n)))
                                                weight law)
                                              n W Erdos390.Full.FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant (epsilon_BW n))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_002 : Prop :=
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2} [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] {M : Nat} {C_K epsilon G₀ k Gf Tlin Tquad Tdiag Trow : Real},
  (∀ (x z : Real),
      LE.le.{0} (0 : Real) x →
        LE.le.{0} (0 : Real) z →
          LE.le.{0} (HAdd.hAdd.{0, 0, 0} x z) (4 : Real) →
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0} (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile (HAdd.hAdd.{0, 0, 0} x z))
                  (HMul.hMul.{0, 0, 0} (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile x) (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile z))))
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C_K x) z)) →
    LE.le.{0} (0 : Real) C_K →
      LE.le.{0} (0 : Real) epsilon →
        LE.le.{0} (0 : Real) G₀ →
          LE.le.{0} (0 : Real) k →
            LE.le.{0} (0 : Real) Gf →
              LE.le.{0} (0 : Real) Tlin →
                LE.le.{0} (0 : Real) Tquad →
                  LE.le.{0} (0 : Real) Tdiag →
                    LE.le.{0} (0 : Real) Trow →
                      ∀ (weight : Erdos390.Full.FiniteProbability.{u_1} Cell) (law : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_2} (Omega c) M) {n W : Nat},
                        LT.lt.{0} (1 : Nat) n →
                          LT.lt.{0} (1 : Nat) W →
                            (∀ (c : Cell) (p : Nat),
                                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                  ∀ (q : Nat),
                                    Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                                      ∀ (r s : Nat),
                                        LE.le.{0} (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s) (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                                          LE.le.{0}
                                            (abs.{0}
                                              (HSub.hSub.{0, 0, 0}
                                                (Erdos390.Full.FiniteProbability.expect.{u_2} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c))
                                                  fun (omega : Omega c) =>
                                                  Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s)
                                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                                                (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s))))
                                            (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperPrimePowerChamberError.pairProbabilityScale epsilon G₀ k)
                                              (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q r s))) →
                              (∀ (c : Cell) (p : Nat),
                                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                    ∀ (r : Nat),
                                      LE.le.{0} (HPow.hPow.{0, 0, 0} p r) (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                                        LE.le.{0}
                                          (abs.{0}
                                            (HSub.hSub.{0, 0, 0}
                                              (Erdos390.Full.FiniteProbability.expect.{u_2} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c)) fun (omega : Omega c) =>
                                                Erdos390.Full.ArithmeticModel.divInd (HPow.hPow.{0, 0, 0} p r) (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                                              (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (HPow.hPow.{0, 0, 0} p r))))
                                          (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperPrimePowerChamberError.pairProbabilityScale epsilon G₀ k)
                                            (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p r))) →
                                (∀ (c : Cell) (D : Nat),
                                    LT.lt.{0} (0 : Nat) D →
                                      LE.le.{0}
                                        (Erdos390.Full.FiniteProbability.expect.{u_2} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c)) fun (omega : Omega c) =>
                                          Erdos390.Full.ArithmeticModel.divInd D (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                                        (HDiv.hDiv.{0, 0, 0} Gf (↑D : Real))) →
                                  (∀ (p : Nat),
                                      Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                        ∀ (q : Nat),
                                          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                            LE.le.{0}
                                              (∑ r ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                Erdos390.Full.PaperPrimePowerFourDisplays.eJI Gf n p q r)
                                              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Tlin (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)) (2 : Nat)))
                                                (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑q : Real)))) →
                                    (∀ (p : Nat),
                                        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                          ∀ (q : Nat),
                                            Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                              LE.le.{0}
                                                (∑ s ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                                  Erdos390.Full.PaperPrimePowerFourDisplays.eIJ Gf n p q s)
                                                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Tlin (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)))
                                                  (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑q : Real)) (2 : Nat)))) →
                                      (∀ (p : Nat),
                                          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                            ∀ (q : Nat),
                                              Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                                LE.le.{0}
                                                  (∑ r ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                    ∑ s ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                                      Erdos390.Full.PaperPrimePowerFourDisplays.eJJ Gf n p q r s)
                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Tquad (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)) (2 : Nat)))
                                                    (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑q : Real)) (2 : Nat)))) →
                                        (∀ (p : Nat),
                                            Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                              LE.le.{0}
                                                (∑ r ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                  HMul.hMul.{0, 0, 0} (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)) : Real)
                                                    (Erdos390.Full.PaperPrimePowerFourDisplays.eD Gf n p r))
                                                (HMul.hMul.{0, 0, 0} Tdiag (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)) (2 : Nat)))) →
                                          (∀ (p : Nat),
                                              Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                                LE.le.{0}
                                                  (HMul.hMul.{0, 0, 0} (↑p : Real)
                                                    (HAdd.hAdd.{0, 0, 0}
                                                      (∑ q ∈ Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p,
                                                        HAdd.hAdd.{0, 0, 0}
                                                          (HAdd.hAdd.{0, 0, 0} (α := Real)
                                                            (∑ r ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                              Erdos390.Full.PaperPrimePowerFourDisplays.eJI Gf n p q r)
                                                            (∑ s ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                                              Erdos390.Full.PaperPrimePowerFourDisplays.eIJ Gf n p q s))
                                                          (∑ r ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                            ∑ s ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                                              Erdos390.Full.PaperPrimePowerFourDisplays.eJJ Gf n p q r s))
                                                      (HMul.hMul.{0, 0, 0} (3 : Real)
                                                        (∑ r ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                          HMul.hMul.{0, 0, 0} (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)) : Real)
                                                            (Erdos390.Full.PaperPrimePowerFourDisplays.eD Gf n p r)))))
                                                  Trow) →
                                            LE.le.{0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W) (HMul.hMul.{0, 0, 0} (2 : Real) (Real.log (4 : Real))) →
                                              Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{max u_2 u_1}
                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_1, u_2} (Omega := Omega) weight law) n W
                                                (Erdos390.Full.PaperPrimePowerLemma75.paperPrimePowerConstant C_K)
                                                (Erdos390.Full.PaperPrimePowerGenericAggregation.genericAggregationRemainder
                                                  (Erdos390.Full.PaperPrimePowerFourDisplays.primePowerChamberRemainder epsilon G₀ k) Tlin Tquad Tdiag Trow n W)

noncomputable def Erdos390.RemainingAnalyticGoal001_003 : Prop :=
∀ {Cell : Type u_1} [Fintype.{u_1} Cell] (H : Cell → Erdos390.Full.HeadPattern.Pattern) (A C : Cell → Real) (Cmax : Real),
  (∀ (c : Cell), LT.lt.{0} (0 : Real) (A c)) →
    (∀ (c : Cell), LT.lt.{0} (A c) (C c)) →
      (∀ (c : Cell), LT.lt.{0} (0 : Real) (C c)) →
        ∀ (hC_le : ∀ (c : Cell), LE.le.{0} (C c) Cmax) (W : Nat),
          LT.lt.{0} (1 : Nat) W →
            (∀ (c : Cell) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (H c)) p → LE.le.{0} p W) →
              ∀ (B : Real),
                LE.le.{0} (0 : Real) B →
                  ∃ (signedError : Nat → Real),
                    And (∀ (n : Nat), LE.le.{0} (0 : Real) (signedError n))
                      (And (Filter.Tendsto.{0, 0} signedError Filter.atTop.{0} (nhds.{0} (0 : Real)))
                        (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (signedError n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                          (∃ (N₀ : Nat),
                            ∀ {n : Nat} (eta : Nat → Real),
                              LE.le.{0} N₀ n →
                                (∀ (z : Nat), Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) z → LE.le.{0} (abs.{0} (eta z)) B) →
                                  let S : (c : Cell) → Finset.{0} Nat := fun (c : Cell) =>
                                    Erdos390.Full.StructuredCells.structuredCell (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n) (Erdos390.Full.ArithmeticModel.physicalBound (C c) n)
                                      (Erdos390.Full.ArithmeticModel.yNat n);
                                  And (∀ (c : Cell), Finset.Nonempty.{0} (S c))
                                    (∀ (hS : ∀ (c : Cell), Finset.Nonempty.{0} (S c)),
                                      have law :
                                        (c : Cell) →
                                          Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{0}
                                            (↥(Erdos390.Full.StructuredCells.structuredCell (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n)
                                                (Erdos390.Full.ArithmeticModel.physicalBound (C c) n) (Erdos390.Full.ArithmeticModel.yNat n)))
                                            (Erdos390.Full.ArithmeticModel.physicalBound Cmax n) :=
                                        fun (c : Cell) =>
                                        Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.widen.{0}
                                          (Erdos390.Full.StructuredCellValuationLaw.valuationTilt (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n)
                                            (Erdos390.Full.ArithmeticModel.physicalBound (C c) n) (Erdos390.Full.ArithmeticModel.yNat n) (hS c) (Erdos390.Full.ArithmeticModel.primeBand n W) eta
                                            (Erdos390.Full.Scale.L n))
                                          (Erdos390.Full.FixedFiniteMixtureFullUniform.physicalBound_mono (hC_le c) n);
                                      And
                                        (∀ (c : Cell) (p : Nat),
                                          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                            ∀ (q : Nat),
                                              Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                                                ∀ (r s : Nat),
                                                  LE.le.{0} (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s) (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                                                    LE.le.{0}
                                                      (abs.{0}
                                                        (HSub.hSub.{0, 0, 0}
                                                          (Erdos390.Full.FiniteProbability.expect.{0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0} (law c))
                                                            fun
                                                              (omega :
                                                                ↥(Erdos390.Full.StructuredCells.structuredCell (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n)
                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (C c) n) (Erdos390.Full.ArithmeticModel.yNat n))) =>
                                                            Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s)
                                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0} (law c) omega))
                                                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s))))
                                                      (HMul.hMul.{0, 0, 0} (signedError n) (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q r s)))
                                        (∀ (c : Cell) (p : Nat),
                                          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                            LE.le.{0}
                                              (abs.{0}
                                                (HSub.hSub.{0, 0, 0}
                                                  (Erdos390.Full.FiniteProbability.expect.{0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0} (law c))
                                                    fun
                                                      (omega :
                                                        ↥(Erdos390.Full.StructuredCells.structuredCell (H c) (Erdos390.Full.ArithmeticModel.physicalBound (A c) n)
                                                            (Erdos390.Full.ArithmeticModel.physicalBound (C c) n) (Erdos390.Full.ArithmeticModel.yNat n))) =>
                                                    Erdos390.Full.ArithmeticModel.divInd p (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0} (law c) omega))
                                                  (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                                              (HMul.hMul.{0, 0, 0} (signedError n) (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat))))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_004 : Prop :=
∀ (H : Erdos390.Full.HeadPattern.Pattern) {A C : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      LT.lt.{0} (0 : Real) C →
        ∀ (B : Real) (W : Nat),
          LE.le.{0} (0 : Real) B →
            LT.lt.{0} (1 : Nat) W →
              ∃ (epsilon : Nat → Real),
                And (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon n))
                  (And (Filter.Tendsto.{0, 0} epsilon Filter.atTop.{0} (nhds.{0} (0 : Real)))
                    (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                      (And
                        (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon n) (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.Scale.L n)) (2 : Nat))) Filter.atTop.{0}
                          (nhds.{0} (0 : Real)))
                        (∃ (N₀ : Nat),
                          ∀ {n p q r s : Nat} (eta : Nat → Real),
                            LE.le.{0} N₀ n →
                              Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                                  LE.le.{0} (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s) (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                                    Nat.Coprime p (Erdos390.Full.HeadPattern.Pattern.modulus H) →
                                      Nat.Coprime q (Erdos390.Full.HeadPattern.Pattern.modulus H) →
                                        (∀ (z : Nat), Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) z → LE.le.{0} (abs.{0} (eta z)) B) →
                                          have S :=
                                            Erdos390.Full.StructuredCells.structuredCell H (Erdos390.Full.ArithmeticModel.physicalBound A n) (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                              (Erdos390.Full.ArithmeticModel.yNat n);
                                          And (Finset.Nonempty.{0} S)
                                            (∀ (hS : Finset.Nonempty.{0} S),
                                              LE.le.{0}
                                                (abs.{0}
                                                  (HSub.hSub.{0, 0, 0}
                                                    (Erdos390.Full.FiniteProbability.expect.{0}
                                                      (Erdos390.Full.FiniteProbability.exponentialTilt.{0} (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun (m : ↥S) =>
                                                        Erdos390.Full.ValuationScoreDomination.valuationScore (Erdos390.Full.ArithmeticModel.primeBand n W) eta (Erdos390.Full.Scale.L n) (↑m : Nat))
                                                      fun (m : ↥S) => Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s) (↑m : Nat))
                                                    (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s))))
                                                (Erdos390.Full.FullTiltPairChamber.fullPairChamberError H A C B W n p q r s eta epsilon))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_005 : Prop :=
∀ (H : Erdos390.Full.HeadPattern.Pattern) {A C : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      LT.lt.{0} (0 : Real) C →
        ∀ (B : Real) (W : Nat),
          LE.le.{0} (0 : Real) B →
            LT.lt.{0} (1 : Nat) W →
              ∃ (K : Real) (c : Real) (epsilon : (n : Nat) → Real),
                And (LE.le.{0} (0 : Real) K)
                  (And (LT.lt.{0} (0 : Real) c)
                    (And (Eq.{1} epsilon (Erdos390.Full.OmittedTiltMarkedProbability.omittedTiltRemainder K B C c W))
                      (And (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon n))
                        (And (Filter.Tendsto.{0, 0} epsilon Filter.atTop.{0} (nhds.{0} (0 : Real)))
                          (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                            (And
                              (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon n) (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.Scale.L n)) (2 : Nat))) Filter.atTop.{0}
                                (nhds.{0} (0 : Real)))
                              (∃ (N₀ : Nat),
                                ∀ {n D : Nat} (P : Finset.{0} Nat) (eta : Nat → Real),
                                  LE.le.{0} N₀ n →
                                    LT.lt.{0} (0 : Nat) D →
                                      LE.le.{0} D (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                                        Membership.mem.{0, 0} (Nat.smoothNumbers (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (1 : Nat))) D →
                                          Nat.Coprime D (Erdos390.Full.HeadPattern.Pattern.modulus H) →
                                            HasSubset.Subset.{0} P (Erdos390.Full.ArithmeticModel.primeBand n W) →
                                              (∀ (p : Nat), Membership.mem.{0, 0} P p → Nat.Coprime D p) →
                                                (∀ (p : Nat), Membership.mem.{0, 0} P p → LE.le.{0} (abs.{0} (eta p)) B) →
                                                  have S :=
                                                    Erdos390.Full.StructuredCells.structuredCell H (Erdos390.Full.ArithmeticModel.physicalBound A n) (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                                      (Erdos390.Full.ArithmeticModel.yNat n);
                                                  And (Finset.Nonempty.{0} S)
                                                    (∀ (hS : Finset.Nonempty.{0} S),
                                                      LE.le.{0}
                                                        (abs.{0}
                                                          (HSub.hSub.{0, 0, 0}
                                                            (Erdos390.Full.FiniteProbability.expect.{0}
                                                              (Erdos390.Full.FiniteProbability.exponentialTilt.{0} (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun (m : ↥S) =>
                                                                Erdos390.Full.ValuationScoreDomination.valuationScore P eta (Erdos390.Full.Scale.L n) (↑m : Nat))
                                                              fun (m : ↥S) => Erdos390.Full.ArithmeticModel.divInd D (↑m : Nat))
                                                            (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n D)))
                                                        (HDiv.hDiv.{0, 0, 0} (epsilon n) (↑D : Real))))))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_006 : Prop :=
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real),
  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)) →
    (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) Cmax) →
      ∀ (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank),
        And (LT.lt.{0} (0 : Real) Erdos390.Full.FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant)
          (∀ (W : Nat),
            LT.lt.{0} (1 : Nat) W →
              (∀ (h : Head) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (P h)) p → LE.le.{0} p W) →
                ∀ (Acoef : Real),
                  LE.le.{0} (0 : Real) Acoef →
                    ∀ (Aphys : Real),
                      LE.le.{0} (0 : Real) Aphys →
                        ∃ (epsilon75 : Nat → Real),
                          And (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon75 n))
                            (And (Filter.Tendsto.{0, 0} epsilon75 Filter.atTop.{0} (nhds.{0} (0 : Real)))
                              (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon75 n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                                (And
                                  (Filter.Tendsto.{0, 0}
                                    (fun (n : Nat) =>
                                      HMul.hMul.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionRowError
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalPhysicalPowerCorrectionConstant.{u_1} P I Cmax W Acoef) n W)
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient Cmax W)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardPerturbationConstant.{u_1} P I
                                              (HMul.hMul.{0, 0, 0} Acoef (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient Cmax W)))
                                            n))
                                        (Real.log (Erdos390.Full.Scale.L n)))
                                    Filter.atTop.{0} (nhds.{0} (0 : Real)))
                                  (∃ (N₀ : Nat),
                                    ∀ {Band : Type u_2} [inst_3 : Fintype.{u_2} Band] [inst_4 : DecidableEq.{u_2 + 1} Band] (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
                                      (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B),
                                      LE.le.{0} N₀ (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) W →
                                          ∀
                                            (hsep :
                                              LT.lt.{0}
                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                                            (hremaining :
                                              ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                                Finset.Nonempty.{0}
                                                  (SDiff.sdiff.{0}
                                                    (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P I
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) c)
                                                    (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                      (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))),
                                            Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)
                                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} P I (W :=
                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                  (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))) hsep
                                                  hremaining) →
                                              (∀
                                                  (p :
                                                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                                  LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} B xi p)) Acoef) →
                                                LE.le.{0} (abs.{0} (WithLp.ofLp.{max u_1 u_2} xi Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1})) Aphys →
                                                  ∀
                                                    (p :
                                                      Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                                    LE.le.{0}
                                                      (HMul.hMul.{0, 0, 0} (α := Real) (↑(↑p : Nat) : Real)
                                                        (∑ r :
                                                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                                                          abs.{0}
                                                            (HSub.hSub.{0, 0, 0}
                                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) (↑p : Nat) (↑r : Nat))
                                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) (↑p : Nat) (↑r : Nat)))))
                                                      (HAdd.hAdd.{0, 0, 0}
                                                        (HAdd.hAdd.{0, 0, 0}
                                                          (HMul.hMul.{0, 0, 0} Erdos390.Full.FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
                                                            (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                              (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) : Real)))
                                                          (epsilon75 (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                                                        (HAdd.hAdd.{0, 0, 0}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionRowError
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalPhysicalPowerCorrectionConstant.{u_1} P I Cmax W Acoef)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank
                                                            (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient Cmax W)
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardPerturbationConstant.{u_1} P I
                                                              (HMul.hMul.{0, 0, 0} Acoef (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient Cmax W)))
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_007 : Prop :=
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real),
  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)) →
    (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) Cmax) →
      ∀ (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank),
        And (LT.lt.{0} (0 : Real) Erdos390.Full.FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant)
          (∀ (W : Nat),
            LT.lt.{0} (1 : Nat) W →
              (∀ (h : Head) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (P h)) p → LE.le.{0} p W) →
                ∀ (Acoef : Real),
                  LE.le.{0} (0 : Real) Acoef →
                    ∀ (Aphys : Real),
                      LE.le.{0} (0 : Real) Aphys →
                        ∃ (epsilon75 : Nat → Real),
                          And (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon75 n))
                            (And (Filter.Tendsto.{0, 0} epsilon75 Filter.atTop.{0} (nhds.{0} (0 : Real)))
                              (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon75 n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                                (And
                                  (Filter.Tendsto.{0, 0}
                                    (fun (n : Nat) =>
                                      HMul.hMul.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionRowError
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalPhysicalPowerCorrectionConstant.{u_1} P I Cmax W Acoef) n W)
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient Cmax W)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardPerturbationConstant.{u_1} P I
                                              (HMul.hMul.{0, 0, 0} Acoef (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient Cmax W)))
                                            n))
                                        (Real.log (Erdos390.Full.Scale.L n)))
                                    Filter.atTop.{0} (nhds.{0} (0 : Real)))
                                  (∃ (N₀ : Nat),
                                    ∀ {Band : Type u_3} [inst_3 : Fintype.{u_3} Band] [inst_4 : DecidableEq.{u_3 + 1} Band] (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_3} Head Band)
                                      (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_3} B),
                                      LE.le.{0} N₀ (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) →
                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) W →
                                          ∀
                                            (hsep :
                                              LT.lt.{0}
                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))))
                                            (hremaining :
                                              ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                                Finset.Nonempty.{0}
                                                  (SDiff.sdiff.{0}
                                                    (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P I
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) c)
                                                    (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                      (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))))),
                                            Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)
                                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} P I (W :=
                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                  (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))) hsep
                                                  hremaining) →
                                              (∀
                                                  (p :
                                                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))),
                                                  LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_3} B xi p)) Acoef) →
                                                LE.le.{0} (abs.{0} (WithLp.ofLp.{max u_1 u_3} xi Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_3, u_1})) Aphys →
                                                  ∀ (q : Band → Real),
                                                    (∀ (j : Band), LE.le.{0} (abs.{0} (q j)) (1 : Real)) →
                                                      ∀ (i : Band),
                                                        LE.le.{0}
                                                          (abs.{0}
                                                            (HSub.hSub.{0, 0, 0}
                                                              (Erdos390.Full.PrimePowerSharpBandTransfer.fullSharpRow.{u_1, u_3}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_3} B xi)
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_3} B) q i)
                                                              (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeSharpRow.{u_1, u_3}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_3} B xi)
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_3} B) q i)))
                                                          (HAdd.hAdd.{0, 0, 0}
                                                            (HAdd.hAdd.{0, 0, 0}
                                                              (HMul.hMul.{0, 0, 0}
                                                                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 : Real) Erdos390.Full.FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant)
                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                    (Erdos390.Full.PrimeSums.bandTReciprocalSum
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                                    (1 : Real)))
                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) :
                                                                    Real)))
                                                              (HMul.hMul.{0, 0, 0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0} (3 : Real)
                                                                    (epsilon75
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))))
                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                    (HDiv.hDiv.{0, 0, 0}
                                                                      (Erdos390.Full.PrimeSums.bandTReciprocalSum
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_3} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_3} B) i))
                                                                    (1 : Real)))
                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) :
                                                                    Real))))
                                                            (HDiv.hDiv.{0, 0, 0}
                                                              (HAdd.hAdd.{0, 0, 0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionRowError
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalPhysicalPowerCorrectionConstant.{u_1} P I Cmax W Acoef)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank
                                                                  (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient Cmax W)
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardPerturbationConstant.{u_1} P I
                                                                    (HMul.hMul.{0, 0, 0} Acoef (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient Cmax W)))
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))))
                                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_3} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_3} B) i))))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_008 : Prop :=
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real),
  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)) →
    ∀ (hupperMax : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) Cmax) (Cprom Cbank : Nat)
      (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank),
      And (LT.lt.{0} (0 : Real) Erdos390.Full.FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant)
        (∀ (W : Nat),
          LT.lt.{0} (1 : Nat) W →
            (∀ (h : Head) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (P h)) p → LE.le.{0} p W) →
              ∀ (Acoef : Real),
                LE.le.{0} (0 : Real) Acoef →
                  ∀ (Aphys : Real),
                    LE.le.{0} (0 : Real) Aphys →
                      ∃ (epsilon75 : Nat → Real),
                        And (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon75 n))
                          (And (Filter.Tendsto.{0, 0} epsilon75 Filter.atTop.{0} (nhds.{0} (0 : Real)))
                            (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon75 n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                              (And
                                (Filter.Tendsto.{0, 0}
                                  (fun (n : Nat) =>
                                    HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalNonstepPowerCorrection.{u_1} P I Cmax Cprom Cbank W Acoef Aphys n)
                                      (Real.log (Erdos390.Full.Scale.L n)))
                                  Filter.atTop.{0} (nhds.{0} (0 : Real)))
                                (∃ (N₀ : Nat),
                                  ∀ {Band : Type u_2} [inst_3 : Fintype.{u_2} Band] [inst_4 : DecidableEq.{u_2 + 1} Band] (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
                                    (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B),
                                    LE.le.{0} N₀ (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) W →
                                        ∀
                                          (hsep :
                                            LT.lt.{0}
                                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                                          (hremaining :
                                            ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                              Finset.Nonempty.{0}
                                                (SDiff.sdiff.{0}
                                                  (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P I
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) c)
                                                  (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                    (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))),
                                          Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)
                                              (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} P I (W :=
                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))) hsep
                                                hremaining) →
                                            (∀
                                                (p :
                                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                                LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} B xi p)) Acoef) →
                                              LE.le.{0} (abs.{0} (WithLp.ofLp.{max u_1 u_2} xi Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1})) Aphys →
                                                have hS :
                                                  ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                                    Finset.Nonempty.{0}
                                                      (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P I
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) c) :=
                                                  fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) => Finset.Nonempty.mono.{0} Finset.sdiff_subset.{0} (hremaining c);
                                                have referenceLaw := Erdos390.Full.PaperBridgeFit.BridgeData.canonicalRawMediumReferenceLaw.{u_1, u_2} B P I Cmax xi hupperMax hS;
                                                And
                                                  (Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_1} referenceLaw
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                    Erdos390.Full.FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
                                                    (epsilon75 (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                                                  (∀
                                                    (p :
                                                      Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                                    LE.le.{0}
                                                      (HMul.hMul.{0, 0, 0} (α := Real) (↑(↑p : Nat) : Real)
                                                        (∑ q :
                                                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                                                          abs.{0}
                                                            (HSub.hSub.{0, 0, 0}
                                                              (HSub.hSub.{0, 0, 0}
                                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) (↑p : Nat) (↑q : Nat))
                                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) (↑p : Nat) (↑q : Nat)))
                                                              (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1} referenceLaw (↑p : Nat) (↑q : Nat))
                                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1} referenceLaw (↑p : Nat) (↑q : Nat))))))
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalNonstepPowerCorrection.{u_1} P I Cmax Cprom Cbank W Acoef Aphys
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_009 : Prop :=
∀ (cMesh : Real) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real) (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank),
  Erdos390.Full.PaperBridgeFit.CanonicalProposition87Statement.{u_1, u_2} cMesh I U Cprom Cbank ledger

noncomputable def Erdos390.RemainingAnalyticGoal001_010 : Prop :=
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (Phead : Head → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real),
  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)) →
    (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) Cmax) →
      ∀ (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W : Nat),
        LT.lt.{0} (1 : Nat) W →
          (∀ (h : Head) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Phead h)) p → LE.le.{0} p W) →
            ∀ (Acoef Aphys : Real),
              LE.le.{0} (0 : Real) Acoef →
                LE.le.{0} (0 : Real) Aphys →
                  ∃ (profileError : Nat → Real),
                    And (∀ (n : Nat), LE.le.{0} (0 : Real) (profileError n))
                      (And (Filter.Tendsto.{0, 0} profileError Filter.atTop.{0} (nhds.{0} (0 : Real)))
                        (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (profileError n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                          (∃ (N₀ : Nat),
                            ∀ {Band : Type u_3} [inst_3 : Fintype.{u_3} Band] [inst_4 : DecidableEq.{u_3 + 1} Band] (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_3} Head Band)
                              (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_3} B),
                              LE.le.{0} N₀ (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) →
                                Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.pattern.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) Phead →
                                  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B) sigma)
                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))) →
                                    (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B) sigma)
                                          (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))) →
                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.guards.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                          (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                            (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))) →
                                        (∀
                                            (p :
                                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))),
                                            LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_3} B xi p)) Acoef) →
                                          LE.le.{0} (abs.{0} (WithLp.ofLp.{max u_1 u_3} xi Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_3, u_1})) Aphys →
                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) W →
                                              And
                                                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                                  Membership.mem.{0, 0}
                                                      (Erdos390.Full.ArithmeticModel.primeBand
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                      p →
                                                    ∀ (q : Nat),
                                                      Membership.mem.{0, 0}
                                                          (Finset.erase.{0}
                                                            (Erdos390.Full.ArithmeticModel.primeBand
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                            p)
                                                          q →
                                                        LE.le.{0}
                                                          (abs.{0}
                                                            (HSub.hSub.{0, 0, 0}
                                                              (Erdos390.Full.FiniteProbability.expect.{0}
                                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_3} B xi c))
                                                                fun
                                                                  (m :
                                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)
                                                                      c) =>
                                                                Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat))
                                                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_3} B xi c) m))
                                                              (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                                (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                                                          (HMul.hMul.{0, 0, 0}
                                                            (profileError (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                            (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat))))
                                                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                                  Membership.mem.{0, 0}
                                                      (Erdos390.Full.ArithmeticModel.primeBand
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                      p →
                                                    LE.le.{0}
                                                      (abs.{0}
                                                        (HSub.hSub.{0, 0, 0}
                                                          (Erdos390.Full.FiniteProbability.expect.{0}
                                                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_3} B xi c))
                                                            fun
                                                              (m :
                                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B) c) =>
                                                            Erdos390.Full.ArithmeticModel.divInd p
                                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_3} B xi c) m))
                                                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) p)))
                                                      (HMul.hMul.{0, 0, 0}
                                                        (profileError (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                        (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_011 : Prop :=
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (Phead : Head → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real),
  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)) →
    (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) Cmax) →
      ∀ (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W : Nat),
        LT.lt.{0} (1 : Nat) W →
          (∀ (h : Head) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Phead h)) p → LE.le.{0} p W) →
            ∀ (Acoef : Real),
              LE.le.{0} (0 : Real) Acoef →
                ∃ (profileError : Nat → Real),
                  And (∀ (n : Nat), LE.le.{0} (0 : Real) (profileError n))
                    (And (Filter.Tendsto.{0, 0} profileError Filter.atTop.{0} (nhds.{0} (0 : Real)))
                      (And (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (profileError n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0} (nhds.{0} (0 : Real)))
                        (∃ (N₀ : Nat),
                          ∀ {Band : Type u_3} [inst_3 : Fintype.{u_3} Band] [inst_4 : DecidableEq.{u_3 + 1} Band] (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_3} Head Band)
                            (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_3} B),
                            LE.le.{0} N₀ (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) →
                              Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.pattern.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) Phead →
                                (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                    Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B) sigma)
                                      (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))) →
                                  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B) sigma)
                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))) →
                                    Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.guards.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                        (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                          (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))) →
                                      (∀
                                          (p :
                                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))),
                                          LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_3} B xi p)) Acoef) →
                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) W →
                                          And
                                            (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                              Membership.mem.{0, 0}
                                                  (Erdos390.Full.ArithmeticModel.primeBand
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                  p →
                                                ∀ (q : Nat),
                                                  Membership.mem.{0, 0}
                                                      (Finset.erase.{0}
                                                        (Erdos390.Full.ArithmeticModel.primeBand
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                        p)
                                                      q →
                                                    LE.le.{0}
                                                      (abs.{0}
                                                        (HSub.hSub.{0, 0, 0}
                                                          (Erdos390.Full.FiniteProbability.expect.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_3} B xi c)
                                                            fun
                                                              (m :
                                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B) c) =>
                                                            Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)) (↑m : Nat))
                                                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                            (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                                                      (HMul.hMul.{0, 0, 0}
                                                        (profileError (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                        (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat))))
                                            (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                              Membership.mem.{0, 0}
                                                  (Erdos390.Full.ArithmeticModel.primeBand
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                  p →
                                                LE.le.{0}
                                                  (abs.{0}
                                                    (HSub.hSub.{0, 0, 0}
                                                      (Erdos390.Full.FiniteProbability.expect.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_3} B xi c)
                                                        fun
                                                          (m : Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B) c) =>
                                                        Erdos390.Full.ArithmeticModel.divInd p (↑m : Nat))
                                                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)) p)))
                                                  (HMul.hMul.{0, 0, 0}
                                                    (profileError (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_3} B)))
                                                    (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))))))

noncomputable def Erdos390.RemainingAnalyticGoal001_012 : Prop :=
∃ (meshTol : Real),
  And (LT.lt.{0} (0 : Real) meshTol)
    (∃ (Cschur : Real),
      And (LT.lt.{0} (0 : Real) Cschur)
        (∃ (W₀ : Nat),
          ∀ (W : Nat),
            LE.le.{0} W₀ W →
              ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta),
                LE.le.{0} (HAdd.hAdd.{0, 0, 0} delta (Erdos390.Full.RegularRelativeMesh.Mesh.ratio M)) meshTol →
                  ∀ (anchors : Finset.{0} (Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M))),
                    Finset.Nonempty.{0} anchors →
                      (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
                          Membership.mem.{0, 0} anchors k → LT.lt.{0} (1 / 8 : Real) (Erdos390.Full.RegularRelativeMesh.Mesh.lower M k)) →
                        (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
                            Membership.mem.{0, 0} anchors k → LE.le.{0} (Erdos390.Full.RegularRelativeMesh.Mesh.upper M k) (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real))) →
                          LE.le.{0} (1 / 8 : Real) (HDiv.hDiv.{0, 0, 0} (∑ k ∈ anchors, Erdos390.Full.RegularRelativeMesh.Mesh.width M k) (2 : Real)) →
                            ∀ (Head : Type u_1) [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (Phead : Head → Erdos390.Full.HeadPattern.Pattern),
                              (∀ (h : Head) (p : Nat), Iff (Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Phead h)) p) (And (Nat.Prime p) (LE.le.{0} p W))) →
                                ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real) (hU : LE.le.{0} (1 : Real) U)
                                  (hlowerOne : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
                                  (hupperU : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U) (Cprom Cbank : Nat)
                                  (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (a : NNReal) (marginFloor : Real),
                                  LT.lt.{0} (0 : Real) marginFloor →
                                    ∀ᶠ (n : Nat) in Filter.atTop.{0},
                                      ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat)))),
                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) n →
                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) W →
                                            ∀
                                              (hBWlarge :
                                                LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                              (hsep :
                                                LT.lt.{0}
                                                  (Erdos390.Full.ArithmeticModel.physicalBound
                                                    (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))
                                              (hremaining :
                                                ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                                  Finset.Nonempty.{0}
                                                    (SDiff.sdiff.{0}
                                                      (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Phead I
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) c)
                                                      (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                        (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))))
                                              (hcanonical :
                                                Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)
                                                  (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                    (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))) hsep
                                                    hremaining)),
                                              (∃ (hWne : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) (0 : Nat))
                                                  (S :
                                                  Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                    (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B) hWne S)) →
                                                ∀ (T : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)),
                                                  LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                                                    ∀
                                                      (hbaseline :
                                                        Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, 0} B) (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T)),
                                                      ∃ (e :
                                                        (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                          Membership.mem.{u_1, u_1}
                                                              (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z →
                                                            LinearEquiv.{0, 0, 0, 0} (RingHom.id.{0} Real) ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)
                                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                        And
                                                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                            (hz :
                                                              Membership.mem.{u_1, u_1}
                                                                (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z)
                                                            (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                            Eq.{1} (α := ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                              ((e z hz :
                                                                    (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                  q :
                                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                              ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, 0} B
                                                                      ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                          (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                        z)
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                        (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                                        (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                          Eq.mpr.{0}
                                                                            (id.{0}
                                                                              (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                hcanonical))
                                                                            (Eq.refl.{1}
                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                  (ledger
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                  hsep hremaining)
                                                                                sigma)))
                                                                        (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                          Eq.mpr.{0}
                                                                            (id.{0}
                                                                              (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                hcanonical))
                                                                            (Eq.refl.{1}
                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                  (ledger
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                  hsep hremaining)
                                                                                sigma)))
                                                                        T hbaseline hBWlarge z hz) :
                                                                    (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                  q :
                                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)))
                                                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                            (hz :
                                                              Membership.mem.{u_1, u_1}
                                                                (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z)
                                                            (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                            LE.le.{0}
                                                              (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, 0} B)
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0} B)
                                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B))
                                                                ((LinearEquiv.symm.{0, 0, 0, 0} (e z hz) :
                                                                    (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                  v))
                                                              (HMul.hMul.{0, 0, 0} Cschur
                                                                (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, 0} B)
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0} B)
                                                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B))
                                                                  v)))))

noncomputable def Erdos390.RemainingAnalyticGoal001_013 : Prop :=
∃ (meshTol : Real),
  And (LT.lt.{0} (0 : Real) meshTol)
    (∃ (Cref : Real),
      And (LT.lt.{0} (0 : Real) Cref)
        (∃ (W₀ : Nat),
          ∀ (W : Nat),
            LE.le.{0} W₀ W →
              ∀ (Head : Type u_1) [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta)
                (hdelta : LT.lt.{0} (0 : Real) delta),
                LE.le.{0} (HAdd.hAdd.{0, 0, 0} delta (Erdos390.Full.RegularRelativeMesh.Mesh.ratio M)) meshTol →
                  ∀ (anchors : Finset.{0} (Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M))),
                    Finset.Nonempty.{0} anchors →
                      (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
                          Membership.mem.{0, 0} anchors k → LT.lt.{0} (1 / 8 : Real) (Erdos390.Full.RegularRelativeMesh.Mesh.lower M k)) →
                        (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
                            Membership.mem.{0, 0} anchors k → LE.le.{0} (Erdos390.Full.RegularRelativeMesh.Mesh.upper M k) (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real))) →
                          LE.le.{0} (1 / 8 : Real) (HDiv.hDiv.{0, 0, 0} (∑ k ∈ anchors, Erdos390.Full.RegularRelativeMesh.Mesh.width M k) (2 : Real)) →
                            ∀ᶠ (n : Nat) in Filter.atTop.{0},
                              ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat)))),
                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) n →
                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) W →
                                    (∃ (hWne : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) (0 : Nat)) (S :
                                        Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                          (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B) hWne S)) →
                                      ∃ (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)) (referenceEquiv :
                                        ContinuousLinearEquiv.{0, 0, 0, 0} (RingHom.id.{0} Real)
                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))
                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))),
                                        And
                                          (∀
                                            (q :
                                              ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))),
                                            Eq.{1} (α :=
                                              ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))))
                                              ((referenceEquiv :
                                                    (a :
                                                        ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))) →
                                                      ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))))
                                                  q :
                                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))))
                                              ((Erdos390.Full.ArithmeticGaugeStableInverse.projectedSharpCLM.{0}
                                                      (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{0}
                                                        (Erdos390.Full.ArithmeticModel.y
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{0} cert) (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{0} cert))
                                                      (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{0}
                                                        (Erdos390.Full.ArithmeticModel.y
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{0} cert) (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{0} cert))
                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                      (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{0}
                                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))
                                                      (ne_of_gt.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualSharpWeightTotal_pos.{u_1, 0} B)) :
                                                    (a :
                                                        ↥(Erdos390.Full.FiniteGraphStableInverse.GaugeSpace.{0}
                                                            (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{0}
                                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))))) →
                                                      ↥(Erdos390.Full.FiniteGraphStableInverse.GaugeSpace.{0}
                                                          (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{0}
                                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))))
                                                  q :
                                                ↥(Erdos390.Full.FiniteGraphStableInverse.GaugeSpace.{0}
                                                    (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{0}
                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))))))
                                          (∀
                                            (v :
                                              ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))),
                                            LE.le.{0}
                                              (Norm.norm.{0} (E :=
                                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))))
                                                ((ContinuousLinearEquiv.symm.{0, 0, 0, 0} referenceEquiv :
                                                      (a :
                                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))) →
                                                        ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))))
                                                    v :
                                                  ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{0}
                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))))
                                              (HMul.hMul.{0, 0, 0} Cref (Norm.norm.{0} v)))))

noncomputable def Erdos390.RemainingAnalyticGoal001_014 : Prop :=
∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real) (hU : LE.le.{0} (1 : Real) U)
  (hlowerOne : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
  (hupperU : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U) (Cprom Cbank : Nat)
  (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank),
  ∃ (W₀ : Nat),
    ∀ (W : Nat),
      LE.le.{0} W₀ W →
        ∀ {CinvOrd Tband targetScale gammaSlow Creg : Real},
          LE.le.{0} (0 : Real) CinvOrd →
            LE.le.{0} (0 : Real) Tband →
              LE.le.{0} (0 : Real) targetScale →
                LT.lt.{0} (0 : Real) gammaSlow →
                  LE.le.{0} (0 : Real) Creg →
                    ∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (Phead : Head → Erdos390.Full.HeadPattern.Pattern),
                      (∀ (h : Head) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Phead h)) p → LE.le.{0} p W) →
                        ∀ (a : NNReal) (marginFloor : Real),
                          LT.lt.{0} (0 : Real) marginFloor →
                            ∃ (Crow : Real),
                              And (LE.le.{0} (0 : Real) Crow)
                                (∀ {delta eta : Real} (hdelta : LT.lt.{0} (0 : Real) delta) (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta),
                                  ∀ᶠ (n : Nat) in Filter.atTop.{0},
                                    ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat)))),
                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) n →
                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) W →
                                          ∀ (hBWlarge : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                            (hsep :
                                              LT.lt.{0}
                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))
                                            (hremaining :
                                              ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                                Finset.Nonempty.{0}
                                                  (SDiff.sdiff.{0}
                                                    (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Phead I
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) c)
                                                    (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                      (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))))
                                            (hcanonical :
                                              Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)
                                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                  (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))) hsep
                                                  hremaining)),
                                            (∃ (hWne : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) (0 : Nat)) (S
                                                :
                                                Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                  (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B) hWne S)) →
                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (HAdd.hAdd.{0, 0, 0} delta eta) →
                                                ∀ (Delta : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat)) → Real)
                                                  (T : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)),
                                                  LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                                                    ∀
                                                      (hbaseline :
                                                        Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, 0} B) (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T))
                                                      {gammaFull : Real},
                                                      LT.lt.{0} (0 : Real) gammaFull →
                                                        (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)),
                                                            Membership.mem.{u_1, u_1}
                                                                (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z →
                                                              Erdos390.Full.VectorExponentialFamily.HasCovarianceGap.{u_1, u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1, 0} B)
                                                                gammaFull
                                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                    (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                  z)) →
                                                          ∀
                                                            (e :
                                                              (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                Membership.mem.{u_1, u_1}
                                                                    (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z →
                                                                  LinearEquiv.{0, 0, 0, 0} (RingHom.id.{0} Real) ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)
                                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                            (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                (hz :
                                                                  Membership.mem.{u_1, u_1}
                                                                    (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z)
                                                                (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                                Eq.{1} (α := ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                  ((e z hz :
                                                                        (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                      q :
                                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, 0} B
                                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                              (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                            z)
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                            (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                              Eq.mpr.{0}
                                                                                (id.{0}
                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                    (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                    hcanonical))
                                                                                (Eq.refl.{1}
                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                      (ledger
                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                      hsep hremaining)
                                                                                    sigma)))
                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                              Eq.mpr.{0}
                                                                                (id.{0}
                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                    (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                    hcanonical))
                                                                                (Eq.refl.{1}
                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                      (ledger
                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                      hsep hremaining)
                                                                                    sigma)))
                                                                            T hbaseline hBWlarge z hz) :
                                                                        (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                      q :
                                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))) →
                                                              (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                  (hz :
                                                                    Membership.mem.{u_1, u_1}
                                                                      (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z),
                                                                  LE.le.{0} (HMul.hMul.{0, 0, 0} gammaSlow (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (2 : Nat)))
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1, 0} B
                                                                      ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                          (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                        z)
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                        (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                                        (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                          Eq.mpr.{0}
                                                                            (id.{0}
                                                                              (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                hcanonical))
                                                                            (Eq.refl.{1}
                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                  (ledger
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                  hsep hremaining)
                                                                                sigma)))
                                                                        (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                          Eq.mpr.{0}
                                                                            (id.{0}
                                                                              (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                hcanonical))
                                                                            (Eq.refl.{1}
                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                  (ledger
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                  hsep hremaining)
                                                                                sigma)))
                                                                        T hbaseline hBWlarge z hz)
                                                                      (e z hz))) →
                                                                (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                    (hz :
                                                                      Membership.mem.{u_1, u_1}
                                                                        (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z),
                                                                    LE.le.{0}
                                                                      (abs.{0}
                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.compensatedNormalizedTarget.{u_1, 0} B
                                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                              (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                            z)
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                            (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                              Eq.mpr.{0}
                                                                                (id.{0}
                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                    (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                    hcanonical))
                                                                                (Eq.refl.{1}
                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                      (ledger
                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                      hsep hremaining)
                                                                                    sigma)))
                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                              Eq.mpr.{0}
                                                                                (id.{0}
                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                    (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                    hcanonical))
                                                                                (Eq.refl.{1}
                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                      (ledger
                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                      hsep hremaining)
                                                                                    sigma)))
                                                                            T hbaseline hBWlarge z hz)
                                                                          (e z hz) Delta))
                                                                      (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) targetScale)) →
                                                                  (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                      (hz :
                                                                        Membership.mem.{u_1, u_1}
                                                                          (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z)
                                                                      (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                                      LE.le.{0}
                                                                        (Norm.norm.{0} (E := ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                          ((LinearEquiv.symm.{0, 0, 0, 0} (e z hz) :
                                                                                (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                              v :
                                                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)))
                                                                        (HMul.hMul.{0, 0, 0} CinvOrd (Norm.norm.{0} v))) →
                                                                    LE.le.{0} (Norm.norm.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.projectedNormalizedTargetBand.{u_1, 0} B Delta)) Tband →
                                                                      (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                          (hz :
                                                                            Membership.mem.{u_1, u_1}
                                                                              (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z),
                                                                          LE.le.{0}
                                                                            (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{0}
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, 0} B)
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0} B)
                                                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{0}
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B))
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                    (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                  z)
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                                  (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                                                  (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                    Eq.mpr.{0}
                                                                                      (id.{0}
                                                                                        (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                          (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                              (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                          hcanonical))
                                                                                      (Eq.refl.{1}
                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                          (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                            (ledger
                                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                            hsep hremaining)
                                                                                          sigma)))
                                                                                  (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                    Eq.mpr.{0}
                                                                                      (id.{0}
                                                                                        (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                          (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                              (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                          hcanonical))
                                                                                      (Eq.refl.{1}
                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                          (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                            (ledger
                                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                            hsep hremaining)
                                                                                          sigma)))
                                                                                  T hbaseline hBWlarge z hz)
                                                                                (e z hz)))
                                                                            (HMul.hMul.{0, 0, 0} Creg (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B))) →
                                                                        ∀ (monitoredPrimes : Finset.{0} Nat),
                                                                          (∀ (p : Nat),
                                                                              Membership.mem.{0, 0} monitoredPrimes p →
                                                                                Membership.mem.{0, 0}
                                                                                  (Erdos390.Full.ArithmeticModel.primeBand
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                  p) →
                                                                            ∀ (p : Nat),
                                                                              Membership.mem.{0, 0} monitoredPrimes p →
                                                                                ∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)),
                                                                                  Membership.mem.{u_1, u_1}
                                                                                      (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                                        (↑a : Real))
                                                                                      z →
                                                                                    LE.le.{0}
                                                                                      (abs.{0}
                                                                                        (Erdos390.Full.FiniteExponentialFamily.covariance.{u_1, u_1}
                                                                                          (Erdos390.Full.VectorExponentialFamily.scalarFamily.{u_1, u_1}
                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1, 0} B))
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1, 0} B p)
                                                                                          (fun
                                                                                              (m :
                                                                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) =>
                                                                                            (Erdos390.Full.FiniteExponentialFamily.score.{u_1, u_1}
                                                                                                  (Erdos390.Full.VectorExponentialFamily.scalarFamily.{u_1, u_1}
                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1, 0} B))
                                                                                                  m :
                                                                                                (a : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B) → Real)
                                                                                              (Erdos390.Full.VectorExponentialFamily.vectorField.{u_1, u_1}
                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1, 0} B)
                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.targetVector.{u_1, 0} B Delta)
                                                                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                    (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                  z)))
                                                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                              (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                            z)))
                                                                                      (HDiv.hDiv.{0, 0, 0} Crow (↑p : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal001_015 : Prop :=
∀ (Cref Rproj : Real),
  LT.lt.{0} (0 : Real) Cref →
    LE.le.{0} (0 : Real) Rproj →
      ∃ (W₀ : Nat),
        ∀ (W : Nat),
          LE.le.{0} W₀ W →
            ∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (Phead : Head → Erdos390.Full.HeadPattern.Pattern),
              (∀ (h : Head) (p : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Phead h)) p → LE.le.{0} p W) →
                ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real) (hU : LE.le.{0} (1 : Real) U)
                  (hlowerOne : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
                  (hupperU : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U) (Cprom Cbank : Nat)
                  (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (a : NNReal) (marginFloor : Real),
                  LT.lt.{0} (0 : Real) marginFloor →
                    ∀ {Band : Type u_2} [inst_3 : Fintype.{u_2} Band] [inst_4 : DecidableEq.{u_2 + 1} Band] [inst_5 : Nonempty.{u_2 + 1} Band],
                      ∀ᶠ (n : Nat) in Filter.atTop.{0},
                        ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band),
                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) n →
                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) W →
                              ∀ (hBWlarge : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                (hsep :
                                  LT.lt.{0}
                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                                (hremaining :
                                  ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                    Finset.Nonempty.{0}
                                      (SDiff.sdiff.{0}
                                        (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Phead I
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) c)
                                        (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                          (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))))
                                (hcanonical :
                                  Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)
                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                      (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))) hsep hremaining))
                                (T : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                                LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                                  ∀ (hbaseline : Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B) (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T)),
                                    LE.le.{0}
                                        (∑ j : Band,
                                          HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B j) (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B j))
                                        (HMul.hMul.{0, 0, 0} Rproj
                                          (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_2} (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B))) →
                                      And
                                        (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)),
                                          Membership.mem.{u_1, u_1} (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) (↑a : Real)) z →
                                            ∀ (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) (i : Band),
                                              LE.le.{0}
                                                (abs.{0}
                                                  (HSub.hSub.{0, 0, 0}
                                                    (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeBandRow.{u_1, u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B
                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B :
                                                            (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                                                              Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                          z))
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) (↑q : Band → Real) i)
                                                    (Erdos390.Full.SquarefreeSharpBandTransfer.referenceBandRow.{u_2} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                      (↑q : Band → Real) i)))
                                                (HMul.hMul.{0, 0, 0} (Norm.norm.{u_2} q) (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalOrdinaryRowTolerance Cref Rproj)))
                                        (And
                                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)),
                                            Membership.mem.{u_1, u_1} (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) (↑a : Real)) z →
                                              ∀ (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) (i : Band),
                                                LE.le.{0}
                                                  (abs.{0}
                                                    (HSub.hSub.{0, 0, 0}
                                                      (Erdos390.Full.PrimePowerSharpBandTransfer.fullBandRow.{u_1, u_2}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B
                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B :
                                                              (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                            z))
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) (↑q : Band → Real) i)
                                                      (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeBandRow.{u_1, u_2}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B
                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B :
                                                              (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                            z))
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) (↑q : Band → Real) i)))
                                                  (HMul.hMul.{0, 0, 0} (Norm.norm.{u_2} q) (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalOrdinaryRowTolerance Cref Rproj)))
                                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                            (hz : Membership.mem.{u_1, u_1} (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) (↑a : Real)) z)
                                            (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                            LE.le.{0}
                                              (Norm.norm.{u_2}
                                                (HSub.hSub.{u_2, u_2, u_2} (α := ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) (β :=
                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2} B
                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B :
                                                              (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                            z)
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, u_2} B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, u_2} B I a hU hlowerOne hupperU
                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                              Eq.mpr.{0}
                                                                (id.{0}
                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                    (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                    hcanonical))
                                                                (Eq.refl.{1}
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                                      (ledger
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                                                      hsep hremaining)
                                                                    sigma)))
                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                              Eq.mpr.{0}
                                                                (id.{0}
                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                    (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                    hcanonical))
                                                                (Eq.refl.{1}
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                                      (ledger
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                                                      hsep hremaining)
                                                                    sigma)))
                                                            T hbaseline hBWlarge z hz) :
                                                        (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) →
                                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                                      q :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandFullLinearMap.{u_1, u_2} B
                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B :
                                                              (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                            z) :
                                                        (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) →
                                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                                      q :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))))
                                              (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalOrdinarySchurTolerance Cref) (Norm.norm.{u_2} q))))


