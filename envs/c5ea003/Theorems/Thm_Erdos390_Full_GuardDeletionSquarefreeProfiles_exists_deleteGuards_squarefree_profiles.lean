-- Prove2me | Theorems.Thm_Erdos390_Full_GuardDeletionSquarefreeProfiles_exists_deleteGuards_squarefree_profiles
-- name    : Erdos390.Full.GuardDeletionSquarefreeProfiles.exists_deleteGuards_squarefree_profiles
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:03:07.671025+00:00
-- url     : https://prove2.me/theorems/d22a7c79-4643-4f60-a69b-05fcd3052707
-- title:
--   Signed squarefree profiles survive conditioning away from guards
-- statement:
--   Let $S,G$ be finite sets of natural numbers, $S$ nonempty, and let a score on $S$ satisfy $|s|\le K$. Put $\mu$ equal to the exponential tilt of the uniform law on $S$, and set $\delta=e^{2K}|G|/|S|$. Assume $\delta\le1/2$. Suppose $\mu$ has the common paper divisibility profiles with errors at most $4E/(pq)$ for distinct moving-band primes and $2E/p$ for individual moving-band primes. The guard mass is less than one, so conditioning $\mu$ away from $S\cap G$ is defined. For that conditional law, the same profiles hold with
--   $$E\quad\hbox{replaced by}\quad E+2\delta\,y_{\mathbb N}(n)^2.$$
--   This finite result includes the normalization cost of deleting the guards. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/GuardDeletionSquarefreeProfiles.lean#L34-L208

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

theorem Erdos390.Full.GuardDeletionSquarefreeProfiles.exists_deleteGuards_squarefree_profiles :
∀ (S G : Finset.{0} Nat) (hS : Finset.Nonempty.{0} S) (score : ↥S → Real) (K : Real),
  (∀ (x : ↥S), LE.le.{0} (abs.{0} (score x)) K) →
    ∀ {n W : Nat} {E : Real},
      LE.le.{0}
          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp (HMul.hMul.{0, 0, 0} (2 : Real) K)) ↑(Finset.card.{0} G))
            ↑(Finset.card.{0} S))
          (1 / 2 : Real) →
        (∀ (p : Nat),
            Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
              ∀ (q : Nat),
                Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.FiniteProbability.expect.{0}
                          (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                            (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) score)
                          fun m =>
                          Erdos390.Full.ArithmeticModel.divInd
                            (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)) ↑m)
                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n
                          (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                    (HMul.hMul.{0, 0, 0} E
                      (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat)))) →
          (∀ (p : Nat),
              Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (Erdos390.Full.FiniteProbability.expect.{0}
                        (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                          (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) score)
                        fun m => Erdos390.Full.ArithmeticModel.divInd p ↑m)
                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                  (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
            ∃ (hsmall :
              LT.lt.{0}
                (Erdos390.Full.FiniteProbability.guardMass.{0}
                  (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                    (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) score)
                  (Erdos390.Full.GuardedUniformCell.guardSubtype.{0} S G))
                (1 : Real)),
              have deleted :=
                Erdos390.Full.FiniteProbability.deleteGuards.{0}
                  (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                    (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) score)
                  (Erdos390.Full.GuardedUniformCell.guardSubtype.{0} S G) hsmall;
              And
                (∀ (p : Nat),
                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                    ∀ (q : Nat),
                      Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (Erdos390.Full.FiniteProbability.expect.{0} deleted fun m =>
                                Erdos390.Full.ArithmeticModel.divInd
                                  (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)) ↑m)
                              (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n
                                (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                          (HMul.hMul.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0} E
                              (Erdos390.Full.GuardDeletionSquarefreeProfiles.guardSquarefreeError S G K n))
                            (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat))))
                (∀ (p : Nat),
                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.expect.{0} deleted fun m =>
                            Erdos390.Full.ArithmeticModel.divInd p ↑m)
                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                      (HMul.hMul.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0} E
                          (Erdos390.Full.GuardDeletionSquarefreeProfiles.guardSquarefreeError S G K n))
                        (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) := by sorry
