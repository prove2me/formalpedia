-- Prove2me | solution 1 for CouretOaiBridge01.InteriaSA04.frobeniusCriticalNotIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:33.767875+00:00
-- url     : https://prove2.me/submissions/159e21fd-5b3e-4bad-be7d-9165c3174cb6

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic

/-!
# INTERIA-SA-04 / first analytic power-integrability gates

These theorems are genuine mathematical integrability statements on (0,1),
obtained from the existing mathlib theorem `integrableOn_Ioo_rpow_iff`.
They do not prove the full Weyl endpoint classification, identify operator
domains, or establish any Hilbert-Polya / Riemann-hypothesis claim.

The `x^(1-2*|nu|)` model is the real-power integrand associated with the
squared singular Bessel mode `x^(-|nu|)` under radial weight `x dx`.
The `x^(2*r)` model corresponds to a real Frobenius mode `x^r` squared.
Connecting these model integrands to differential operator solutions
requires separate formalized hypotheses and equivalences.
-/

open Set MeasureTheory intervalIntegral

namespace CouretOaiBridge01.InteriaSA04



/-- The squared real Frobenius mode `x^r` is integrable at zero iff
its real exponent satisfies `r > -1/2`. -/
theorem frobeniusPowerIntegrableAtZero_iff (r : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * r)) (Ioo (0 : ℝ) 1) ↔ -(1 / 2 : ℝ) < r := by
  rw [integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)]
  constructor <;> intro h <;> linarith







/-- Borderline Frobenius exponent `r = -1/2` fails the power test. -/
theorem p2m_local_frobeniusCriticalNotIntegrable :
    ¬ IntegrableOn (fun x : ℝ => x ^ (2 * (-(1 / 2 : ℝ))))
      (Ioo (0 : ℝ) 1) := by
  intro h
  have hbad := (frobeniusPowerIntegrableAtZero_iff (-(1 / 2 : ℝ))).mp h
  norm_num at hbad

end CouretOaiBridge01.InteriaSA04


theorem solution : Not
  (@MeasureTheory.IntegrableOn.{0, 0} Real Real
    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@SeminormedAddGroup.toContinuousENorm.{0} Real
      (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
              (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))
    (fun x =>
      @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) x
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@Neg.neg.{0} Real Real.instNeg
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))
    (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)) := @_root_.CouretOaiBridge01.InteriaSA04.p2m_local_frobeniusCriticalNotIntegrable

