-- Prove2me | solution 1 for CouretOaiBridge01.InteriaSA04.besselPowerIntegrableAtZero_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:46.661338+00:00
-- url     : https://prove2.me/submissions/078119e6-6ee0-44a7-857c-5437e6884595

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

/-- Classical `p > -1` criterion for the model Bessel singular-mode power.
This checks real Lebesgue integrability of the power integrand; it does NOT
construct a weighted Hilbert-space operator or prove a Weyl classification. -/
theorem p2m_local_besselPowerIntegrableAtZero_iff (nu : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (1 - 2 * |nu|)) (Ioo (0 : ℝ) 1) ↔ |nu| < 1 := by
  rw [integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)]
  constructor <;> intro h <;> linarith











end CouretOaiBridge01.InteriaSA04


theorem solution : ∀ (nu : Real),
  Iff
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
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@abs.{0} Real Real.lattice Real.instAddGroup nu))))
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (@LT.lt.{0} Real Real.instLT (@abs.{0} Real Real.lattice Real.instAddGroup nu)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := @_root_.CouretOaiBridge01.InteriaSA04.p2m_local_besselPowerIntegrableAtZero_iff

