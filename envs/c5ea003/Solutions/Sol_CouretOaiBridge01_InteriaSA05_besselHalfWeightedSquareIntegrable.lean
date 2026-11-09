-- Prove2me | solution 1 for CouretOaiBridge01.InteriaSA05.besselHalfWeightedSquareIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:40.298253+00:00
-- url     : https://prove2.me/submissions/85538f2a-9c07-4ece-b028-090eefa67389

import Definitions.Def_Couret_INTERIA_SA_05_BesselWeightedModes_d5985292a225
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import Theorems.Thm_CouretOaiBridge01_InteriaSA04_besselPowerIntegrableAtZero_iff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# INTERIA-SA-05 — singular Bessel power mode and weighted norm

A first, narrowly scoped connection from the mathlib power-integrability
criterion to an explicit differentiable function.

This is a model zero-energy power mode (not a classification of the Bessel
minimal operator). In particular the logarithmic companion at ν=0, the
second-order differential equation, Weyl's alternative, boundary domains and
deficiency indices are NOT established here. No Hilbert–Pólya/RH claim.
-/

open Set MeasureTheory

namespace CouretOaiBridge01.InteriaSA05





/-- Exact pointwise radial-weight identity on the positive half-line. -/
theorem besselWeightedSquare_eq_power (ν x : ℝ) (hx : 0 < x) :
    besselWeightedSquare ν x = x ^ (1 - 2 * |ν|) := by
  unfold besselWeightedSquare besselSingularMode
  calc
    x * (x ^ (-|ν|)) ^ (2 : ℕ) =
        x ^ (1 : ℝ) * x ^ ((-|ν|) * (2 : ℝ)) := by
      rw [Real.rpow_one, ← Real.rpow_mul_natCast (le_of_lt hx) (-|ν|) 2]
      norm_cast
    _ = x ^ ((1 : ℝ) + (-|ν|) * (2 : ℝ)) :=
      (Real.rpow_add hx 1 ((-|ν|) * 2)).symm
    _ = x ^ (1 - 2 * |ν|) := by congr 1; ring

/-- The exact weighted-square power integral on (0,1) is integrable
iff |ν| < 1. It does not by itself establish a Weyl LC property. -/
theorem besselWeightedSquareIntegrable_iff (ν : ℝ) :
    IntegrableOn (besselWeightedSquare ν) (Ioo (0 : ℝ) 1) ↔ |ν| < 1 := by
  rw [integrableOn_congr_fun (fun x hx =>
    besselWeightedSquare_eq_power ν x hx.1) measurableSet_Ioo]
  exact CouretOaiBridge01.InteriaSA04.besselPowerIntegrableAtZero_iff ν







/-- The interior ν=1/2 model is weighted-square integrable. -/
theorem p2m_local_besselHalfWeightedSquareIntegrable :
    IntegrableOn (besselWeightedSquare (1 / 2)) (Ioo (0 : ℝ) 1) := by
  exact (besselWeightedSquareIntegrable_iff (1 / 2)).2 (by norm_num)

end CouretOaiBridge01.InteriaSA05


theorem solution : @MeasureTheory.IntegrableOn.{0, 0} Real Real (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
  (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
  (@SeminormedAddGroup.toContinuousENorm.{0} Real
    (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))
  (CouretOaiBridge01.InteriaSA05.besselWeightedSquare
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
  (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) := @_root_.CouretOaiBridge01.InteriaSA05.p2m_local_besselHalfWeightedSquareIntegrable

