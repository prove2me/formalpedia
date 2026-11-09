-- Prove2me | solution 1 for CouretOaiBridge01.InteriaSA05.besselSingularMode_euler_first_order
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:01:00.310245+00:00
-- url     : https://prove2.me/submissions/81c2ae7f-327c-4238-aa96-fb498de45f21

import Definitions.Def_Couret_INTERIA_SA_05_BesselWeightedModes_d5985292a225
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
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









/-- The explicit singular power mode has the standard first derivative. -/
theorem besselSingularMode_deriv (ν x : ℝ) :
    deriv (besselSingularMode ν) x = (-|ν|) * x ^ ((-|ν|) - 1) := by
  change deriv (fun y : ℝ => y ^ (-|ν|)) x = _
  exact Real.deriv_rpow_const x (-|ν|)

/-- On x>0 the model mode solves the *first-order* Euler equation
x u' = -|ν| u. This is not yet the second-order Bessel equation. -/
theorem p2m_local_besselSingularMode_euler_first_order (ν x : ℝ) (hx : 0 < x) :
    x * deriv (besselSingularMode ν) x = (-|ν|) * besselSingularMode ν x := by
  rw [besselSingularMode_deriv]
  have heq : x * x ^ ((-|ν|) - 1) = x ^ (-|ν|) := by
    calc
      x * x ^ ((-|ν|) - 1) =
          x ^ (1 : ℝ) * x ^ ((-|ν|) - 1) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + ((-|ν|) - 1)) :=
        (Real.rpow_add hx 1 ((-|ν|) - 1)).symm
      _ = x ^ (-|ν|) := by congr 1; ring
  calc
    x * ((-|ν|) * x ^ ((-|ν|) - 1)) =
        (-|ν|) * (x * x ^ ((-|ν|) - 1)) := by ring
    _ = (-|ν|) * besselSingularMode ν x := by rw [heq]; rfl





end CouretOaiBridge01.InteriaSA05


theorem solution : ∀ (ν x : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x →
    @Eq.{1} Real
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x
        (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
          Real.instAddCommGroup
          (@Semiring.toModule.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (CouretOaiBridge01.InteriaSA05.besselSingularMode ν) x))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Neg.neg.{0} Real Real.instNeg (@abs.{0} Real Real.lattice Real.instAddGroup ν))
        (CouretOaiBridge01.InteriaSA05.besselSingularMode ν x)) := @_root_.CouretOaiBridge01.InteriaSA05.p2m_local_besselSingularMode_euler_first_order

