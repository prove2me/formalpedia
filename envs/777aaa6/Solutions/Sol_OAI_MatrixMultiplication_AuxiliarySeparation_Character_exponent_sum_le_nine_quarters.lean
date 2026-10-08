-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.Character.exponent_sum_le_nine_quarters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:48:43.331261+00:00
-- url     : https://prove2.me/submissions/e7851974-44e0-472d-ae97-7def59391ec2

/-
Port of OpenAI math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, with an all-fields extension and comparison to the MME tensor-rank model.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.


Copyright (c) 2026 harfe

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.AddTorsor.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.MonotoneConvergence
import Definitions.Def_OAI429_GenericCharacterCore
import Definitions.Def_OAI429_GenericCharacterLaws
import Definitions.Def_OAI429_GenericConvolution
import Definitions.Def_OAI429_GenericNumerics
import Definitions.Def_OAI429_GenericPairing
import Definitions.Def_OAI429_GenericProfile
import Definitions.Def_OAI429_GenericRank
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_convolutionProfile_concave
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_convolutionProfile_tripling
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_one_le_sixfoldProduct
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_one_le_value
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_sixfoldProduct_dotPairing
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_sixfoldProduct_le_rank
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_sixfoldProduct_reindex
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_ScalarProfile_exponent_le_three_quarters
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_eq_of_nat_mul_sub_bounded
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_positiveMultiplicative_log_error_bounds
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Character
end OAI.MatrixMultiplication.AuxiliarySeparation.Character
open OAI.MatrixMultiplication.AuxiliarySeparation.Character

namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation
namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_b6058a9b2e46
namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation



set_option linter.all false

set_option autoImplicit false

section AllFieldsModule0/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.MultiplicativePower -/
section AbstractModule19



namespace OAI

/-!
# Monotone multiplicative functions on the positive natural numbers

The scalar classification used in Section 3.1: positivity, multiplicativity,
and monotonicity force a function on positive natural numbers to be a real
power. No property of the function at zero is required.
-/

namespace MatrixMultiplication.AuxiliarySeparation













/-- The logarithmic exponent is the same at every positive natural number. -/
theorem positiveMultiplicative_log_eq
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    Real.log (f n) = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by
  have heq : Real.log (f n) * Real.log 2 =
      Real.log (n : ℝ) * Real.log (f 2) :=
    eq_of_nat_mul_sub_bounded
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).1)
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).2)
  calc
    Real.log (f n) = (Real.log (n : ℝ) * Real.log (f 2)) / Real.log 2 :=
      (eq_div_iff (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne').2 heq
    _ = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by ring

/-- The explicit exponent in the classification of positive monotone
multiplicative functions on the positive natural numbers. -/
theorem positiveMultiplicative_eq_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    f n = (n : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnp, ← positiveMultiplicative_log_eq hpos hmul hmono hn,
    Real.exp_log (hpos n hn)]



end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule19


end AllFieldsModule0/- BEGIN all-fields module GenericCharacterCore -/
section AllFieldsModule3



namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section DependentSum

variable {K S : Type*} [CommSemiring K] [DecidableEq S]
variable {X Y Z : S → Type*}











end DependentSum
end Tensor


end MatrixMultiplication.Foundation
end OAI


/- Character/Basic -/
section CharacterModule0

namespace OAI

/-!
# Characters of finite complex tensors

The tensor operations in this file are the coefficient operations from
`MatrixMultiplication.Foundation.Tensor`. A character is an assumption on those
operations, not an assertion that a character exists. Restriction monotonicity
forces invariance under independent invertible changes of coordinates, so this
interface descends to the mutual-restriction classes of Section 3 of the paper.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]







namespace Character

variable (χ : (Character K))
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Coordinate pullbacks are restrictions. -/
theorem value_pullback_le (T : Tensor K X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by
  classical
  rw [Tensor.pullback_eq_restrict]
  exact χ.monotone T _ _ _

/-- Independent coordinate bijections preserve a character. -/
theorem value_reindex (T : Tensor K X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  apply le_antisymm ((_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ) T ex ey ez)
  have h := (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ) (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm
      (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h













end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end CharacterModule0


/- Tensor/CharacterBounds -/
section CharacterModule1

namespace OAI

/-!
# (Character K) values on powers and varying-dimension direct sums

These are consequences of the normalized restriction-monotone character
interface. Coordinate changes preserve values; permuting the three tensor
legs need not preserve an individual character.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {K : Type*} [Field K]

variable (χ : (Character K))

section Embeddings

variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']



end Embeddings

section Powers

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]







end Powers

section DependentDirectSum

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X Y Z : ι → Type}
variable [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]


















end DependentDirectSum

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end CharacterModule1




end AllFieldsModule3
/- END all-fields module GenericCharacterCore -/

/- BEGIN all-fields module GenericCharacterLaws -/
section AllFieldsModule10

set_option autoImplicit false

section DotCharacter
namespace OAI

/-!
# Dot-product exponents of tensor characters

The power laws here follow from restriction monotonicity and tensor products.
They are not additional assumptions on a character. The three exponents refer
to the leg on which the corresponding dot product has dimension one.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {K : Type*} [Field K]
variable (χ : Character K)

theorem value_pos {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} (hT : T ≠ 0) : 0 < χ.value T :=
  lt_of_lt_of_le zero_lt_one (χ.one_le_value hT)





private theorem dotPairing_ne_zero {m : ℕ} (hm : 0 < m) :
    Tensor.dotPairing (K := K) (Fin m) ≠ 0 := by
  intro h
  have hv := congrFun (congrFun (congrFun h ⟨0, hm⟩) ⟨0, hm⟩) ()
  simp [Tensor.dotPairing] at hv



theorem value_dotPairing_pos {m : ℕ} (hm : 0 < m) :
    0 < χ.value (Tensor.dotPairing (K := K) (Fin m)) :=
  (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pos χ) (dotPairing_ne_zero hm)



theorem value_dotPairing_mono {m n : ℕ} (hmn : m ≤ n) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) ≤
      χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback (Fin.castLE hmn) (Fin.castLE hmn) id
      (Tensor.dotPairing (K := K) (Fin n)) = Tensor.dotPairing (K := K) (Fin m) := by
    funext x y z
    simp [Tensor.pullback, Tensor.dotPairing]
  rw [← heq]
  exact (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ) _ _ _ _

theorem value_dotPairing_mul (m n : ℕ) :
    χ.value (Tensor.dotPairing (K := K) (Fin (m * n))) =
      χ.value (Tensor.dotPairing (K := K) (Fin m)) *
        χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback finProdFinEquiv.symm finProdFinEquiv.symm
      (Equiv.prodUnique Unit Unit).symm
      (Tensor.product (Tensor.dotPairing (K := K) (Fin m))
        (Tensor.dotPairing (K := K) (Fin n))) =
      Tensor.dotPairing (K := K) (Fin (m * n)) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing,
      ite_zero_mul_ite_zero, one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  rw [← heq, (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_reindex χ), χ.map_product]
















theorem value_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) = (m : ℝ) ^ χ.pZ := by
  apply positiveMultiplicative_eq_rpow
    (f := fun m => χ.value (Tensor.dotPairing (K := K) (Fin m)))
    (fun n hn => (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_pos χ) hn)
    (fun m n _ _ => (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_mul χ) m n)
    (fun _ _ _ _ hmn => (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_mono χ) hmn) hm

theorem value_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m))) =
      (m : ℝ) ^ χ.pY :=
  (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing χ.cyclicCharacter) hm

theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m)))) =
      (m : ℝ) ^ χ.pX :=
  (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing χ.cyclicCharacter.cyclicCharacter) hm







end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end DotCharacter

section DegenerationCharacter
namespace OAI

/-!
# Characters decrease under polynomial degeneration

Finite interpolation expresses a polynomial's leading coefficient as a sum
of evaluations.  Applying it after tensor powering gives only a linear
overhead, which disappears in the exponential growth rate.  No continuity
assumption on the character is used.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

variable {K : Type*} [Field K] [Infinite K]
variable (χ : Character K)
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]















end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end DegenerationCharacter



end AllFieldsModule10
/- END all-fields module GenericCharacterLaws -/

/- BEGIN all-fields module GenericConvolution -/
section AllFieldsModule11
set_option autoImplicit false

section Module0
namespace OAI
variable {K : Type*} [Field K]

/-!
# The polynomial multiplication tensor

The coefficient tensor `convolution (K := K) a b` represents multiplication of binary forms
of degrees `a - 1` and `b - 1`, or equivalently ordinary coefficient convolution.
The output leg has `a + b - 1` coordinates.  The definitions also make sense when
an input dimension is zero, while the nonzero and full-output-support statements
use the positive dimensions assumed in Section 5 of the paper.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation



@[simp] theorem convolution_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl









@[simp] theorem convolution_at_output {a b : ℕ} (i : Fin a) (j : Fin b) :
    convolution (K := K) a b i j (convolutionOutput i j) = 1 := by
  simp [convolutionOutput]



theorem convolution_nonzero {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    convolution (K := K) a b ≠ 0 := by
  intro hz
  have hc := congrFun (congrFun (congrFun hz ⟨0, ha⟩) ⟨0, hb⟩)
    (convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩)
  change convolution (K := K) a b ⟨0, ha⟩ ⟨0, hb⟩
    (convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩) = 0 at hc
  rw [convolution_at_output] at hc
  exact one_ne_zero hc



/-- Commuting the two inputs only casts the equal output dimensions. -/
theorem convolution_comm (a b : ℕ) (i : Fin a) (j : Fin b)
    (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k =
      convolution (K := K) b a j i (Fin.cast (by omega) k) := by
  simp only [convolution, Fin.val_cast, Nat.add_comm]









/-- `C(1,b)` is the dot-product tensor with the singleton on the first leg. -/
theorem convolution_one_left_dotPairing (b : ℕ) :
    Tensor.pullback convolutionOneInputEquiv (Equiv.refl (Fin b))
      (convolutionOneOutputEquiv b) (convolution (K := K) 1 b) =
      Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin b))) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff]







end MatrixMultiplication.AuxiliarySeparation

end OAI

end Module0


section Module1
namespace OAI
variable {K : Type*} [Field K]

/-!
# Polynomial convolution (K := K) by evaluation and interpolation

Evaluating the two input polynomials at `a + b - 1` distinct complex points,
then interpolating their product, expresses the convolution (K := K) tensor as a sum
of `a + b - 1` rank-one tensors. This is the polynomial multiplication rank
upper bound used in Section 5.
-/

open scoped BigOperators
open Polynomial

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Recover each monomial coefficient from evaluations at distinct nodes. -/
lemma monomial_coeff_eq_sum_interpolation {n m : ℕ} (hm : m < n)
    (v : Fin n → K) (hv : Function.Injective v) (k : ℕ) :
    (if m = k then (1 : K) else 0) =
      ∑ r : Fin n, v r ^ m * (Lagrange.basis Finset.univ v r).coeff k := by
  have hdeg : (X ^ m : K[X]).degree < (Finset.univ : Finset (Fin n)).card := by
    simpa using hm
  have hpoly := Lagrange.eq_interpolate (f := (X ^ m : K[X])) hv.injOn hdeg
  have hcoeff := congrArg (fun p : K[X] => p.coeff k) hpoly
  simpa only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow, eq_comm] using hcoeff

/-- Evaluation at distinct nodes and Lagrange interpolation give an explicit
rank-one decomposition of polynomial convolution. -/
theorem convolution_eq_sum_rankOne {a b : ℕ}
    (v : Fin (a + b - 1) → K) (hv : Function.Injective v) :
    convolution (K := K) a b = fun i j k => ∑ r : Fin (a + b - 1),
      Tensor.rankOne (fun i : Fin a => v r ^ i.val)
        (fun j : Fin b => v r ^ j.val)
        (fun k : Fin (a + b - 1) => (Lagrange.basis Finset.univ v r).coeff k.val)
        i j k := by
  funext i j k
  have hij : i.val + j.val < a + b - 1 := (convolutionOutput i j).isLt
  simpa only [convolution_apply, Tensor.rankOne, pow_add] using
    monomial_coeff_eq_sum_interpolation hij v hv k.val

/-- The convolution (K := K) tensor `C(a,b)` has rank at most `a + b - 1` over `K`. -/
theorem convolution_rankAtMost [Infinite K] (a b : ℕ) :
    Tensor.RankAtMost (convolution (K := K) a b) (a + b - 1) := by
  let v : Fin (a + b - 1) → K := fun i => Infinite.natEmbedding K i.val
  have hv : Function.Injective v := by
    intro i j h
    exact Fin.ext ((Infinite.natEmbedding K).injective h)
  rw [convolution_eq_sum_rankOne v hv]
  simpa using Tensor.rankAtMost_sum_rankOne
    (fun r (i : Fin a) => v r ^ i.val)
    (fun r (j : Fin b) => v r ^ j.val)
    (fun r (k : Fin (a + b - 1)) => (Lagrange.basis Finset.univ v r).coeff k.val)

end MatrixMultiplication.AuxiliarySeparation

end OAI

end Module1


section Module2
namespace OAI
variable {K : Type*} [Field K]

/-!
# Exact rank of polynomial convolution

Each output coefficient of polynomial multiplication occurs in some product
of two input monomials. Choosing one such pair for each output gives an
identity minor in the output flattening. Together with evaluation and
interpolation, this proves the exact rank of `C(a,b)` for positive dimensions.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation







end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end Module2



end AllFieldsModule11
/- END all-fields module GenericConvolution -/

/- BEGIN all-fields module GenericProfile -/
section AllFieldsModule13


section ProfileModule0

namespace OAI

/-!
# The symmetrized tensor-character product

The sixfold product is defined on arbitrary finite, possibly different, leg
spaces. Its symmetry follows by permuting the factors and requires no symmetry
of the character itself.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character 𝕜))
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']



/-- Cycling the legs permutes the six factors. -/
theorem sixfoldProduct_cyclic (T : Tensor 𝕜 X Y Z) :
    χ.sixfoldProduct (fun y z x => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- Exchanging the first two legs permutes the six factors. -/
theorem sixfoldProduct_swap12 (T : Tensor 𝕜 X Y Z) :
    χ.sixfoldProduct (fun y x z => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring





/-- Commuting convolution inputs preserves the sixfold character product. -/
theorem sixfoldProduct_convolution_comm (a b : ℕ) :
    χ.sixfoldProduct (convolution a b) = χ.sixfoldProduct (convolution b a) := by
  let e : Fin (a + b - 1) ≃ Fin (b + a - 1) := finCongr (by omega)
  have heq : Tensor.pullback (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
      (convolution (K := 𝕜) b a) = fun j i k => convolution a b i j k := by
    funext j i k
    exact (convolution_comm a b i j k).symm
  have h := χ.sixfoldProduct_reindex (convolution b a)
    (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
  rw [heq, (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_swap12 χ)] at h
  exact h











end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end ProfileModule0


section ProfileModule1

namespace OAI

/-!
# Algebra and bounds for the sixfold character product

The product over all six leg orders is multiplicative and nonnegative. A
nonzero tensor has product at least one, and every rank decomposition bounds
the product by the sixth power of its size.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character 𝕜))
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]



/-- All six factors of the symmetrized product are nonnegative. -/
theorem sixfoldProduct_nonneg (T : Tensor 𝕜 X Y Z) : 0 ≤ χ.sixfoldProduct T := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (χ.nonneg T) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)



/-- In particular, the sixfold product of a nonzero tensor is positive. -/
theorem sixfoldProduct_pos {T : Tensor 𝕜 X Y Z} (hT : T ≠ 0) :
    0 < χ.sixfoldProduct T :=
  zero_lt_one.trans_le (χ.one_le_sixfoldProduct hT)





end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end ProfileModule1


section ProfileModule2

namespace OAI

/-!
# Positivity and rank bounds for the normalized profile

The normalization exponent is positive when the mean singleton-leg exponent
is positive. Under this hypothesis, passing to the profile preserves order,
and a rank bound `r` becomes the bound `r ^ (1 / t)`.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character 𝕜))
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]



theorem symmetrizedProfile_pos (t : ℝ) {T : Tensor 𝕜 X Y Z} (hT : T ≠ 0) :
    0 < χ.symmetrizedProfile t T :=
  Real.rpow_pos_of_pos ((_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_pos χ) hT) _







/-- The symmetrized profile has the rank bound used in Section 5. -/
theorem symmetrizedProfile_le_rank {t : ℝ} (ht : 0 < t)
    {T : Tensor 𝕜 X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.symmetrizedProfile t T ≤ (r : ℝ) ^ (1 / t) := by
  calc
    χ.symmetrizedProfile t T ≤ ((r : ℝ) ^ 6) ^ (1 / (6 * t)) :=
      Real.rpow_le_rpow ((_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_nonneg χ) T) (χ.sixfoldProduct_le_rank h)
        (by positivity)
    _ = (r : ℝ) ^ (1 / t) := by
      rw [← Real.rpow_natCast (r : ℝ) 6, ← Real.rpow_mul (by positivity)]
      congr 1
      field_simp
      norm_num



end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end ProfileModule2


section ProfileModule3

namespace OAI

/-!
# (Character 𝕜) identities for polynomial convolution

The boundary convolution tensors are dot products. In the sixfold character
product, each possible singleton leg appears exactly twice. Consequently the
normalization by the average dot-product exponent gives the boundary values
of the polynomial profile from Section 5.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character 𝕜))



/-- The boundary `C(1,b)` has the sixfold product of a dot product. -/
theorem sixfoldProduct_convolution_one_left (b : ℕ) :
    χ.sixfoldProduct (convolution 1 b) =
      χ.sixfoldProduct (Tensor.dotPairing (K := 𝕜) (Fin b)) := by
  have h := χ.sixfoldProduct_reindex (convolution 1 b)
    convolutionOneInputEquiv (Equiv.refl (Fin b)) (convolutionOneOutputEquiv b)
  rw [convolution_one_left_dotPairing] at h
  calc
    _ = χ.sixfoldProduct (Tensor.cyclic (Tensor.cyclic
        (Tensor.dotPairing (K := 𝕜) (Fin b)))) := h.symm
    _ = χ.sixfoldProduct (Tensor.cyclic (Tensor.dotPairing (K := 𝕜) (Fin b))) :=
      (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_cyclic χ) _
    _ = _ := (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_cyclic χ) _









/-- The three exponents occur twice in the sixfold boundary product. -/
theorem sixfoldProduct_dotPairing_eq_rpow {n : ℕ} (hn : 0 < n) :
    χ.sixfoldProduct (Tensor.dotPairing (K := 𝕜) (Fin n)) =
      (n : ℝ) ^ (6 * χ.meanExponent) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [χ.sixfoldProduct_dotPairing, (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing χ) hn,
    (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_cyclic_dotPairing χ) hn, (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_cyclic_cyclic_dotPairing χ) hn,
    ← Real.rpow_add hn', ← Real.rpow_add hn']
  calc
    ((n : ℝ) ^ (χ.pZ + χ.pY + χ.pX)) ^ 2 =
        (n : ℝ) ^ ((χ.pZ + χ.pY + χ.pX) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast hn'.le _ 2).symm
    _ = _ := by congr 1; unfold meanExponent; ring

/-- The positive-size boundary product has its exact normalized power. -/
theorem sixfoldProduct_convolution_one_left_eq_rpow {b : ℕ} (hb : 0 < b) :
    χ.sixfoldProduct (convolution 1 b) = (b : ℝ) ^ (6 * χ.meanExponent) := by
  rw [(_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_convolution_one_left χ), (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_dotPairing_eq_rpow χ) hb]



/-- Swapping the two polynomial inputs preserves the normalized profile. -/
theorem convolutionProfile_comm (a b : ℕ) :
    χ.convolutionProfile a b = χ.convolutionProfile b a := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * χ.meanExponent)))
    ((_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_convolution_comm χ) a b)



/-- Nonzero polynomial multiplication gives a positive normalized profile. -/
theorem convolutionProfile_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.convolutionProfile a b :=
  (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.symmetrizedProfile_pos χ) _ (convolution_nonzero ha hb)

/-- The evaluation/interpolation algorithm bounds the normalized profile. -/
theorem convolutionProfile_le {a b : ℕ} (ht : 0 < χ.meanExponent) :
    χ.convolutionProfile a b ≤ (a + b - 1 : ℕ) ^ (1 / χ.meanExponent) :=
  (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.symmetrizedProfile_le_rank χ) ht (convolution_rankAtMost a b)

/-- The normalization gives the exact initial value `P(1,b) = b`. -/
theorem convolutionProfile_one_left {b : ℕ} (ht : 0 < χ.meanExponent) (hb : 0 < b) :
    χ.convolutionProfile 1 b = b := by
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  unfold convolutionProfile symmetrizedProfile
  rw [(_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sixfoldProduct_convolution_one_left_eq_rpow χ) hb, ← Real.rpow_mul hb'.le]
  rw [show (6 * χ.meanExponent) * (1 / (6 * χ.meanExponent)) = 1 by
    field_simp [ne_of_gt ht]]
  exact Real.rpow_one _







end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end ProfileModule3


section ProfileModule4

namespace OAI

/-!
# The six permuted tensor characters

Precomposing a character with a leg permutation gives another character. The
six resulting values multiply to the symmetrized product, and each singleton
leg exponent occurs twice among their first-leg exponents.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable (χ : (Character 𝕜))























end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end ProfileModule4


end AllFieldsModule13
/- END all-fields module GenericProfile -/

/- BEGIN all-fields module GenericBound -/
section AllFieldsModule26


section BoundModule0

namespace OAI

/-!
# The inequalities for the polynomial profile

The six character values are combined before the common probability law is
optimized. Each first-leg exponent occurs twice, so the total entropy exponent
is exactly six times the mean exponent used to normalize the profile.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable (χ : (Character 𝕜))













/-- The polynomial profile satisfies every hypothesis of the scalar growth theorem. -/
def toScalarProfile (ht : 0 < χ.meanExponent) : ScalarProfile χ.meanExponent where
  value := χ.convolutionProfile
  positive a b ha hb := (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolutionProfile_pos χ) (by omega) (by omega)
  symmetric a b _ _ := (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolutionProfile_comm χ) a b
  boundary b hb := (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolutionProfile_one_left χ) ht (by omega)
  concave a b ha hb := χ.convolutionProfile_concave ht (by omega) hb
  tripling a h ha hh := χ.convolutionProfile_tripling ht (by omega) (by omega)
  rank_bound a b ha hb := by
    have h := _root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolutionProfile_le χ (a := a) (b := b) ht
    have hab : 1 ≤ a + b := by omega
    simpa only [Nat.cast_sub hab, Nat.cast_add, Nat.cast_one] using h

/-- Every actual tensor character has mean singleton-leg exponent at most `3/4`. -/
theorem meanExponent_le_three_quarters : χ.meanExponent ≤ 3 / 4 := by
  by_cases ht : 0 < χ.meanExponent
  · exact ((_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.toScalarProfile χ) ht).exponent_le_three_quarters ht
  · have hle : χ.meanExponent ≤ 0 := le_of_not_gt ht
    linarith

/-- The three dot-product exponents of an actual character sum to at most `9/4`. -/
theorem exponent_sum_le_nine_quarters : χ.pX + χ.pY + χ.pZ ≤ 9 / 4 := by
  have h := (_root_.OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.meanExponent_le_three_quarters χ)
  unfold meanExponent at h
  linarith

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end BoundModule0


section BoundModule1

namespace OAI

/-!
# Integer rounding in the detecting-character argument

The character used at a matrix size may depend on that size. A uniform bound
on all those characters is enough: the loss of one in rounding their target
values cannot change a positive power exponent. The character-existence and
character-growth assumptions remain explicit in the final implications.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

open MatrixMultiplication.Foundation















end MatrixMultiplication.AuxiliarySeparation

end OAI

end BoundModule1


section BoundModule2

namespace OAI

/-!
# The exact-rank exponent bound

Detecting characters exist by Appendix A. The determinant and three-sector
polynomial constructions bound the sum of their dot-product exponents by
`9/4`. Integer rounding then gives the same bound for the exact-rank exponent.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]



end MatrixMultiplication.AuxiliarySeparation

end OAI

end BoundModule2




end AllFieldsModule26
/- END all-fields module GenericBound -/

end OAIExtractedProof_b6058a9b2e46

theorem solution.{u_1} :
    ∀ {𝕜 : Type u_1} [inst : Field 𝕜] [IsAlgClosed 𝕜] (χ : OAI.MatrixMultiplication.AuxiliarySeparation.Character 𝕜),
  χ.pX + χ.pY + χ.pZ ≤ 9 / 4
:= @OAIExtractedProof_b6058a9b2e46.OAI.MatrixMultiplication.AuxiliarySeparation.Character.exponent_sum_le_nine_quarters
