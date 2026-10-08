-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolution_concavity_tag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:44:50.852062+00:00
-- url     : https://prove2.me/submissions/4e68849d-3597-46a5-b27a-5d506552afe4

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
import Definitions.Def_OAI429_GenericDeterminantCharacter
import Definitions.Def_OAI429_GenericDeterminantCore
import Definitions.Def_OAI429_GenericDeterminantFiltration
import Definitions.Def_OAI429_GenericNumerics
import Definitions.Def_OAI429_GenericPairing
import Definitions.Def_OAI429_GenericRank
import Definitions.Def_OAI429_GenericSeparation
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_one_le_value
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_sharedFirst_tag
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_value_extendByZero
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_value_polynomialRestrictionDegeneration_le
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_value_sharedFirstTensor_eq_sum
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_DeterminantFiltration_sourceTensor_coordinate_change
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_eq_of_nat_mul_sub_bounded
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_positiveMultiplicative_log_error_bounds
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_tensor_eq_extendByZero_pullback
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical
namespace OAIAllFieldsSeparation
end OAIAllFieldsSeparation

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Character
end OAI.MatrixMultiplication.AuxiliarySeparation.Character
open OAI.MatrixMultiplication.AuxiliarySeparation.Character

namespace OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration
end OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration
open OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation
namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_cf165bcfa0e9
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
  apply le_antisymm (_root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ T ex ey ez)
  have h := _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
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
  _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pos χ (dotPairing_ne_zero hm)



theorem value_dotPairing_mono {m n : ℕ} (hmn : m ≤ n) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) ≤
      χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback (Fin.castLE hmn) (Fin.castLE hmn) id
      (Tensor.dotPairing (K := K) (Fin n)) = Tensor.dotPairing (K := K) (Fin m) := by
    funext x y z
    simp [Tensor.pullback, Tensor.dotPairing]
  rw [← heq]
  exact _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ _ _ _ _

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
  rw [← heq, _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_reindex χ, χ.map_product]
















theorem value_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) = (m : ℝ) ^ χ.pZ := by
  apply positiveMultiplicative_eq_rpow
    (f := fun m => χ.value (Tensor.dotPairing (K := K) (Fin m)))
    (fun n hn => _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_pos χ hn)
    (fun m n _ _ => _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_mul χ m n)
    (fun _ _ _ _ hmn => _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_mono χ hmn) hm



theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m)))) =
      (m : ℝ) ^ χ.pX :=
  _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing (χ.cyclicCharacter.cyclicCharacter) hm







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

/- BEGIN all-fields module GenericNumerics -/
section AllFieldsModule12

set_option autoImplicit false

section CompatibilityAliases

universe u

/- Compatibility aliases: Lean 4.34.1 Init/Core.lean names, proved by their
   Lean 4.33.1 predecessors without changing the source statements. -/




/- From Mathlib 4.34.1 Order/Antisymmetrization.lean, unchanged proof. -/


end CompatibilityAliases



/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy -/
section NumericModule0

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators















namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]





















end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI

end NumericModule0


/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity -/
section NumericModule1

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation































namespace FiniteLaw

variable {A : Type*} [Fintype A]





















end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI

end NumericModule1


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Laws -/
section NumericModule2

namespace OAI

/-!
# Probability laws for the polynomial tensor inequalities

The determinant filtration uses an arbitrary binary law, while the three-sector
filtration uses the uniform law on three branches.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation



@[simp] theorem binaryLaw_zero (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (binaryLaw q hq₀ hq₁).mass 0 = q := by simp [binaryLaw]

@[simp] theorem binaryLaw_one (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (binaryLaw q hq₀ hq₁).mass 1 = 1 - q := by simp [binaryLaw]

/-- The finite-law entropy agrees exactly with the binary entropy convention. -/
theorem binaryLaw_entropy (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    finiteEntropy (binaryLaw q hq₀ hq₁).mass = Real.binEntropy q := by
  simp [finiteEntropy, Fin.sum_univ_two, entropyTerm, Real.binEntropy, Real.log_inv]
  ring

theorem binaryLaw_product (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (f : Fin 2 → ℝ) :
    (∏ i, f i ^ (binaryLaw q hq₀ hq₁).mass i) = f 0 ^ q * f 1 ^ (1 - q) := by
  simp [Fin.prod_univ_two]





end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end NumericModule2


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Optimization -/
section NumericModule3

namespace OAI

/-!
# Entropy optimization for finitely many sectors

The normalized weights `q = A / (A + B)` and `1 - q = B / (A + B)`
make the entropy-weighted geometric mean equal to `A + B`. This is the
scalar identity used in Section 5.1 of the auxiliary-separation argument.
The same calculation also applies to an arbitrary nonempty finite family.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation











end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule3


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.ProductBounds -/
section NumericModule4

namespace OAI

/-!
# Combining the scalar sector bounds

Pointwise character bounds multiply over a finite family of leg orders. After
normalization by the sum of the singleton exponents, the entropy identity gives
the midpoint-concavity bound for the profile.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation





end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule4


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ConcaveSlopes -/
section NumericModule5

namespace OAI

/-!
# Slopes of positive discretely concave sequences

The row sequences in Section 6 have decreasing consecutive increments. A
nonnegative sequence cannot have a negative increment of this kind: every later
increment would be at least as negative. Consequently the increments converge
to a nonnegative limit, and the sequence divided by its index has the same limit.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology















end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule5


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ProfileSlopes -/
section NumericModule6

namespace OAI

/-!
# Shifted tripling and diagonal increments

These are the two estimates on the limiting row slopes used in Section 6.
Iteration retains the additive shift in the tripling inequality. Symmetry
then expresses a diagonal step as one increment in each of two adjacent rows.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology



















end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule6


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison -/
section NumericModule7

namespace OAI

/-!
# Comparing power growth

The last scalar step of the auxiliary-separation argument compares a
fourth-power lower bound for the cube of the diagonal profile with its
dimension upper bound.  Powers of two suffice to compare the exponents, so
the argument needs no asymptotic estimates or approximation of constants.
-/

namespace MatrixMultiplication.AuxiliarySeparation







end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule7


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Profile -/
section NumericModule8

namespace OAI

/-!
# Growth of the scalar profile

This file proves the scalar implication of Section 6 (Lemma 6.1). The profile
properties are explicit hypotheses: the construction of a profile from a tensor
character and the proof of those properties are separate arguments.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology



namespace ScalarProfile









end ScalarProfile



end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule8


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PermutationProduct -/
section NumericModule9

namespace OAI

/-!
# Products over the six permutations of three tensor legs

The symmetrized quantity in Section 5 uses every permutation of the three
tensor legs. Composing by a fixed permutation preserves this product. For
the exponent calculation, each original leg occurs twice in any fixed slot.
These are finite identities; they do not assume that an individual tensor
character is invariant under exchanging its legs.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation



namespace LegPermutation





























end LegPermutation

end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule9


/- OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexFactorialLogBounds -/
section NumericModule10

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology



























end MatrixMultiplication.Foundation

end OAI

end NumericModule10


/- OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteControl -/
section NumericModule11

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation
namespace FiniteControl

open scoped BigOperators















end FiniteControl
end MatrixMultiplication.Foundation

end OAI

end NumericModule11


/- OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexRationalTypes -/
section NumericModule12

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators



namespace RationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]















end RationalLaw



namespace FiniteLaw

variable {A : Type*} [Fintype A]





end FiniteLaw

end MatrixMultiplication.Foundation

end OAI

end NumericModule12


/- OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting -/
section NumericModule13

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]























end MatrixMultiplication.Foundation

end OAI

end NumericModule13


/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy -/
section NumericModule14

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]









































namespace RationalLaw



end RationalLaw

end MatrixMultiplication.Foundation

end OAI

end NumericModule14


/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity -/
section NumericModule15
namespace OAI.MatrixMultiplication.ConditionalLabels
open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology Classical
variable {A : Type*} [Fintype A]



end OAI.MatrixMultiplication.ConditionalLabels

end NumericModule15


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Tag -/
section NumericModule16

namespace OAI

/-!
# The entropy limit for matched types

The finite hypothesis in this file is an inequality at every integral type.
The conclusion follows by first repeating a fixed type, and then approximating
an arbitrary probability law by rational laws. No entropy inequality is
included in the finite hypothesis.
-/

noncomputable section

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

namespace MatrixMultiplication.AuxiliarySeparation

variable {A : Type*} [Fintype A] [DecidableEq A]






















end MatrixMultiplication.AuxiliarySeparation
end
end OAI

end NumericModule16


end AllFieldsModule12
/- END all-fields module GenericNumerics -/

/- BEGIN all-fields module GenericDeterminantFiltration -/
section AllFieldsModule15
set_option autoImplicit false
namespace OAI
variable {K : Type*} [Field K]

/-!
# The finite determinant filtration of polynomial multiplication

The first leg is kept fixed throughout. The second and third legs use the
explicit quotient/kernel vectors of `DeterminantKernel`. The coefficient
identity `adaptedTensor_reconstruct` verifies the actual multiplication on
every basis input; it does not assume a simultaneous triangularization.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation Polynomial

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration































/-! The actual coordinate change from the original two-copy convolution. -/















@[simp] theorem sourceTensor_inl_inl (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor (K := K) d e i (.inl j) (.inl k) =
      convolution (d + 1) (e + 1) i j (Fin.cast (by omega) k) := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift,
    ← pow_add, convolution, eq_comm]

@[simp] theorem sourceTensor_inr_inr (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor (K := K) d e i (.inr j) (.inr k) =
      convolution (d + 1) (e + 1) i j (Fin.cast (by omega) k) := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift,
    ← pow_add, convolution, eq_comm]

@[simp] theorem sourceTensor_inl_inr (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor (K := K) d e i (.inl j) (.inr k) = 0 := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift]

@[simp] theorem sourceTensor_inr_inl (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor (K := K) d e i (.inr j) (.inl k) = 0 := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift]



/-- The source is exactly polynomial convolution (K := K) tensored with a two-coordinate
dot product whose singleton is on the unchanged first leg. -/
theorem sourceTensor_product (d e : ℕ) :
    sourceTensor (K := K) d e =
      Tensor.pullback (fun i : Fin (d + 1) => (i, ())) (originalCoordinate e)
        (fun k => (Fin.cast (by omega) (originalCoordinate (d + e) k).1,
          (originalCoordinate (d + e) k).2))
        (Tensor.product (convolution (d + 1) (e + 1))
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))) := by
  funext i j k
  rcases j with j | j <;> rcases k with k | k <;>
    simp [Tensor.pullback, Tensor.product, Tensor.cyclic, Tensor.dotPairing,
      originalCoordinate]













end MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

end

end OAI



end AllFieldsModule15
/- END all-fields module GenericDeterminantFiltration -/

/- BEGIN all-fields module GenericTags -/
section AllFieldsModule21

open OAIAllFieldsSeparation


section TagModule0

namespace OAI

/-!
# Recovering tensors from their supported coordinate subspaces

If a tensor has support inside three injectively embedded coordinate sets, it
is exactly the extension by zero of its pullback to those sets. Characters
therefore have the same value on the ambient tensor and this smaller tensor.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

open MatrixMultiplication.Foundation
open scoped Classical

variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']



namespace Character

/-- A character ignores ambient coordinates outside a tensor's support. -/
theorem value_eq_pullback_of_support (χ : (Character 𝕜)) (T : Tensor 𝕜 X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    χ.value T = χ.value (Tensor.pullback fx fy fz T) := by
  calc
    χ.value T = χ.value (Tensor.restrict
        (fun x' x => if fx x = x' then 1 else 0)
        (fun y' y => if fy y = y' then 1 else 0)
        (fun z' z => if fz z = z' then 1 else 0)
        (Tensor.pullback fx fy fz T)) :=
      congrArg χ.value (tensor_eq_extendByZero_pullback T fx fy fz hx hy hz hs)
    _ = _ := χ.value_extendByZero _ fx fy fz hx hy hz

end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end TagModule0


section TagModule1

namespace OAI

/-!
# Padding shared-input tensors with different branch dimensions

The finite separation construction uses fixed ambient coordinate spaces on
each leg. A family with a common first leg and varying second and third legs
embeds into that setting without changing any character values. The extra
coordinates introduced by padding have zero coefficients.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable {M : ℕ} {X : Type} {Y Z : Fin M → Type}
variable [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]



















namespace Character





end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule1


section TagModule2

namespace OAI

/-!
# Recovering branch tags from coordinate support

When both non-shared coordinates determine a branch label, adding explicit
matching branch tags does not change a character's value. The tags can be
recovered by independent coordinate maps, and forgetting them recovers the
original coefficientwise sum of branches.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable {M : ℕ} {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]



namespace Character



end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule2


section TagModule3
namespace OAI
noncomputable section
open MatrixMultiplication.Foundation
open scoped BigOperators Topology
namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
namespace Character

variable {I X Y Z : Type} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [Fintype Z]
  {BX BY BZ : I → Type}
  [∀ a, Fintype (BX a)] [∀ a, Fintype (BY a)] [∀ a, Fintype (BZ a)]





end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule3


section TagModule4

namespace OAI

/-!
# The shared-input tensor tag inequality

Exact type words in a power of a matched-sector tensor are obtained by explicit
coordinate pullbacks. Their character values depend only on the type counts.
The finite auxiliary separation inequality therefore supplies the integral
bounds required by the entropy limit.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable {s : ℕ} {X Y Z : Type}
  [Fintype X] [Fintype Y] [Fintype Z]





















section Dependent

variable {U V : Fin s → Type} [∀ a, Fintype (U a)] [∀ a, Fintype (V a)]





end Dependent

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule4


end AllFieldsModule21
/- END all-fields module GenericTags -/

/- BEGIN all-fields module GenericDeterminantCharacter -/
section AllFieldsModule22
set_option autoImplicit false
open OAIAllFieldsSeparation
namespace OAI
variable {K : Type*} [Field K] [IsAlgClosed K]

/-!
# The determinant inequality for an actual tensor character

The shared-input tag inequality is applied to the two concrete branches of the
checked determinant degeneration. All basis changes and the output-dual change
are supplied by `DeterminantFiltration`.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration





theorem branch_support (d e : ℕ) (n : Fin 2) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) (h : branch (K := K) d e n i j k ≠ 0) :
    branchLabel e j = n ∧ branchLabel (d + e) k = n := by
  fin_cases n <;> rcases j with j | j <;> rcases k with k | k <;>
    simp_all [branch, branchLabel]

theorem sum_branch (d e : ℕ) :
    (∑ n, branch (K := K) d e n) = gradedTensor (K := K) d e := by
  funext i j k
  rcases j with j | j <;> rcases k with k | k <;>
    simp [branch, gradedTensor]

theorem branch_ne_zero (d e : ℕ) (he : 0 < e) (n : Fin 2) :
    branch (K := K) d e n ≠ 0 := by
  intro h
  fin_cases n
  · have hv := congrFun (congrFun (congrFun h ⟨0, by omega⟩)
      (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩)
    simp [branch] at hv
  · have hv := congrFun (congrFun (congrFun h ⟨0, by omega⟩)
      (.inr ⟨0, he⟩)) (.inr ⟨0, by omega⟩)
    simp [branch] at hv

end DeterminantFiltration

namespace Character

open DeterminantFiltration

variable (χ : (Character K))

theorem value_determinant_branch_zero (d e : ℕ) :
    χ.value (branch (K := K) d e 0) = χ.value (convolution (d + 1) (e + 2)) := by
  let fz : Fin ((d + 1) + (e + 2) - 1) → Index (d + e) :=
    fun k => .inl (Fin.cast (by omega) k)
  have hfz : Function.Injective fz := by
    intro a b h
    exact Fin.ext (congrArg (fun z : Index (d + e) =>
      match z with | .inl k => k.val | .inr k => k.val) h)
  have hs : ∀ i j k, branch (K := K) d e 0 i j k ≠ 0 →
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
      j ∈ Set.range (Sum.inl : Fin (e + 2) → Index e) ∧ k ∈ Set.range fz := by
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    · exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz]⟩⟩
    all_goals simp [branch] at h
  have hv := _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_eq_pullback_of_support χ (branch (K := K) d e 0) id Sum.inl fz
    Function.injective_id Sum.inl_injective hfz hs
  have ht : Tensor.pullback id Sum.inl fz (branch (K := K) d e 0) =
      convolution (d + 1) (e + 2) := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  simpa only [ht] using hv

theorem value_determinant_branch_one (d e : ℕ) :
    χ.value (branch (K := K) d e 1) = χ.value (convolution (d + 1) e) := by
  let fz : Fin ((d + 1) + e - 1) → Index (d + e) :=
    fun k => .inr (Fin.cast (by omega) k)
  have hfz : Function.Injective fz := by
    intro a b h
    exact Fin.ext (congrArg (fun z : Index (d + e) =>
      match z with | .inl k => k.val | .inr k => k.val) h)
  have hs : ∀ i j k, branch (K := K) d e 1 i j k ≠ 0 →
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
      j ∈ Set.range (Sum.inr : Fin e → Index e) ∧ k ∈ Set.range fz := by
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    any_goals simp [branch] at h
    exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz]⟩⟩
  have hv := _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_eq_pullback_of_support χ (branch (K := K) d e 1) id Sum.inr fz
    Function.injective_id Sum.inr_injective hfz hs
  have ht : Tensor.pullback id Sum.inr fz (branch (K := K) d e 1) =
      convolution (d + 1) e := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  simpa only [ht] using hv

private theorem value_bool_dot :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool))) =
      (2 : ℝ) ^ χ.pX := by
  have hv := _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_reindex χ
    (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))
    (Equiv.refl Unit) finTwoEquiv finTwoEquiv
  have ht : Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv
      (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool))) =
        Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin 2))) := by
    funext i j k
    simp [Tensor.pullback, Tensor.cyclic, Tensor.dotPairing]
  rw [ht] at hv
  exact hv.symm.trans (_root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_cyclic_cyclic_dotPairing χ (by decide))

/-- The auxiliary dot product is charged once, on the actual source tensor. -/
theorem value_determinant_source_le (d e : ℕ) :
    χ.value (sourceTensor (K := K) d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  rw [sourceTensor_product]
  apply (_root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ _ _ _ _).trans_eq
  rw [χ.map_product, value_bool_dot χ]
  ring

/-- Actual basis-change and degeneration (K := K) certificates give this comparison. -/
theorem value_determinant_graded_le (d e : ℕ) :
    χ.value (gradedTensor (K := K) d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  calc
    χ.value (gradedTensor (K := K) d e) ≤ χ.value (adaptedTensor (K := K) d e) :=
      χ.value_polynomialRestrictionDegeneration_le (degeneration (K := K) d e)
    _ ≤ χ.value (sourceTensor (K := K) d e) := by
      simpa only [sourceTensor_coordinate_change] using
        χ.monotone (sourceTensor (K := K) d e) (fixedFirst (K := K) d) (inputChange (K := K) e)
          (outputDualChange (K := K) (d + e))
    _ ≤ _ := _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_determinant_source_le χ d e

/-- The binary tag bound before normalizing over all six characters. -/
theorem convolution_concavity_tag_dims (d e : ℕ) (he : 0 < e)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution (d + 1) (e + 2)) ^ q *
        χ.value (convolution (d + 1) e) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  have ht := χ.sharedFirst_tag (binaryLaw q hq₀ hq₁) (branch (K := K) d e)
    (branch_ne_zero d e he)
  rw [χ.value_sharedFirstTensor_eq_sum (branch (K := K) d e)
    (branchLabel e) (branchLabel (d + e)) (branch_support d e), sum_branch] at ht
  rw [binaryLaw_entropy, binaryLaw_product,
    _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_determinant_branch_zero χ, _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_determinant_branch_one χ] at ht
  apply le_trans (b := χ.value (gradedTensor (K := K) d e))
  · simpa only [mul_assoc] using ht
  · exact _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_determinant_graded_le χ d e

/-- The determinant inequality in the paper's positive-dimension notation. -/
theorem convolution_concavity_tag (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution (K := K) a (b + 1)) ^ q *
        χ.value (convolution (K := K) a (b - 1)) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (K := K) a b) := by
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  obtain ⟨e, rfl, he⟩ : ∃ e, b = e + 1 ∧ 0 < e := ⟨b - 1, by omega, by omega⟩
  simpa [Nat.add_assoc] using _root_.OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolution_concavity_tag_dims χ d e he q hq₀ hq₁

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI



end AllFieldsModule22
/- END all-fields module GenericDeterminantCharacter -/

end OAIExtractedProof_cf165bcfa0e9

theorem solution.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [IsAlgClosed K] (χ : OAI.MatrixMultiplication.AuxiliarySeparation.Character K)
  (a b : ℕ),
  0 < a →
    2 ≤ b →
      ∀ (q : ℝ),
        0 ≤ q →
          q ≤ 1 →
            Real.exp (χ.pX * Real.binEntropy q) *
                  χ.value (Y := Fin (b + 1)) (OAI.MatrixMultiplication.AuxiliarySeparation.convolution a (b + 1)) ^ q *
                χ.value (Y := Fin (b - 1)) (OAI.MatrixMultiplication.AuxiliarySeparation.convolution a (b - 1)) ^
                  (1 - q) ≤
              2 ^ χ.pX * χ.value (OAI.MatrixMultiplication.AuxiliarySeparation.convolution a b)
:= @OAIExtractedProof_cf165bcfa0e9.OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolution_concavity_tag
