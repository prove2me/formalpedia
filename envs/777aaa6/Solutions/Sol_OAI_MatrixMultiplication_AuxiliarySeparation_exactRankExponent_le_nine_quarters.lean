-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_nine_quarters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:46:20.303321+00:00
-- url     : https://prove2.me/submissions/33dfd4ab-6b0a-4306-bcc1-05433b3d6c58

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
import Definitions.Def_OAI429_GenericPairing
import Definitions.Def_OAI429_GenericRank
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_exponent_sum_le_nine_quarters
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_one_le_value
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_eq_of_nat_mul_sub_bounded
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exists_detecting_character
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_positiveMultiplicative_log_error_bounds
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_rpow_exponent_le_of_nat_bound
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

namespace OAI.MatrixMultiplication.Foundation.Tensor
end OAI.MatrixMultiplication.Foundation.Tensor
open OAI.MatrixMultiplication.Foundation.Tensor

namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation
namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_56511643897a
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


end AllFieldsModule0/- BEGIN all-fields module GenericRank -/
section AllFieldsModule1

set_option autoImplicit false

section RankModule0
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation



namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

































variable [Fintype X] [Fintype Y] [Fintype Z]







end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]







end Pullback

end Tensor
end MatrixMultiplication.Foundation
end OAI

end RankModule0


section RankModule1
namespace OAI.MatrixMultiplication.Foundation.Tensor
variable {K : Type*} [CommSemiring K]


end OAI.MatrixMultiplication.Foundation.Tensor

end RankModule1


section RankModule2
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]



theorem matrixMultiplication_eq_matrixCoefficients (a b c : ℕ) :
    matrixMultiplication (K := K) a b c = matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) := rfl















end Tensor
end MatrixMultiplication.Foundation

end OAI

end RankModule2


section RankModule3
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]







end Tensor
end MatrixMultiplication.Foundation

end

end OAI

end RankModule3


section RankModule4
namespace OAI

/-!
# Exact tensor rank and its matrix multiplication exponent

The rank is the least size of an exact decomposition into simple tensors. The
exponent is the infimum of the finite matrix multiplication rank ratios from
Section 3; no attainment of this real infimum is assumed.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]



























































end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end RankModule4



end AllFieldsModule1
/- END all-fields module GenericRank -/

/- BEGIN all-fields module GenericCharacterCore -/
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
  apply le_antisymm ((_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ) T ex ey ez)
  have h := (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ) (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
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

/- BEGIN all-fields module GenericPairing -/
section AllFieldsModule6
/-! The generic algebraic pairing and symmetrization layers from OAI.
Complex topological border-rank theorems are excluded. All retained algebraic
statements use the original namespaces and are valid over CommSemiring K.
-/
set_option autoImplicit false
section PairingModule0
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Pairing

variable {K U : Type*} [CommSemiring K] [DecidableEq U]







end Pairing

end Tensor
end MatrixMultiplication.Foundation

end OAI

end PairingModule0

section PairingModule1
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]





























section Rectangular

variable {A B C : Type*}







variable [DecidableEq A] [DecidableEq B] [DecidableEq C]















end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end OAI

end PairingModule1

section PairingModule2
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K : Type*} [CommSemiring K]



















variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem pairingTriple_matrixCoefficients :
    pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
      (pairingTripleMatrixZ C A) (pairingTriple (K := K) A B C) =
      matrixCoefficients A B C := by
  funext x y z
  change ((if x.2 = y.1 then (1 : K) else 0) *
    (if z.2 = x.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : ((x.2 = y.1 ∧ z.2 = x.1) ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]





end Tensor
end MatrixMultiplication.Foundation

end OAI

end PairingModule2



end AllFieldsModule6
/- END all-fields module GenericPairing -/

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
  (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pos χ) (dotPairing_ne_zero hm)



theorem value_dotPairing_mono {m n : ℕ} (hmn : m ≤ n) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) ≤
      χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback (Fin.castLE hmn) (Fin.castLE hmn) id
      (Tensor.dotPairing (K := K) (Fin n)) = Tensor.dotPairing (K := K) (Fin m) := by
    funext x y z
    simp [Tensor.pullback, Tensor.dotPairing]
  rw [← heq]
  exact (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_pullback_le χ) _ _ _ _

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
  rw [← heq, (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_reindex χ), χ.map_product]
















theorem value_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) = (m : ℝ) ^ χ.pZ := by
  apply positiveMultiplicative_eq_rpow
    (f := fun m => χ.value (Tensor.dotPairing (K := K) (Fin m)))
    (fun n hn => (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_pos χ) hn)
    (fun m n _ _ => (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_mul χ) m n)
    (fun _ _ _ _ hmn => (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing_mono χ) hmn) hm

theorem value_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m))) =
      (m : ℝ) ^ χ.pY :=
  (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing χ.cyclicCharacter) hm

theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m)))) =
      (m : ℝ) ^ χ.pX :=
  (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing χ.cyclicCharacter.cyclicCharacter) hm

/-- Exact factorization through the three oriented dot products. -/
theorem value_matrixCoefficients {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    χ.value (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) =
      (b : ℝ) ^ χ.pZ * (a : ℝ) ^ χ.pY * (c : ℝ) ^ χ.pX := by
  rw [← Tensor.pairingTriple_matrixCoefficients, (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_reindex χ)]
  simp only [Tensor.pairingTriple, χ.map_product, (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_dotPairing χ) hb,
    (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_cyclic_dotPairing χ) ha, (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_cyclic_cyclic_dotPairing χ) hc]

/-- The character of square matrix multiplication has exponent `pX + pY + pZ`. -/
theorem value_matrixCoefficients_square {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.matrixCoefficients (K := K) (Fin m) (Fin m) (Fin m)) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  rw [(_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_matrixCoefficients χ) hm hm hm]
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [Real.rpow_add hm', Real.rpow_add hm']
  ring

/-- The same power law in the matrix-tensor notation used for exact rank. -/
theorem value_matrixMultiplication {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.matrixMultiplication m m m) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  simpa only [Tensor.matrixMultiplication_eq_matrixCoefficients] using
    (_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_matrixCoefficients_square χ) hm

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

/-- Rounding strictly down works at integers too: use `ceil x - 1`. -/
theorem exists_nat_sub_one_le_lt {x : ℝ} (hx : 0 < x) :
    ∃ k : ℕ, x - 1 ≤ (k : ℝ) ∧ (k : ℝ) < x := by
  have hc : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
  refine ⟨⌈x⌉₊ - 1, ?_, ?_⟩
  · rw [Nat.cast_sub hc]
    norm_num only [Nat.cast_one]
    linarith [Nat.le_ceil x]
  · exact ((Nat.ceil_eq_iff (by omega : ⌈x⌉₊ ≠ 0)).1 rfl).1

/-- An additive loss of one does not affect a comparison to a nonnegative
power exponent. No sign assumption on the exponent on the left is needed. -/
theorem rpow_exponent_le_of_nat_sub_one_bound {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hbound : ∀ d : ℕ, 2 ≤ d → (d : ℝ) ^ ν - 1 ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  by_cases hd2 : 2 ≤ d
  · have h := hbound d hd2
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hpow : 1 ≤ (d : ℝ) ^ τ := Real.one_le_rpow hdreal hτ
    linarith
  · have hd1 : d = 1 := by omega
    simp [hd1]

/-- The integer witnesses in the final rounding argument can vary with `d`. -/
theorem exponent_le_of_integer_rounding {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hround : ∀ d : ℕ, 2 ≤ d →
      ∃ k : ℕ, (d : ℝ) ^ ν - 1 ≤ k ∧ (k : ℝ) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_sub_one_bound hτ
  intro d hd
  obtain ⟨k, hk, hk'⟩ := hround d hd
  exact hk.trans hk'



/-- Explicitly conditional passage from detecting characters to the exponent
bound. The detecting character is allowed to depend on both `d` and `k`. -/
theorem exponent_le_of_detecting_characters {ν τ : ℝ} (hτ : 0 ≤ τ)
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, (k : ℝ) < (d : ℝ) ^ ν →
      ∃ χ : (Character 𝕜), (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d))
    (bound : ∀ χ : (Character 𝕜), ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matrixMultiplication d d d) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply exponent_le_of_integer_rounding hτ
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨k, hk, hk'⟩ :=
    exists_nat_sub_one_le_lt (Real.rpow_pos_of_pos hdpos ν)
  obtain ⟨χ, hχ⟩ := detect d hd k hk'
  exact ⟨k, hk, hχ.trans (bound χ d hd)⟩



/-- The paper's final `ν ≤ 9/4` implication, with its two substantive character
inputs visible rather than incorporated into the definition of `ν`. -/
theorem exactRankExponent_le_nine_quarters_of_characters
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ,
      (k : ℝ) < (d : ℝ) ^ (exactRankExponent 𝕜) →
      ∃ χ : (Character 𝕜), (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d))
    (bound : ∀ χ : (Character 𝕜), ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matrixMultiplication d d d) ≤ (d : ℝ) ^ (9 / 4 : ℝ)) :
    (exactRankExponent 𝕜) ≤ 9 / 4 :=
  exponent_le_of_detecting_characters (by norm_num) detect bound

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

/-- The polynomial inequalities bound the actual exact-rank exponent. -/
theorem exactRankExponent_le_nine_quarters : (exactRankExponent 𝕜) ≤ (9 : ℝ) / 4 := by
  apply exactRankExponent_le_nine_quarters_of_characters
  · intro d hd k hk
    exact exists_detecting_character hd hk
  · intro χ d hd
    rw [(_root_.OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_matrixMultiplication χ) (by omega)]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ d by omega)) χ.exponent_sum_le_nine_quarters

end MatrixMultiplication.AuxiliarySeparation

end OAI

end BoundModule2




end AllFieldsModule26
/- END all-fields module GenericBound -/

end OAIExtractedProof_56511643897a

theorem solution.{u_1} :
    ∀ {𝕜 : Type u_1} [inst : Field 𝕜] [IsAlgClosed 𝕜],
  OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent 𝕜 ≤ 9 / 4
:= @OAIExtractedProof_56511643897a.OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_nine_quarters
