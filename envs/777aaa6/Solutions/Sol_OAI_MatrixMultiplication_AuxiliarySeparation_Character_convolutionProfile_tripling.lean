-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolutionProfile_tripling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:45:43.121898+00:00
-- url     : https://prove2.me/submissions/28171795-d6f8-440e-be34-73270e3ae4a1

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
import Definitions.Def_OAI429_GenericPairing
import Definitions.Def_OAI429_GenericProfile
import Definitions.Def_OAI429_GenericRank
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_one_le_value
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Sector_convolution_tripling_tag
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_finite_product_tripling
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

namespace OAIExtractedProof_20ce45d35853
namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation



set_option linter.all false

set_option autoImplicit false

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



@[simp] theorem cyclicCharacter_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    χ.cyclicCharacter.value T = χ.value (Tensor.cyclic T) := rfl








































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







/-- The leg exchange used by the middle convolution branch preserves the product. -/
theorem sixfoldProduct_swap23 (T : Tensor 𝕜 X Y Z) :
    χ.sixfoldProduct (fun x z y => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring















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

































/-- Positive input sizes give a positive individual character value. -/
theorem value_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.value (convolution a b) :=
  zero_lt_one.trans_le (χ.one_le_value (convolution_nonzero ha hb))

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



@[simp] theorem swap23Character_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor 𝕜 X Y Z) :
    χ.swap23Character.value T = χ.value (fun x z y => T x y z) := rfl



/-- The six permuted characters give exactly the sixfold product on any legs. -/
theorem prod_permutedCharacter_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor 𝕜 X Y Z) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value T) = χ.sixfoldProduct T := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change χ.value T * (χ.value (fun y z x => T x y z) *
      (χ.value (fun z x y => T x y z) * (χ.value (fun x z y => T x y z) *
      (χ.value (fun y x z => T x y z) * χ.value (fun z y x => T x y z))))) = _
  unfold sixfoldProduct
  ring

@[simp] theorem cyclicCharacter_pX : χ.cyclicCharacter.pX = χ.pZ := by
  rfl

@[simp] theorem cyclicCharacter_pY : χ.cyclicCharacter.pY = χ.pX := rfl

@[simp] theorem cyclicCharacter_pZ : χ.cyclicCharacter.pZ = χ.pY := rfl





@[simp] theorem swap23Character_pX : χ.swap23Character.pX = χ.pX := by
  unfold pX pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pY : χ.swap23Character.pY = χ.pZ := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pZ : χ.swap23Character.pZ = χ.pY := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

/-- Each singleton-leg exponent occurs twice among the first-leg exponents. -/
theorem sum_permutedCharacter_pX :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 2 * (χ.pX + χ.pY + χ.pZ) := by
  simp [permutedCharacter, Fin.sum_univ_succ]
  ring

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



/-- The exponents of the six permuted characters have the normalization total. -/
theorem sum_permutedCharacter_pX_mean :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 6 * χ.meanExponent := by
  rw [(sum_permutedCharacter_pX χ)]
  unfold meanExponent
  ring

/-- All six factors associated to a positive-size polynomial tensor are positive. -/
theorem permutedCharacter_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (i : Fin 6) : 0 < (χ.permutedCharacter i).value (convolution a b) :=
  value_convolution_pos (χ.permutedCharacter i) ha hb

/-- Exchanging the two output-side positions reorders the six convolution factors. -/
theorem prod_permutedCharacter_swapped_convolution (a b : ℕ) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value
      (fun x z y => convolution a b x y z)) =
    ∏ i : Fin 6, (χ.permutedCharacter i).value (convolution a b) := by
  rw [(prod_permutedCharacter_value χ), (prod_permutedCharacter_value χ)]
  exact (sixfoldProduct_swap23 χ) _



/-- The actual three-sector degeneration triples the normalized profile. -/
theorem convolutionProfile_tripling {a h : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hh : 0 < h) :
    3 * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3 * h + a - 1) := by
  have hsw : (fun i s r => convolution (K := 𝕜) a h i r s) ≠ 0 := by
    intro hz
    apply convolution_nonzero (K := 𝕜) ha hh
    exact congrArg
      (fun T : Tensor 𝕜 (Fin a) (Fin (a + h - 1)) (Fin h) => fun i j k => T i k j) hz
  have h := finite_product_tripling
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a (3 * h + a - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a h))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (fun x z y => convolution a h x y z))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) (sum_permutedCharacter_pX_mean χ)
    (fun i => (permutedCharacter_convolution_pos χ) ha (by omega) i)
    (fun i => (permutedCharacter_convolution_pos χ) ha hh i)
    (fun i => value_pos (χ.permutedCharacter i) hsw)
    (fun i => Sector.convolution_tripling_tag (χ.permutedCharacter i) a h ha hh)
    ((prod_permutedCharacter_swapped_convolution χ) a h)
  simpa only [(prod_permutedCharacter_value χ), convolutionProfile, symmetrizedProfile] using h







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

end OAIExtractedProof_20ce45d35853

theorem solution.{u_1} :
    ∀ {𝕜 : Type u_1} [inst : Field 𝕜] [IsAlgClosed 𝕜] (χ : OAI.MatrixMultiplication.AuxiliarySeparation.Character 𝕜)
  {a h : ℕ}, 0 < χ.meanExponent → 0 < a → 0 < h → 3 * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3 * h + a - 1)
:= @OAIExtractedProof_20ce45d35853.OAI.MatrixMultiplication.AuxiliarySeparation.Character.convolutionProfile_tripling
