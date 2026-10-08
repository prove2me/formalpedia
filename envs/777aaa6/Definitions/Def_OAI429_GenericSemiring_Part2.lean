-- Prove2me | Definitions.Def_OAI429_GenericSemiring_Part2
-- name    : OAI429_GenericSemiring_Part2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-07T06:59:14.092213+00:00
-- url     : https://prove2.me/theorems/aff5d35f-bd7a-40ff-a249-038a10965ed3
-- title:
--   The semiring of tensors modulo mutual restriction (part 2)
-- statement:
--   Finite tensors over a field are identified when each is a linear restriction of the other. Direct sum and tensor product induce addition and multiplication on these equivalence classes, giving a commutative semiring ordered by restriction.
--
--   The construction also makes exact rank and the square matrix multiplication class available on the quotient. The included structural proofs establish that these operations are independent of the chosen presentation.
-- source:
--   Extracted from the verified Lean proof at https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; source module GenericSemiring.

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
import Definitions.Def_OAI429_GenericRank
import Definitions.Def_OAI429_GenericSemiring_Part1
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical


set_option linter.all false

set_option autoImplicit false

/- BEGIN all-fields module GenericSemiring -/
section AllFieldsModule2




namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]















end Algebra


end Tensor
end MatrixMultiplication.Foundation
end OAI


namespace OAI

/-!
# Binary sums of finite coefficient tensors

The coordinate types of the summands may differ.  The identities below give
the explicit changes of coordinates needed for the tensor semiring, together
with the block-diagonal restriction maps.
-/

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {K X Y Z U V W A B C : Type*} [CommSemiring K]



























end MatrixMultiplication.AuxiliarySeparation

end OAI


namespace OAI

/-!
# Finite tensors modulo mutual restriction

Representatives have three natural-number dimensions and complex coefficients.
The order is actual linear restriction, and equality in the quotient is mutual
restriction. In particular, changing coordinates does not change the class.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.TensorSemiring

variable {K : Type*} [Field K]

section Restriction

variable {X Y Z U V W P Q R : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]
variable [Fintype P] [Fintype Q] [Fintype R]























end Restriction



namespace FiniteTensor

















end FiniteTensor

















theorem classOf_eq_of_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (h : Tensor.pullback ex ey ez S = T) : classOf T = classOf S :=
  (congrArg classOf h).symm.trans (classOf_reindex S ex ey ez)

@[simp] theorem classOf_coeff (T : (FiniteTensor K)) : classOf T.coeff = tensorClass T := by
  apply (tensorClass_eq_iff _ _).mpr
  exact ⟨IsRestriction.pullback T.coeff _ _ _, IsRestriction.of_reindex T.coeff _ _ _⟩

instance : Mul (TensorClass K) where
  mul := Quotient.map₂ FiniteTensor.product (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.product_mono hT.1 hS.1,
      FiniteTensor.product_mono hT.2 hS.2⟩)

instance : Add (TensorClass K) where
  add := Quotient.map₂ FiniteTensor.sum (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.sum_mono hT.1 hS.1, FiniteTensor.sum_mono hT.2 hS.2⟩)





theorem classOf_product {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S := by
  symm
  exact classOf_reindex (Tensor.product T S)
    (Equiv.prodCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.prodCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.prodCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)

theorem classOf_sum {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (sumTensor T S) = classOf T + classOf S := by
  symm
  have h := classOf_reindex (sumTensor T S)
    (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
  change classOf (sumTensor (FiniteTensor.ofTensor T).coeff
    (FiniteTensor.ofTensor S).coeff) = _
  have heq : sumTensor (FiniteTensor.ofTensor T).coeff (FiniteTensor.ofTensor S).coeff =
      Tensor.pullback
        (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
        (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
        (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
        (sumTensor T S) := by
    funext x y z
    cases x <;> cases y <;> cases z <;> rfl
  rw [heq]
  exact h

instance : Zero (TensorClass K) := ⟨classOf (0 : Tensor K Empty Empty Empty)⟩
instance : One (TensorClass K) := ⟨classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))⟩

theorem classOf_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    classOf (0 : Tensor K X Y Z) = 0 :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.zero _, IsRestriction.zero _⟩

 theorem class_add_assoc (a b c : (TensorClass K)) : (a + b) + c = a + (b + c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a + tensorClass b) + tensorClass c =
    tensorClass a + (tensorClass b + tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_assoc a.coeff b.coeff c.coeff)

 theorem class_add_comm (a b : (TensorClass K)) : a + b = b + a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a + tensorClass b = tensorClass b + tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_comm a.coeff b.coeff)

 theorem class_add_zero (a : (TensorClass K)) : a + 0 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a + 0 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff + classOf (0 : Tensor K Empty Empty Empty) = classOf a.coeff
  rw [← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (sumTensor_empty_right a.coeff
    (0 : Tensor K Empty Empty Empty))).symm

 theorem class_zero_add (a : (TensorClass K)) : 0 + a = a :=
  (class_add_comm 0 a).trans (class_add_zero a)

 theorem class_mul_assoc (a b c : (TensorClass K)) : (a * b) * c = a * (b * c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a * tensorClass b) * tensorClass c =
    tensorClass a * (tensorClass b * tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_assoc a.coeff b.coeff c.coeff)

 theorem class_mul_comm (a b : (TensorClass K)) : a * b = b * a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a * tensorClass b = tensorClass b * tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_comm a.coeff b.coeff)

 theorem class_mul_one (a : (TensorClass K)) : a * 1 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 1 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (fun (_ _ _ : PUnit.{1}) => (1 : K)) = classOf a.coeff
  rw [← classOf_product]
  exact (classOf_eq_of_reindex _ _ _ (tensorProduct_one_right a.coeff)).symm

 theorem class_one_mul (a : (TensorClass K)) : 1 * a = a :=
  (class_mul_comm 1 a).trans (class_mul_one a)

 theorem class_mul_zero (a : (TensorClass K)) : a * 0 = 0 := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 0 = 0
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (0 : Tensor K Empty Empty Empty) = 0
  rw [← classOf_product]
  have heq : Tensor.product a.coeff (0 : Tensor K Empty Empty Empty) = 0 := by
    funext x y z
    simp [Tensor.product]
  rw [heq, classOf_zero]

 theorem class_zero_mul (a : (TensorClass K)) : 0 * a = 0 :=
  (class_mul_comm 0 a).trans (class_mul_zero a)

 theorem class_left_distrib (a b c : (TensorClass K)) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change tensorClass a * (tensorClass b + tensorClass c) =
    tensorClass a * tensorClass b + tensorClass a * tensorClass c
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product, ← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (product_sumTensor a.coeff b.coeff c.coeff)).symm

 theorem class_right_distrib (a b c : (TensorClass K)) : (a + b) * c = a * c + b * c := by
  rw [class_mul_comm, class_left_distrib, class_mul_comm c a, class_mul_comm c b]

instance : CommSemiring (TensorClass K) where
  add_assoc := class_add_assoc
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero := class_add_zero
  nsmul := nsmulRec
  mul_assoc := class_mul_assoc
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one := class_mul_one
  zero_mul := class_zero_mul
  mul_zero := class_mul_zero
  left_distrib := class_left_distrib
  right_distrib := class_right_distrib

theorem mul_mono {T T' S S' : (TensorClass K)} (hT : T ≤ T') (hS : S ≤ S') :
    T * S ≤ T' * S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.product_mono hT hS

theorem add_mono {T T' S S' : (TensorClass K)} (hT : T ≤ T') (hS : S ≤ S') :
    T + S ≤ T' + S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.sum_mono hT hS

/-- Every tensor class is nonnegative in the restriction order. -/
theorem zero_le (T : (TensorClass K)) : 0 ≤ T := by
  induction T using Quotient.inductionOn with | h T =>
  change (0 : (TensorClass K)) ≤ tensorClass T
  rw [← classOf_coeff T]
  exact (classOf_le_iff _ _).mpr (IsRestriction.zero T.coeff)

instance : OrderBot (TensorClass K) where
  bot := 0
  bot_le := zero_le

instance : IsOrderedAddMonoid (TensorClass K) where
  add_le_add_left _ _ h _c := add_mono h le_rfl

instance : IsOrderedMonoid (TensorClass K) where
  mul_le_mul_left _ _ h _c := mul_mono h le_rfl

instance : IsOrderedRing (TensorClass K) where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    exact mul_mono le_rfl hbc
  mul_le_mul_of_nonneg_right := by
    intro a ha b c hbc
    exact mul_mono hbc le_rfl

/-- Exact rank descends to mutual-restriction classes. -/
def rank : (TensorClass K) → ℕ := Quotient.lift (fun T : (FiniteTensor K) => exactRank T.coeff)
  (by
    intro T S h
    exact le_antisymm (IsRestriction.rank_le h.1) (IsRestriction.rank_le h.2))









/-- Square matrix multiplication as an element of the tensor semiring. -/
def matrixClass (n : ℕ) : (TensorClass K) := classOf (Tensor.matrixMultiplication n n n)











theorem classOf_eq_zero_iff {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : classOf T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hr : IsRestriction T (0 : Tensor K Empty Empty Empty) :=
      ((classOf_eq_iff _ _).mp h).1
    exact hr.eq_zero_of_zero
  · rintro rfl
    exact classOf_zero

instance : Nontrivial (TensorClass K) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have heq : (fun (_ _ _ : PUnit.{1}) => (1 : K)) = 0 :=
    (classOf_eq_zero_iff _).mp h
  have := congrFun (congrFun (congrFun heq PUnit.unit) PUnit.unit) PUnit.unit
  exact one_ne_zero this





end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end OAI



end AllFieldsModule2
/- END all-fields module GenericSemiring -/


