-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.not_tensor_add_positive_nat_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:24:47.127328+00:00
-- url     : https://prove2.me/submissions/a432edc2-b106-4c73-85a4-c1b6475e7167

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
import Definitions.Def_OAI429_GenericRank
import Definitions.Def_OAI429_GenericSemiring_Part1
import Definitions.Def_OAI429_GenericSemiring_Part2
import Theorems.Thm_OAI_MatrixMultiplication_Foundation_Tensor_RankAtMost_card_le_of_identity
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
end OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring

namespace OAI.MatrixMultiplication.Foundation.Tensor
end OAI.MatrixMultiplication.Foundation.Tensor
open OAI.MatrixMultiplication.Foundation.Tensor

namespace OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost
end OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost
open OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost

open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_b0149dcc5e79
namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation



set_option linter.all false

set_option autoImplicit false

/- BEGIN all-fields module GenericRank -/
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





theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

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











/-- Independent bijections of the three coordinate sets preserve exact rank. -/
theorem exactRank_reindex {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le (_root_.OAIExtractedProof_b0149dcc5e79.OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost.pullback (exactRank_spec T) ex ey ez))
  have h := exactRank_le
    (_root_.OAIExtractedProof_b0149dcc5e79.OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost.pullback (exactRank_spec (Tensor.pullback ex ey ez T)) ex.symm ey.symm ez.symm)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h















































end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end RankModule4



end AllFieldsModule1
/- END all-fields module GenericRank -/

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


















































































@[simp] theorem rank_classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : rank (classOf T) = exactRank T :=
  exactRank_reindex T _ _ _

theorem rank_mono {T S : (TensorClass K)} (h : T ≤ S) : rank T ≤ rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  exact IsRestriction.rank_le h























end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end OAI



end AllFieldsModule2
/- END all-fields module GenericSemiring -/

/- BEGIN all-fields module GenericCharacters -/
section AllFieldsModule4



/- Tensor/BinaryCharacter -/
section CharacterModule2

namespace OAI

/-!
# (Character K) additivity for binary tensor sums

The summands may have different finite coordinate types.  A binary sum is a
coordinate reindexing of the dependent direct sum over `Bool`.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {K : Type*} [Field K]



end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end CharacterModule2


/- Tensor/DirectSumClass -/
section CharacterModule3

namespace OAI

/-!
# Finite direct sums in the tensor semiring

The tensor class of a block direct sum is the sum of its constituent classes.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.TensorSemiring

variable {K : Type*} [Field K]

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]







end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end OAI

end CharacterModule3


/- Tensor/Characters -/
section CharacterModule4

namespace OAI

/-!
# Concrete tensor characters and the tensor semiring

The coefficient-level character interface and monotone real-valued semiring
homomorphisms on mutual-restriction classes describe the same valuations.
The map `classOf` uses finite natural-number coordinate presentations, so
the construction applies to all finite coordinate types in the character
interface.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]

open TensorSemiring

namespace Character



































end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end CharacterModule4


/- Tensor/Scalar -/
section CharacterModule5

namespace OAI

/-!
# Natural numbers and rank in the tensor semiring

The natural number `r` is the class of the diagonal scalar tensor with `r`
terms.  Consequently, comparison with `r` in the restriction order is exactly
the existence of a rank decomposition with `r` terms.
-/

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]

/-- Splitting the diagonal index set splits its scalar tensor into two blocks. -/
theorem scalarTensor_add_reindex (m n : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      finSumFinEquiv finSumFinEquiv ((scalarTensor (K := K)) (m + n)) =
      sumTensor ((scalarTensor (K := K)) m) ((scalarTensor (K := K)) n) := by
  funext x y z
  simp only [Tensor.pullback, scalarTensor,
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).injective.eq_iff]
  cases x <;> cases y <;> cases z <;> simp [sumTensor, scalarTensor]

/-- A diagonal scalar tensor has its evident decomposition into simple terms. -/
theorem scalarTensor_rankAtMost (r : ℕ) : Tensor.RankAtMost ((scalarTensor (K := K)) r) r := by
  classical
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0), (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- The diagonal flattening also gives the matching lower bound. -/
@[simp] theorem exactRank_scalarTensor (r : ℕ) : exactRank ((scalarTensor (K := K)) r) = r := by
  apply le_antisymm (exactRank_le (scalarTensor_rankAtMost r))
  have h := (exactRank_spec ((scalarTensor (K := K)) r)).card_le_of_identity id id id
    (by intro i j; simp [scalarTensor])
  simpa only [Fintype.card_fin] using h

namespace TensorSemiring

/-- Addition of the diagonal index sets is semiring addition. -/
theorem classOf_scalarTensor_add (m n : ℕ) :
    classOf ((scalarTensor (K := K)) (m + n)) =
      classOf ((scalarTensor (K := K)) m) + classOf ((scalarTensor (K := K)) n) := by
  have h := classOf_eq_of_reindex _ _ _ (scalarTensor_add_reindex (K := K) m n)
  exact h.symm.trans (classOf_sum _ _)

@[simp] theorem classOf_scalarTensor_zero :
    classOf ((scalarTensor (K := K)) 0) = (0 : (TensorClass K)) := by
  have h : (scalarTensor (K := K)) 0 = 0 := by
    funext x
    exact Fin.elim0 x
  rw [h, classOf_zero]

@[simp] theorem classOf_scalarTensor_one :
    classOf ((scalarTensor (K := K)) 1) = (1 : (TensorClass K)) := by
  change classOf ((scalarTensor (K := K)) 1) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))
  apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 1))
    (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
  funext x y z
  simp [Tensor.pullback, scalarTensor, Subsingleton.elim x y, Subsingleton.elim y z]

/-- Natural numbers in the quotient semiring have their intended tensor meaning. -/
@[simp] theorem classOf_scalarTensor (r : ℕ) :
    classOf ((scalarTensor (K := K)) r) = (r : (TensorClass K)) := by
  induction r with
  | zero => exact classOf_scalarTensor_zero
  | succ r ih =>
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ,
        classOf_scalarTensor_one, ih] using
        classOf_scalarTensor_add (K := K) r 1





/-- Rank takes its usual value on natural numbers in the tensor semiring. -/
@[simp] theorem rank_natCast (r : ℕ) : rank (r : (TensorClass K)) = r := by
  rw [← classOf_scalarTensor r, rank_classOf, exactRank_scalarTensor]







end TensorSemiring
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end CharacterModule5




end AllFieldsModule4
/- END all-fields module GenericCharacters -/

/- BEGIN all-fields module GenericSpectrum -/
section AllFieldsModule5



section SpectrumModule0

namespace OAI

/-!
# The rank obstruction behind the preliminary spectral state

The finite catalyst is kept fixed while first tensor powers, then exponent
slack, then the number of copies are varied.  The hypotheses below isolate the
rank inequalities supplied by the catalytic comparison; they do not assert
the existence of a tensor spectrum or the separation argument producing that
comparison.
-/

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜]



















/-- A finite tensor cannot absorb a positive scalar direct summand.  Iterating
such an absorption would place arbitrarily large scalar tensors below one
fixed finite-rank tensor.  This uses rank monotonicity, not rank additivity. -/
theorem not_tensor_add_positive_nat_le_self (D : (TensorSemiring.TensorClass 𝕜))
    {m : ℕ} (hm : 0 < m) : ¬ D + (m : (TensorSemiring.TensorClass 𝕜)) ≤ D := by
  intro h
  have hiter : ∀ n : ℕ, D + ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) ≤ D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        D + (((n + 1) * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) =
            (D + ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜))) + m := by push_cast; ring
        _ ≤ D + (m : (TensorSemiring.TensorClass 𝕜)) := TensorSemiring.add_mono ih le_rfl
        _ ≤ D := h
  let n := TensorSemiring.rank D + 1
  have hscalar : ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) ≤ D := by
    have hleft := TensorSemiring.add_mono (TensorSemiring.zero_le D)
      (le_refl ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)))
    have hsmall : ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) ≤
        D + ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) := by
      simpa only [zero_add] using hleft
    exact hsmall.trans (hiter n)
  have hrank : n * m ≤ TensorSemiring.rank D := by
    simpa only [TensorSemiring.rank_natCast] using TensorSemiring.rank_mono hscalar
  have hnm : n ≤ n * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (Nat.succ_le_of_lt hm)
  have hlarge : TensorSemiring.rank D + 1 ≤ TensorSemiring.rank D := hnm.trans hrank
  omega





end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end SpectrumModule0


section SpectrumModule1

namespace OAI

/-!
# Detecting characters for complex matrix multiplication

This proves Lemma 3.1, including Appendix A. Finite inconsistency would
produce a positive scalar-gain catalyst, ruled out by the exact-rank exponent.
A compact normalized state space then yields a multiplicative state, which
transfers to the concrete coefficient-level character interface.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜]

open MatrixMultiplication.Foundation



end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end SpectrumModule1




end AllFieldsModule5
/- END all-fields module GenericSpectrum -/

end OAIExtractedProof_b0149dcc5e79

theorem solution.{u_1} :
    ∀ {𝕜 : Type u_1} [inst : Field 𝕜] (D : OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring.TensorClass 𝕜)
  {m : ℕ}, 0 < m → ¬D + ↑m ≤ D
:= @OAIExtractedProof_b0149dcc5e79.OAI.MatrixMultiplication.AuxiliarySeparation.not_tensor_add_positive_nat_le_self
