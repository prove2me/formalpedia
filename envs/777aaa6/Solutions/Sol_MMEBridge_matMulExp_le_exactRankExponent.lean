-- Prove2me | solution 1 for MMEBridge.matMulExp_le_exactRankExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:22:11.012636+00:00
-- url     : https://prove2.me/submissions/0219e657-2611-42d4-9168-4c0dea96b0d4

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
import Definitions.Def_OAI429_AllFields
import Definitions.Def_OAI429_GenericRank
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical
namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation

namespace MMEBridge
end MMEBridge
open MMEBridge

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_c0718a48a9e5


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

















theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost (Tensor.matrixMultiplication (K := K) n n n) ((exactMatrixRank K) n) :=
  exactRank_spec _



















theorem exactRankExponentSet_nonempty : (exactRankExponentSet K).Nonempty :=
  ⟨Real.logb 2 ((exactMatrixRank K) 2), 2, le_rfl, rfl⟩





















end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end RankModule4



end AllFieldsModule1
/- END all-fields module GenericRank -/

/- BEGIN all-fields module AllFields -/
section AllFieldsModule40

/-!
Matrix multiplication has exact tensor-rank exponent at most 9/4 over every field.
The algebraically closed construction uses a characteristic-safe Fourier period;
algebraic descent gives the same rank exponent bound over the base field.
-/

set_option autoImplicit false

namespace OAI.MatrixMultiplication




end OAI.MatrixMultiplication




end AllFieldsModule40
/- END all-fields module AllFields -/


section CampaignBridge

set_option maxHeartbeats 200000
universe u
noncomputable section
open PiTensorProduct BigOperators Module
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace MMEBridge
variable {K : Type u} [Field K]





theorem repr_tprod (n : ℕ) (v : ∀ s, MME.MMSpace K n n n s)
    (p : Fin 3 → Fin n × Fin n) :
    (mmTensorBasis K n).repr (tprod K v) p =
      v 0 (p 0) * v 1 (p 1) * v 2 (p 2) := by
  simp [mmTensorBasis, Basis.piTensorProduct_repr_tprod_apply,
    Fin.prod_univ_succ, mmBasis, Pi.basisFun_repr, mul_assoc]
  exact congrArg₂ (· * ·) (Pi.basisFun_repr K _ (v 0) (p 0))
    (congrArg₂ (· * ·) (Pi.basisFun_repr K _ (v 1) (p 1))
      (Pi.basisFun_repr K _ (v 2) (p 2)))


theorem repr_mmTensor (n : ℕ) (p : Fin 3 → Fin n × Fin n) :
    (mmTensorBasis K n).repr (MME.MMTensor K n n n) p =
      Tensor.matrixMultiplication (K := K) n n n (p 0) (p 1) (p 2) := by
  classical
  simp [MME.MMTensor, map_sum, repr_tprod,
    Tensor.matrixMultiplication, Pi.single_apply, Prod.ext_iff,
    mul_ite, ite_and]
  split_ifs <;> simp_all [eq_comm]


theorem tensorRank_le_of_rankAtMost {n r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixMultiplication (K := K) n n n) r) :
    MME.tensorRank (MME.MMTensor K n n n) ≤ r := by
  classical
  obtain ⟨a, b, c, h⟩ := h
  apply Nat.sInf_le
  let v : Fin r → ∀ s, MME.MMSpace K n n n s := fun j s =>
    match s with
    | ⟨0, _⟩ => a j
    | ⟨1, _⟩ => b j
    | ⟨2, _⟩ => c j
  refine ⟨v, (mmTensorBasis K n).repr.injective ?_⟩
  ext p
  simp only [map_sum, Finsupp.finset_sum_apply, repr_tprod, repr_mmTensor]
  have hp := congrFun (congrFun (congrFun h (p 0)) (p 1)) (p 2)
  exact hp

theorem tensorRank_le_exactMatrixRank (n : ℕ) :
    MME.tensorRank (MME.MMTensor K n n n) ≤ exactMatrixRank K n :=
  tensorRank_le_of_rankAtMost (exactMatrixRank_spec n)

end MMEBridge

namespace MMEBridge
variable {K : Type u} [Field K]

theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))

theorem mme_exponent_range_bddBelow :
    BddBelow (Set.range (fun n : ℕ =>
      if 1 < n then
        Real.log (MME.tensorRank (MME.MMTensor K n n n) : ℝ) / Real.log n
      else 3)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  dsimp only
  split_ifs
  · exact div_nonneg (log_nat_nonneg _) (log_nat_nonneg _)
  · norm_num

theorem matMulExp_le_exactRankExponent : MME.matMulExp K ≤ exactRankExponent K := by
  apply le_csInf (exactRankExponentSet_nonempty (K := K))
  rintro _ ⟨n, hn, rfl⟩
  have hle := ciInf_le (mme_exponent_range_bddBelow (K := K)) n
  have hn1 : 1 < n := by omega
  simp only [if_pos hn1] at hle
  apply hle.trans
  rw [Real.logb]
  apply div_le_div_of_nonneg_right _ (log_nat_nonneg n)
  by_cases hz : MME.tensorRank (MME.MMTensor K n n n) = 0
  · simpa only [hz, Nat.cast_zero, Real.log_zero] using log_nat_nonneg (exactMatrixRank K n)
  · apply Real.log_le_log
    · exact_mod_cast (Nat.pos_of_ne_zero hz)
    · exact_mod_cast (tensorRank_le_exactMatrixRank (K := K) n)


end MMEBridge

end
end CampaignBridge

section CampaignGoal

universe u






end CampaignGoal

end OAIExtractedProof_c0718a48a9e5

theorem solution.{u} :
    ∀ {K : Type u} [inst : Field K], MME.matMulExp K ≤ OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent K
:= @OAIExtractedProof_c0718a48a9e5.MMEBridge.matMulExp_le_exactRankExponent
