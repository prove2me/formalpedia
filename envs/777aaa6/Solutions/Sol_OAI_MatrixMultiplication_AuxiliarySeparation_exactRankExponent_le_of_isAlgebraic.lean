-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:36:57.25753+00:00
-- url     : https://prove2.me/submissions/a76e8f71-4dc3-4e8e-ad09-7ff99abd9eae

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
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_le_of_forall_pow_le_constant_mul_pow
import Theorems.Thm_OAI_MatrixMultiplication_Foundation_Tensor_RankAtMost_card_le_of_identity
import Theorems.Thm_OAI_MatrixMultiplication_Foundation_Tensor_RankAtMost_exists_finite_intermediateField
import Theorems.Thm_OAI_MatrixMultiplication_Foundation_Tensor_RankAtMost_matrixMultiplication_power
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAI.MatrixMultiplication.Foundation.Tensor
end OAI.MatrixMultiplication.Foundation.Tensor
open OAI.MatrixMultiplication.Foundation.Tensor

namespace OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost
end OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost
open OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost

open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_871d3dd41666


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





/-- An identity minor of the output flattening forces the quadratic lower bound. -/
theorem matrixMultiplication_rank_lower {n R : ℕ} (hn : 0 < n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication (K := K) n n n) R) : n ^ 2 ≤ R := by
  let j : Fin n := ⟨0, hn⟩
  have hminor : ∀ i k : Fin n × Fin n,
      Tensor.matrixMultiplication (K := K) n n n (i.2, j) (j, i.1) k =
        if i = k then 1 else 0 := by
    intro i k
    simp [Tensor.matrixMultiplication, Prod.ext_iff, eq_comm]
  have h := hRank.card_le_of_identity
    (fun i : Fin n × Fin n => (i.2, j))
    (fun i : Fin n × Fin n => (j, i.1)) id hminor
  simpa [Fintype.card_prod, pow_two] using h

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ (exactMatrixRank K) n :=
  (matrixMultiplication_rank_lower (K := K)) hn ((exactMatrixRank_spec (K := K)) n)

theorem exactMatrixRank_pos {n : ℕ} (hn : 0 < n) : 0 < (exactMatrixRank K) n :=
  lt_of_lt_of_le (pow_pos hn 2) ((exactMatrixRank_lower (K := K)) hn)









theorem exactRankExponentSet_nonempty : (exactRankExponentSet K).Nonempty :=
  ⟨Real.logb 2 ((exactMatrixRank K) 2), 2, le_rfl, rfl⟩

theorem exactMatrixRank_logb_lower {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ Real.logb n ((exactMatrixRank K) n) := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < ((exactMatrixRank K) n : ℝ) := by
    exact_mod_cast (exactMatrixRank_pos (K := K)) (show 0 < n by omega)
  apply (Real.le_logb_iff_rpow_le hn1 hr).mpr
  rw [Real.rpow_two]
  exact_mod_cast (exactMatrixRank_lower (K := K)) (show 0 < n by omega)



theorem exactRankExponentSet_bddBelow : BddBelow (exactRankExponentSet K) := by
  refine ⟨2, ?_⟩
  rintro τ ⟨n, hn, rfl⟩
  exact (exactMatrixRank_logb_lower (K := K)) hn



theorem exactRankExponent_le_logb {n : ℕ} (hn : 2 ≤ n) :
    (exactRankExponent K) ≤ Real.logb n ((exactMatrixRank K) n) :=
  csInf_le (exactRankExponentSet_bddBelow (K := K)) ⟨n, hn, rfl⟩



/-- Each matrix multiplication tensor has rank at least `n^ν`. -/
theorem exactMatrixRank_rpow_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ (exactRankExponent K) ≤ (exactMatrixRank K) n := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < ((exactMatrixRank K) n : ℝ) := by
    exact_mod_cast (exactMatrixRank_pos (K := K)) (show 0 < n by omega)
  exact (Real.le_logb_iff_rpow_le hn1 hr).mp ((exactRankExponent_le_logb (K := K)) hn)







end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end RankModule4



end AllFieldsModule1
/- END all-fields module GenericRank -/

/- BEGIN all-fields module FiniteRankDescent -/
section AllFieldsModule37

/-!
Finite-extension descent for the exact coefficient-tensor rank used by OAI.
The square of the extension degree is an overhead independent of tensor size.
This lemma alone does not establish the all-fields 9/4 exponent theorem.
-/

noncomputable section
open scoped BigOperators

namespace OAI.MatrixMultiplication.Foundation.Tensor

variable {K E X Y Z I : Type*} [Field K] [Field E] [Algebra K E]
variable [Fintype I]

theorem linear_projection_triple_product
    (b : Module.Basis I K E) (π : E →ₗ[K] K) (a c d : E) :
    π (a * c * d) = ∑ i, ∑ j,
      b.repr a i * b.repr c j * π (b i * b j * d) := by
  conv_lhs => rw [← b.sum_repr a, ← b.sum_repr c]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc,
    mul_smul_comm, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring

theorem RankAtMost.descend_with_projection
    (b : Module.Basis I K E) (π : E →ₗ[K] K) (hπ : π 1 = 1)
    {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost (fun x y z => algebraMap K E (T x y z)) r) :
    RankAtMost T (Fintype.card I * Fintype.card I * r) := by
  classical
  rcases h with ⟨a, c, d, ht⟩
  let aa : (I × I × Fin r) → X → K := fun s x => b.repr (a s.2.2 x) s.1
  let bb : (I × I × Fin r) → Y → K := fun s y => b.repr (c s.2.2 y) s.2.1
  let cc : (I × I × Fin r) → Z → K := fun s z =>
    π (b s.1 * b s.2.1 * d s.2.2 z)
  have heq : T = fun x y z => ∑ s, rankOne (aa s) (bb s) (cc s) x y z := by
    funext x y z
    have hp (t : K) : π (algebraMap K E t) = t := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]
    rw [← hp (T x y z)]
    have hxyz := congrFun (congrFun (congrFun ht x) y) z
    rw [hxyz, map_sum]
    calc
      (∑ t : Fin r, π (rankOne (a t) (c t) (d t) x y z)) =
          ∑ t : Fin r, ∑ i : I, ∑ j : I,
            b.repr (a t x) i * b.repr (c t y) j * π (b i * b j * d t z) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact linear_projection_triple_product b π (a t x) (c t y) (d t z)
      _ = _ := by
        simp only [rankOne, Fintype.sum_prod_type, aa, bb, cc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
  rw [heq]
  convert rankAtMost_sum_rankOne aa bb cc using 1
  simp [Fintype.card_prod, Nat.mul_assoc]

theorem RankAtMost.descend [FiniteDimensional K E]
    {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost (fun x y z => algebraMap K E (T x y z)) r) :
    RankAtMost T (Module.finrank K E ^ 2 * r) := by
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : E) ≠ 0)
  simpa only [Fintype.card_fin, pow_two] using
    _root_.OAIExtractedProof_871d3dd41666.OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost.descend_with_projection (Module.finBasis K E) π hπ h


end OAI.MatrixMultiplication.Foundation.Tensor

end

end AllFieldsModule37
/- END all-fields module FiniteRankDescent -/

/- BEGIN all-fields module AlgebraicRankDescent -/
section AllFieldsModule38

set_option autoImplicit false

noncomputable section

open scoped BigOperators Topology
open Filter

namespace OAI.MatrixMultiplication.Foundation.Tensor

variable {K E X Y Z : Type*} [Field K] [Field E] [Algebra K E]





omit [Algebra K E] in
theorem map_matrixMultiplication (f : K →+* E) (a b c : ℕ) :
    (fun x y z => f (matrixMultiplication (K := K) a b c x y z)) =
      matrixMultiplication (K := E) a b c := by
  funext x y z
  simp only [matrixMultiplication]
  split_ifs <;> simp



/- The same finite extension is used for every tensor power. -/
set_option backward.isDefEq.respectTransparency false in
theorem RankAtMost.algebraic_power_descent
    [Algebra.IsAlgebraic K E] {n r : ℕ}
    (h : RankAtMost (matrixMultiplication (K := E) n n n) r) :
    ∃ C : ℕ, ∀ t : ℕ,
      RankAtMost (matrixMultiplication (K := K) (n ^ t) (n ^ t) (n ^ t))
        (C * r ^ t) := by
  have hmap : RankAtMost
      (fun x y z => algebraMap K E (matrixMultiplication (K := K) n n n x y z)) r := by
    simpa only [map_matrixMultiplication] using h
  obtain ⟨L, hfinite, hL⟩ := hmap.exists_finite_intermediateField
  letI : FiniteDimensional K L := hfinite
  have hL' : RankAtMost (matrixMultiplication (K := L) n n n) r := by
    simpa only [map_matrixMultiplication] using hL
  refine ⟨Module.finrank K L ^ 2, ?_⟩
  intro t
  have hp : RankAtMost (fun x y z =>
      algebraMap K L (matrixMultiplication (K := K) (n ^ t) (n ^ t) (n ^ t) x y z))
        (r ^ t) := by
    simpa only [map_matrixMultiplication] using hL'.matrixMultiplication_power t
  exact _root_.OAIExtractedProof_871d3dd41666.OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost.descend hp

end OAI.MatrixMultiplication.Foundation.Tensor

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open OAI.MatrixMultiplication.Foundation



variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem exactRankExponent_rpow_le_of_algebraic_rank
    [Algebra.IsAlgebraic K E] {n r : ℕ} (hn : 2 ≤ n)
    (h : Tensor.RankAtMost (Tensor.matrixMultiplication (K := E) n n n) r) :
    (n : ℝ) ^ exactRankExponent K ≤ (r : ℝ) := by
  obtain ⟨C, hC⟩ := _root_.OAIExtractedProof_871d3dd41666.OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost.algebraic_power_descent (K := K) h
  apply le_of_forall_pow_le_constant_mul_pow (Nat.cast_nonneg r) (C := (C : ℝ))
  intro t ht
  have hnt : 2 ≤ n ^ t := hn.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have hlower := exactMatrixRank_rpow_lower (K := K) hnt
  have hupper : exactMatrixRank K (n ^ t) ≤ C * r ^ t := exactRank_le (hC t)
  have hbound := hlower.trans (Nat.cast_le.mpr hupper)
  simpa only [Nat.cast_mul, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg n)]
    using hbound

theorem exactRankExponent_le_logb_of_algebraic_rank
    [Algebra.IsAlgebraic K E] {n r : ℕ} (hn : 2 ≤ n)
    (h : Tensor.RankAtMost (Tensor.matrixMultiplication (K := E) n n n) r) :
    exactRankExponent K ≤ Real.logb (n : ℝ) (r : ℝ) := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hrnat : 0 < r :=
    (pow_pos (show 0 < n by omega) 2).trans_le
      (matrixMultiplication_rank_lower (K := E) (by omega) h)
  have hr : 0 < (r : ℝ) := by exact_mod_cast hrnat
  exact (Real.le_logb_iff_rpow_le hn1 hr).mpr
    (exactRankExponent_rpow_le_of_algebraic_rank (K := K) hn h)

/-- Algebraic field extensions do not lower the base field's asymptotic rank exponent. -/
theorem exactRankExponent_le_of_isAlgebraic [Algebra.IsAlgebraic K E] :
    exactRankExponent K ≤ exactRankExponent E := by
  apply le_csInf (exactRankExponentSet_nonempty (K := E))
  rintro τ ⟨n, hn, rfl⟩
  exact exactRankExponent_le_logb_of_algebraic_rank (K := K) hn
    (exactMatrixRank_spec (K := E) n)






end OAI.MatrixMultiplication.AuxiliarySeparation

end

end AllFieldsModule38
/- END all-fields module AlgebraicRankDescent -/

end OAIExtractedProof_871d3dd41666

theorem solution.{u_1, u_2} :
    ∀ {K : Type u_1} {E : Type u_2} [inst : Field K] [inst_1 : Field E] [inst_2 : Algebra K E] [Algebra.IsAlgebraic K E],
  OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent K ≤
    OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent E
:= @OAIExtractedProof_871d3dd41666.OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_of_isAlgebraic
