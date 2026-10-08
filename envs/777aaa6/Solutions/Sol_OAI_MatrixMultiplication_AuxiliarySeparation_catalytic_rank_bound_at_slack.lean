-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.catalytic_rank_bound_at_slack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:27:20.611335+00:00
-- url     : https://prove2.me/submissions/1c42d8f7-668b-4c54-a575-480dadd4b7b5

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
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exactMatrixRank_pow_le
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_floor_rank_power_bounds
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_le_of_eventually_pow_le_linear_mul_pow
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_matrixMultiplication_rankAtMost_cubic
import Theorems.Thm_OAI_MatrixMultiplication_Foundation_Tensor_RankAtMost_card_le_of_identity
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_18653e479a48


set_option linter.all false

set_option autoImplicit false

section AllFieldsModule0/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead -/
section AbstractModule18



namespace OAI

/-!
# Removing polynomial overhead from exponential inequalities

The interpolation argument in Section 4 bounds tensor powers with an extra
linear factor. Such a factor does not change their exponential growth rate.
The statements below include eventual inequalities and constant factors, so
the same argument also removes fixed counting losses in entropy limits.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology





/-- Fixed multiplicative losses disappear on taking exponential growth rates. -/
theorem le_of_eventually_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ C * a ^ j) : b ≤ a := by
  apply le_of_eventually_pow_le_linear_mul_pow (K := 0) (C := C) ha
  simpa only [mul_zero, zero_add] using h







end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule18


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



theorem exactMatrixRank_upper (n : ℕ) : (exactMatrixRank K) n ≤ n ^ 3 :=
  exactRank_le ((matrixMultiplication_rankAtMost_cubic (K := K)) n)

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



@[simp] theorem exactMatrixRank_one : (exactMatrixRank K) 1 = 1 := by
  apply le_antisymm
  · simpa using (exactMatrixRank_upper (K := K)) 1
  · simpa using (exactMatrixRank_lower (K := K) (n := 1)) zero_lt_one





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

theorem exactRankExponent_lower : 2 ≤ (exactRankExponent K) :=
  le_csInf (exactRankExponentSet_nonempty (K := K)) (by
    rintro τ ⟨n, hn, rfl⟩
    exact (exactMatrixRank_logb_lower (K := K)) hn)

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

/-- The rank lower bound includes the one-dimensional boundary case. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (exactRankExponent K) ≤ (exactMatrixRank K) n := by
  by_cases hn2 : 2 ≤ n
  · exact (exactMatrixRank_rpow_lower (K := K)) hn2
  · have hn1 : n = 1 := by omega
    simp [hn1]

/-- A strict upper bound for the infimum is witnessed by an actual finite block. -/
theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : (exactRankExponent K) < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ ((exactMatrixRank K) n : ℝ) < (n : ℝ) ^ τ := by
  obtain ⟨σ, ⟨n, hn, rfl⟩, hσ⟩ :=
    exists_lt_of_csInf_lt (exactRankExponentSet_nonempty (K := K)) hτ
  refine ⟨n, hn, ?_⟩
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < ((exactMatrixRank K) n : ℝ) := by
    exact_mod_cast (exactMatrixRank_pos (K := K)) (show 0 < n by omega)
  exact (Real.logb_lt_iff_lt_rpow hn1 hr).mp hσ



end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end RankModule4



end AllFieldsModule1
/- END all-fields module GenericRank -/

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





/-- At fixed `n` and exponent slack, every admissible matrix rank budget
forces the exponential growth rate of the catalytic comparison.  The constant
`R` is fixed before the tensor-power parameter varies. -/
theorem catalytic_rank_bound_at_slack {d n K R : ℕ}
    (hd : 0 < d) (hn : 1 ≤ n)
    (hbound : ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ, (exactMatrixRank 𝕜) g ≤ n ^ j →
      (exactMatrixRank 𝕜) (d ^ j * g) ≤ R * K ^ j)
    {δ : ℝ} (hδ : 0 < δ) :
    (d : ℝ) ^ (exactRankExponent 𝕜) *
      (n : ℝ) ^ ((exactRankExponent 𝕜) / ((exactRankExponent 𝕜) + δ)) ≤ K := by
  let ν := (exactRankExponent 𝕜)
  let τ := ν + δ
  have hν : 0 ≤ ν := (by norm_num : (0 : ℝ) ≤ 2).trans (exactRankExponent_lower (K := 𝕜))
  have hτ : 0 < τ := add_pos_of_nonneg_of_pos hν hδ
  obtain ⟨u, hu, huR⟩ := (exists_exactMatrixRank_lt_rpow (K := 𝕜))
    (show (exactRankExponent 𝕜) < τ from lt_add_of_pos_right _ hδ)
  apply le_of_eventually_pow_le_const_mul_pow (C := (u : ℝ) ^ ν * R)
    (Nat.cast_nonneg K)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with j hj
  let l := ⌊(j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ⌋₊
  let g := u ^ l
  have hg : 0 < g := pow_pos (by omega) l
  have hf := floor_rank_power_bounds hu hn hτ huR.le j
  change ((exactMatrixRank 𝕜) u : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
    (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l at hf
  have hbudget : (exactMatrixRank 𝕜) g ≤ n ^ j := by
    have hpow : ((exactMatrixRank 𝕜) g : ℝ) ≤ ((exactMatrixRank 𝕜) u : ℝ) ^ l := by
      exact_mod_cast exactMatrixRank_pow_le u l
    have hb := hpow.trans hf.1
    exact_mod_cast hb
  have hrank := hbound j hj g hbudget
  have hsize : (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * g := by
    simpa only [g, Nat.cast_pow] using hf.2
  have hlow := (exactMatrixRank_rpow_lower_of_pos (K := 𝕜)) (mul_pos (pow_pos hd j) hg)
  have hpow_n : ((n : ℝ) ^ (ν / τ)) ^ j =
      ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  calc
    ((d : ℝ) ^ ν * (n : ℝ) ^ (ν / τ)) ^ j =
        (((d ^ j : ℕ) : ℝ) ^ ν) * ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
      rw [mul_pow, Real.rpow_pow_comm (Nat.cast_nonneg d), hpow_n, Nat.cast_pow]
    _ ≤ (((d ^ j : ℕ) : ℝ) ^ ν) * ((u : ℝ) * g) ^ ν := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsize hν)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (u : ℝ) ^ ν * (((d ^ j * g : ℕ) : ℝ) ^ ν) := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg u) (Nat.cast_nonneg g),
        Real.mul_rpow (Nat.cast_nonneg (d ^ j)) (Nat.cast_nonneg g)]
      ring
    _ ≤ (u : ℝ) ^ ν * ((exactMatrixRank 𝕜) (d ^ j * g) : ℝ) :=
      mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (Nat.cast_nonneg u) _)
    _ ≤ (u : ℝ) ^ ν * ((R : ℝ) * (K : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg u) _)
      exact_mod_cast hrank
    _ = ((u : ℝ) ^ ν * R) * (K : ℝ) ^ j := by ring



















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

end OAIExtractedProof_18653e479a48

theorem solution.{u_1} :
    ∀ {𝕜 : Type u_1} [inst : Field 𝕜] {d n K R : ℕ},
  0 < d →
    1 ≤ n →
      (∀ (j : ℕ),
          1 ≤ j →
            ∀ (g : ℕ),
              OAI.MatrixMultiplication.AuxiliarySeparation.exactMatrixRank 𝕜 g ≤ n ^ j →
                OAI.MatrixMultiplication.AuxiliarySeparation.exactMatrixRank 𝕜 (d ^ j * g) ≤ R * K ^ j) →
        ∀ {δ : ℝ},
          0 < δ →
            HPow.hPow (α := ℝ) (↑d) (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent 𝕜) *
                HPow.hPow (α := ℝ) (↑n)
                  (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent 𝕜 /
                    (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent 𝕜 + δ)) ≤
              ↑K
:= @OAIExtractedProof_18653e479a48.OAI.MatrixMultiplication.AuxiliarySeparation.catalytic_rank_bound_at_slack
