-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.Sector.branchFamily_labels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:22:10.862035+00:00
-- url     : https://prove2.me/submissions/2b582d36-e4b4-41b0-a9d8-0d0312cd8e8e

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
import Definitions.Def_OAI429_GenericSectorAlgebra
import Definitions.Def_OAI429_GenericSectorCharacter
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical
namespace OAIAllFieldsSeparation
end OAIAllFieldsSeparation

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Sector
end OAI.MatrixMultiplication.AuxiliarySeparation.Sector
open OAI.MatrixMultiplication.AuxiliarySeparation.Sector

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Sector.LeftBranch
end OAI.MatrixMultiplication.AuxiliarySeparation.Sector.LeftBranch
open OAI.MatrixMultiplication.AuxiliarySeparation.Sector.LeftBranch

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Sector.MiddleBranch
end OAI.MatrixMultiplication.AuxiliarySeparation.Sector.MiddleBranch
open OAI.MatrixMultiplication.AuxiliarySeparation.Sector.MiddleBranch

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Sector.RightBranch
end OAI.MatrixMultiplication.AuxiliarySeparation.Sector.RightBranch
open OAI.MatrixMultiplication.AuxiliarySeparation.Sector.RightBranch

open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_429525806cee


set_option linter.all false

set_option autoImplicit false

/- BEGIN all-fields module GenericSectorAlgebra -/
section AllFieldsModule23
set_option autoImplicit false

section Module0
namespace OAI

/-!
# Interval weights for the three-sector convolution degeneration

Section 5.2 assigns weights to the second and third coordinates of
`C(a, 3 * h + a - 1)`. The total weight is nonnegative on convolution support,
and its zero set consists exactly of the three matching sector blocks.
The middle block is a convolution with the last two legs exchanged and the
first coordinate reversed.
-/

namespace MatrixMultiplication.AuxiliarySeparation.Sector









































/-- The left block preserves the actual first coordinate. -/
theorem leftBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    LeftBranch a h i j k ↔ j < h ∧ k < h + a - 1 := by
  rcases hs with ⟨hi, hj, hk⟩
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hleft, _⟩
    exact ⟨i, j, hi, hleft, rfl, rfl, hk⟩

/-- The middle support equation becomes convolution after reversing the first
coordinate and exchanging the second and third legs. -/
theorem middleBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    MiddleBranch a h i j k ↔ MiddleY a h j ∧ MiddleZ a h k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold MiddleY MiddleZ rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hy, hz⟩
    refine ⟨a - 1 - i, k - (h + a - 1), ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The right block is the same convolution after translating the two outer
coordinates. -/
theorem rightBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    RightBranch a h i j k ↔ rightStart a h ≤ j ∧ rightStart a h ≤ k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold sourceWidth at hj
  unfold RightBranch rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hjr, hkr⟩
    refine ⟨i, j - (2 * h + a - 1), hi, ?_, rfl, ?_, ?_⟩ <;> omega









/-- Every displayed left-branch term belongs to the original convolution. -/
theorem LeftBranch.support {a h i j k : ℕ} (hb : LeftBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed middle-branch term belongs to the original convolution. -/
theorem MiddleBranch.support {a h i j k : ℕ} (hb : MiddleBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed right-branch term belongs to the original convolution. -/
theorem RightBranch.support {a h i j k : ℕ} (hb : RightBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth rightStart
  omega



















end MatrixMultiplication.AuxiliarySeparation.Sector

end OAI

end Module0

section Module1
namespace OAI
variable {K : Type*} [Field K]

/-!
# The actual three-sector polynomial (K := K) degeneration

The interval weights of `SectorWeights` act by diagonal local maps on the
coefficient tensor `C(a, 3h+a-1)`. Shifting every third-leg weight by one makes
the local maps polynomial. Their restriction (K := K) is exactly `X * retained +
X^2 * erased`, so the existing polynomial-restriction (K := K) degeneration interface
applies with leading order one and local degree bounds `(0,1,1)`.
-/

noncomputable section

open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation.Sector

open MatrixMultiplication.Foundation
open Polynomial
























































end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI

end Module1



end AllFieldsModule23
/- END all-fields module GenericSectorAlgebra -/

/- BEGIN all-fields module GenericSectorCharacter -/
section AllFieldsModule25
set_option autoImplicit false
open OAIAllFieldsSeparation
namespace OAI
variable {K : Type*} [Field K] [IsAlgClosed K]

/-!
# The character inequality from the three-sector degeneration

The retained (K := K) tensor has three branches sharing its actual first-input space.
Their two remaining coordinate intervals determine matching branch labels.
The uniform three-branch tag inequality and polynomial degeneration then yield
the character inequality of Section 5.2 before symmetrization.
-/

noncomputable section

open scoped BigOperators Classical
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation.Sector













/-- Every nonzero branch coefficient lies in the two matching labelled sectors. -/
theorem branchFamily_labels (a h : ℕ) (b : Fin 3) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) (hn : branchFamily (K := K) a h b i j k ≠ 0) :
    yLabel a h j = b ∧ zLabel a h k = b := by
  fin_cases b
  · have hb : LeftBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, leftTensor, hb])
    have h := (leftBranch_iff (_root_.OAIExtractedProof_429525806cee.OAI.MatrixMultiplication.AuxiliarySeparation.Sector.LeftBranch.support hb)).mp hb
    simp [yLabel, zLabel, h.1, h.2]
  · have hb : MiddleBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, middleTensor, hb])
    rcases (middleBranch_iff (_root_.OAIExtractedProof_429525806cee.OAI.MatrixMultiplication.AuxiliarySeparation.Sector.MiddleBranch.support hb)).mp hb with ⟨⟨hy₀, hy₁⟩, ⟨hz₀, hz₁⟩⟩
    simp [yLabel, zLabel, not_lt.mpr hy₀, hy₁, not_lt.mpr hz₀, hz₁]
  · have hb : RightBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, rightTensor, hb])
    rcases (rightBranch_iff (_root_.OAIExtractedProof_429525806cee.OAI.MatrixMultiplication.AuxiliarySeparation.Sector.RightBranch.support hb)).mp hb with ⟨hy, hz⟩
    have hi := i.isLt
    have hy₀ : h ≤ j.val := by unfold rightStart at hy; omega
    have hz₀ : h + a - 1 ≤ k.val := by unfold rightStart at hz; omega
    simp [yLabel, zLabel, not_lt.mpr hy₀, not_lt.mpr hy,
      not_lt.mpr hz₀, not_lt.mpr hz]













end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI



end AllFieldsModule25
/- END all-fields module GenericSectorCharacter -/

end OAIExtractedProof_429525806cee

theorem solution.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [@IsAlgClosed K inst] (a h : Nat)
  (b : Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (i : Fin a)
  (j : OAI.MatrixMultiplication.AuxiliarySeparation.Sector.YIndex a h)
  (k : OAI.MatrixMultiplication.AuxiliarySeparation.Sector.ZIndex a h),
  @Ne K (@OAI.MatrixMultiplication.AuxiliarySeparation.Sector.branchFamily K inst a h b i j k)
      (@OfNat.ofNat K (nat_lit 0)
        (@Zero.toOfNat0 K
          (@MulZeroClass.toZero K
            (@NonUnitalNonAssocSemiring.toMulZeroClass K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K
                      (@EuclideanDomain.toCommRing K (@Field.toEuclideanDomain K inst)))))))))) →
    And
      (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (OAI.MatrixMultiplication.AuxiliarySeparation.Sector.yLabel a h j) b)
      (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (OAI.MatrixMultiplication.AuxiliarySeparation.Sector.zLabel a h k) b)
:= @OAIExtractedProof_429525806cee.OAI.MatrixMultiplication.AuxiliarySeparation.Sector.branchFamily_labels
