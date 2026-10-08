-- Prove2me | Definitions.Def_OAI429_GenericSemiring_Part1
-- name    : OAI429_GenericSemiring_Part1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-07T06:58:25.669987+00:00
-- url     : https://prove2.me/theorems/e6007ca7-a66e-4a1f-9f75-d2afbb27ec15
-- title:
--   The semiring of tensors modulo mutual restriction (part 1)
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
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical


set_option linter.all false

set_option autoImplicit false

/- BEGIN all-fields module GenericSemiring -/
section AllFieldsModule2


theorem toAntisymmetrization_eq {α : Type*} (r : α → α → Prop)
    [IsPreorder α r] (a b : α) :
    toAntisymmetrization r a = toAntisymmetrization r b ↔ r a b ∧ r b a :=
  Quotient.eq

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]

def composeRestrictionMatrix [Fintype X']
    (D : X'' → X' → K) (A : X' → X → K) : X'' → X → K :=
  fun x'' x => ∑ x', D x'' x' * A x' x

 theorem sum_three_mul [Fintype X] [Fintype Y] [Fintype Z]
    (a : X → K) (b : Y → K) (c : Z → K) (t : K) :
    (∑ x, a x) * (∑ y, b y) * (∑ z, c z) * t =
      ∑ x, ∑ y, ∑ z, a x * b y * c z * t := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]

 theorem sum_six_comm [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (f : X' → Y' → Z' → X → Y → Z → K) :
    (∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z, f x' y' z' x y z) =
      ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z', f x' y' z' x y z := by
  calc
    _ = ∑ p : X' × Y' × Z', ∑ q : X × Y × Z,
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : X × Y × Z, ∑ p : X' × Y' × Z',
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

 theorem sum_interleaved_triples {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X → Y → Z → U → V → W → K) :
    (∑ x, ∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
      ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w, f x y z u v w := by
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
        ∑ y, ∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w) =
            ∑ u, ∑ z, ∑ v, ∑ w, f x y z u v w := by
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem restrict_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : X'' → X' → K) (E : Y'' → Y' → K) (F : Z'' → Z' → K)
    (T : Tensor K X Y Z) :
    restrict D E F (restrict A B C T) =
      restrict (composeRestrictionMatrix D A) (composeRestrictionMatrix E B)
        (composeRestrictionMatrix F C) T := by
  funext x'' y'' z''
  unfold restrict composeRestrictionMatrix
  calc
    _ = ∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z,
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := by
      simp only [Finset.mul_sum]
    _ = ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z',
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := sum_six_comm _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [sum_three_mul]
      apply Finset.sum_congr rfl
      intro x' hx'
      apply Finset.sum_congr rfl
      intro y' hy'
      apply Finset.sum_congr rfl
      intro z' hz'
      ring

theorem restrict_product {U V W U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    restrict (fun (x : X' × U') (u : X × U) => A x.1 u.1 * D x.2 u.2)
      (fun (y : Y' × V') (v : Y × V) => B y.1 v.1 * E y.2 v.2)
      (fun (z : Z' × W') (w : Z × W) => C z.1 w.1 * F z.2 w.2) (product T S) =
      product (restrict A B C T) (restrict D E F S) := by
  funext x' y' z'
  simp only [restrict, product, Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * D x'.2 u) * (B y'.1 y * E y'.2 v) *
          (C z'.1 z * F z'.2 w) * (T x y z * S u v w) :=
      sum_interleaved_triples _
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * B y'.1 y * C z'.1 z * T x y z) *
          (D x'.2 u * E y'.2 v * F z'.2 w * S u v w) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = _ := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

theorem restrict_identity [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) :
    restrict (fun x' x => if x = x' then 1 else 0)
      (fun y' y => if y = y' then 1 else 0)
      (fun z' z => if z = z' then 1 else 0) T = T := by
  calc
    _ = pullback id id id T := (pullback_eq_restrict id id id T).symm
    _ = T := rfl

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

/-- The binary direct sum, with each of its three block labels retained. -/
def sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

/-- The block-diagonal sum of two restriction matrices. -/
def sumRestriction {X' U' : Type*} (f : X' → X → K) (g : U' → U → K) :
    (X' ⊕ U') → (X ⊕ U) → K
  | .inl x', .inl x => f x' x
  | .inr u', .inr u => g u' u
  | _, _ => 0

/-- Independent restrictions of both summands give a restriction of the sum. -/
theorem sumTensor_restrict
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X' → X → K) (g : Y' → Y → K) (h : Z' → Z → K)
    (f' : U' → U → K) (g' : V' → V → K) (h' : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.restrict (sumRestriction f f') (sumRestriction g g')
      (sumRestriction h h') (sumTensor T S) =
      sumTensor (Tensor.restrict f g h T) (Tensor.restrict f' g' h' S) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.restrict, sumRestriction, sumTensor, Fintype.sum_sum_type]

/-- Exchanging the two blocks is a coordinate permutation. -/
theorem sumTensor_comm (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.sumComm X U) (Equiv.sumComm Y V)
      (Equiv.sumComm Z W) (sumTensor S T) = sumTensor T S := by
  funext x y z
  cases x <;> cases y <;> cases z <;> rfl

/-- Reassociating the three blocks is a coordinate permutation. -/
theorem sumTensor_assoc (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.sumAssoc X U A) (Equiv.sumAssoc Y V B)
      (Equiv.sumAssoc Z W C) (sumTensor T (sumTensor S R)) =
      sumTensor (sumTensor T S) R := by
  funext x y z
  rcases x with (x | x) | x <;>
    rcases y with (y | y) | y <;>
    rcases z with (z | z) | z <;> rfl

/-- An empty right summand disappears under its canonical coordinates. -/
theorem sumTensor_empty_right [IsEmpty U] [IsEmpty V] [IsEmpty W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.sumEmpty X U).symm (Equiv.sumEmpty Y V).symm
      (Equiv.sumEmpty Z W).symm (sumTensor T S) = T := by
  rfl





/-- Tensor product distributes over the second binary sum by coordinate
permutation. -/
theorem product_sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.prodSumDistrib X U A).symm
      (Equiv.prodSumDistrib Y V B).symm (Equiv.prodSumDistrib Z W C).symm
      (Tensor.product T (sumTensor S R)) =
      sumTensor (Tensor.product T S) (Tensor.product T R) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, sumTensor]

/-- Exchanging product factors is a coordinate permutation. -/
theorem tensorProduct_comm (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.prodComm X U) (Equiv.prodComm Y V)
      (Equiv.prodComm Z W) (Tensor.product S T) = Tensor.product T S := by
  funext x y z
  simp [Tensor.pullback, Tensor.product, mul_comm]

/-- Reassociating product factors is a coordinate permutation. -/
theorem tensorProduct_assoc (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.prodAssoc X U A) (Equiv.prodAssoc Y V B)
      (Equiv.prodAssoc Z W C) (Tensor.product T (Tensor.product S R)) =
      Tensor.product (Tensor.product T S) R := by
  funext x y z
  simp [Tensor.pullback, Tensor.product, mul_assoc]

/-- Scalar multiplication by one is the right unit for tensor product. -/
theorem tensorProduct_one_right (T : Tensor K X Y Z) :
    Tensor.pullback (Equiv.prodPUnit X).symm (Equiv.prodPUnit Y).symm
      (Equiv.prodPUnit Z).symm
      (Tensor.product T (fun (_ _ _ : PUnit) => (1 : K))) = T := by
  funext x y z
  simp [Tensor.pullback, Tensor.product]



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

/-- `T` is obtained from `S` by three linear maps on its coordinate spaces. -/
def IsRestriction (T : Tensor K X Y Z) (S : Tensor K U V W) : Prop :=
  ∃ (A : X → U → K) (B : Y → V → K) (C : Z → W → K),
    T = Tensor.restrict A B C S

theorem IsRestriction.refl (T : Tensor K X Y Z) : IsRestriction T T := by
  classical
  exact ⟨_, _, _, (Tensor.restrict_identity T).symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.trans {T : Tensor K X Y Z} {S : Tensor K U V W}
    {L : Tensor K P Q R} (hTS : IsRestriction T S) (hSL : IsRestriction S L) :
    IsRestriction T L := by
  rcases hTS with ⟨A, B, C, rfl⟩
  rcases hSL with ⟨D, E, F, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix A D, Tensor.composeRestrictionMatrix B E,
    Tensor.composeRestrictionMatrix C F, Tensor.restrict_restrict D E F A B C L⟩

omit [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.pullback (T : Tensor K X Y Z)
    (fx : U → X) (fy : V → Y) (fz : W → Z) :
    IsRestriction (Tensor.pullback fx fy fz T) T := by
  classical
  exact ⟨_, _, _, Tensor.pullback_eq_restrict fx fy fz T⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.of_reindex (T : Tensor K X Y Z)
    (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    IsRestriction T (Tensor.pullback ex ey ez T) := by
  have h := IsRestriction.pullback (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  rwa [heq] at h

theorem IsRestriction.reindex_iff
    (T : Tensor K X Y Z) (S : Tensor K U V W)
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype U'] [Fintype V'] [Fintype W']
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z)
    (eu : U' ≃ U) (ev : V' ≃ V) (ew : W' ≃ W) :
    IsRestriction (Tensor.pullback ex ey ez T) (Tensor.pullback eu ev ew S) ↔
      IsRestriction T S := by
  constructor
  · intro h
    exact (IsRestriction.of_reindex T ex ey ez).trans
      (h.trans (IsRestriction.pullback S eu ev ew))
  · intro h
    exact (IsRestriction.pullback T ex ey ez).trans
      (h.trans (IsRestriction.of_reindex S eu ev ew))

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.product {T : Tensor K X Y Z} {S : Tensor K U V W}
    {T' : Tensor K P Q R} {U' V' W' : Type*}
    [Fintype U'] [Fintype V'] [Fintype W'] {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (Tensor.restrict_product A B C D E F T' S').symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.sum {T : Tensor K X Y Z} {S : Tensor K U V W}
    {T' : Tensor K P Q R} {U' V' W' : Type*}
    [Fintype U'] [Fintype V'] [Fintype W'] {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (sumTensor T S) (sumTensor T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (sumTensor_restrict A B C D E F T' S').symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.zero (S : Tensor K U V W) :
    IsRestriction (0 : Tensor K X Y Z) S := by
  refine ⟨0, 0, 0, ?_⟩
  funext x y z
  simp [Tensor.restrict]

theorem IsRestriction.rank_le {T : Tensor K X Y Z} {S : Tensor K U V W}
    (h : IsRestriction T S) : exactRank T ≤ exactRank S := by
  rcases h with ⟨A, B, C, rfl⟩
  exact exactRank_restrict_le S A B C

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.eq_zero_of_zero {T : Tensor K X Y Z}
    (h : IsRestriction T (0 : Tensor K U V W)) : T = 0 := by
  rcases h with ⟨A, B, C, h⟩
  funext x y z
  rw [h]
  simp [Tensor.restrict]

end Restriction

/-- A set-sized presentation of any finite complex coefficient tensor. -/
structure FiniteTensor (K : Type*) where
  nx : ℕ
  ny : ℕ
  nz : ℕ
  coeff : Tensor K (Fin nx) (Fin ny) (Fin nz)

namespace FiniteTensor

/-- Replace arbitrary finite coordinate sets by standard finite sets. -/
def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (FiniteTensor K) where
  nx := Fintype.card X
  ny := Fintype.card Y
  nz := Fintype.card Z
  coeff := Tensor.pullback (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T

instance : LE (FiniteTensor K) := ⟨fun T S => IsRestriction T.coeff S.coeff⟩

instance : Preorder (FiniteTensor K) where
  le_refl T := IsRestriction.refl T.coeff
  le_trans _ _ _ := IsRestriction.trans

theorem ofTensor_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    ofTensor T ≤ ofTensor S ↔ IsRestriction T S :=
  IsRestriction.reindex_iff T S _ _ _ _ _ _

def product (T S : (FiniteTensor K)) : (FiniteTensor K) :=
  ofTensor (Tensor.product T.coeff S.coeff)

def sum (T S : (FiniteTensor K)) : (FiniteTensor K) :=
  ofTensor (sumTensor T.coeff S.coeff)

theorem product_mono {T T' S S' : (FiniteTensor K)} (hT : T ≤ T') (hS : S ≤ S') :
    product T S ≤ product T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.product hT hS)

theorem sum_mono {T T' S S' : (FiniteTensor K)} (hT : T ≤ T') (hS : S ≤ S') :
    sum T S ≤ sum T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.sum hT hS)

end FiniteTensor

/-- Finite complex tensors, with two presentations identified exactly when
each is a linear restriction of the other. -/
abbrev TensorClass (K : Type*) [Field K] := Antisymmetrization (FiniteTensor K) (· ≤ ·)

/-- The class of a finite tensor presentation. -/
def tensorClass (T : (FiniteTensor K)) : (TensorClass K) := toAntisymmetrization (· ≤ ·) T

@[simp] theorem tensorClass_eq_iff (T S : (FiniteTensor K)) :
    tensorClass T = tensorClass S ↔ T ≤ S ∧ S ≤ T :=
  toAntisymmetrization_eq (· ≤ ·) T S



/-- The quotient class of a tensor on any three finite coordinate sets. -/
def classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (TensorClass K) := tensorClass (FiniteTensor.ofTensor T)

theorem classOf_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T ≤ classOf S ↔ IsRestriction T S := FiniteTensor.ofTensor_le_iff T S

theorem classOf_eq_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T = classOf S ↔ IsRestriction T S ∧ IsRestriction S T := by
  rw [le_antisymm_iff, classOf_le_iff, classOf_le_iff]

theorem classOf_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    classOf (Tensor.pullback ex ey ez T) = classOf T :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.pullback T ex ey ez,
    IsRestriction.of_reindex T ex ey ez⟩




























































































end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end OAI



end AllFieldsModule2
/- END all-fields module GenericSemiring -/


