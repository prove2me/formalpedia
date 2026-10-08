-- Prove2me | Definitions.Def_OAI429_GenericCharacters
-- name    : OAI429_GenericCharacters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-07T07:01:29.25599+00:00
-- url     : https://prove2.me/theorems/4708b9e1-0733-4002-96cd-86a24ab04558
-- title:
--   Tensor characters induced by homomorphisms on restriction classes
-- statement:
--   A normalized monotone semiring homomorphism from the semiring of mutual-restriction tensor classes to $\mathbb R$ defines a tensor character by evaluating the class of each tensor.
--
--   The constructor packages normalization, direct-sum additivity, tensor-product multiplicativity, and restriction monotonicity in the coefficient-tensor interface.
-- source:
--   Extracted from the verified Lean proof at https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; source module GenericCharacters.

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
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical


set_option linter.all false

set_option autoImplicit false

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

 theorem classOf_directSum_reindex {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (T : κ → Tensor K X Y Z) (e : ι ≃ κ) :
    classOf (Tensor.directSum (fun i => T (e i))) = classOf (Tensor.directSum T) := by
  apply classOf_eq_of_reindex (Equiv.prodCongr e (Equiv.refl X))
    (Equiv.prodCongr e (Equiv.refl Y)) (Equiv.prodCongr e (Equiv.refl Z))
  funext x y z
  simp [Tensor.pullback, Tensor.directSum, e.injective.eq_iff]

 theorem classOf_directSum_option {ι : Type*} [Fintype ι] [di : DecidableEq ι]
    [dopt : DecidableEq (Option ι)]
    (T : Option ι → Tensor K X Y Z) :
    classOf (Tensor.directSum T) =
      classOf (T none) + classOf (Tensor.directSum (fun i => T (some i))) := by
  rw [← classOf_sum]
  symm
  apply classOf_eq_of_reindex optionProdEquiv.symm
    optionProdEquiv.symm optionProdEquiv.symm
  funext x y z
  cases x with
  | inl x =>
    cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]
  | inr x =>
    cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]

/-- Passing to tensor classes converts every finite block direct sum to a sum. -/
theorem classOf_directSum {ι : Type*} [Fintype ι] [dec : DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    classOf (Tensor.directSum T) = ∑ i, classOf (T i) := by
  have hdec : dec = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst dec
  classical
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ T : ι → Tensor K X Y Z,
      classOf (Tensor.directSum T) = ∑ i, classOf (T i)) ?_ ?_ ?_ ι T
  · intro α β _ e ih S
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← classOf_directSum_reindex S e, ih]
    exact e.sum_comp (fun i => classOf (S i))
  · intro S
    have he : (∑ i, classOf (S i)) = 0 := Finset.sum_eq_zero (fun i _ => i.elim)
    rw [he]
    apply (classOf_eq_zero_iff _).mpr
    funext x
    exact x.1.elim
  · intro α _ ih S
    rw [classOf_directSum_option
      (di := fun a b => Classical.propDecidable (a = b))
      (dopt := fun a b => Classical.propDecidable (a = b)), ih, Fintype.sum_option]

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























/-- A monotone semiring homomorphism on tensor classes gives a character on all
finite coefficient tensors. Normalization follows from preservation of `0` and `1`. -/
def ofTensorClassHom (φ : (TensorClass K) →+* ℝ) (hφ : Monotone φ) : (Character K) where
  value := fun T => φ (classOf T)
  nonneg := by
    intro X Y Z hX hY hZ T
    simpa only [φ.map_zero] using hφ (TensorSemiring.zero_le (classOf T))
  map_zero := by
    intro X Y Z hX hY hZ
    rw [classOf_zero]
    exact φ.map_zero
  map_one := by
    change φ 1 = 1
    exact φ.map_one
  map_directSum := by
    intro ι X Y Z hι dι hX hY hZ T
    rw [classOf_directSum, map_sum]
  map_product := by
    intro X Y Z U V W hX hY hZ hU hV hW T S
    rw [classOf_product, map_mul]
  monotone := by
    intro X Y Z X' Y' Z' hX hY hZ hX' hY' hZ' T A B C
    apply hφ
    exact (classOf_le_iff _ _).mpr ⟨A, B, C, rfl⟩











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







namespace TensorSemiring





















end TensorSemiring
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end CharacterModule5




end AllFieldsModule4
/- END all-fields module GenericCharacters -/


