-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.Character.sharedFirst_tag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:44:50.793211+00:00
-- url     : https://prove2.me/submissions/ee34567c-36e0-4d81-860e-d047eca0831d

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
import Definitions.Def_OAI429_GenericNumerics
import Definitions.Def_OAI429_GenericRank
import Definitions.Def_OAI429_GenericSeparation
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_integral_type_comparison
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_Character_one_le_value
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exp_le_of_tendsto_log_div
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_typeContribution_rate
import Theorems.Thm_OAI_MatrixMultiplication_Foundation_FiniteLaw_exists_rational_approximation
import Theorems.Thm_OAI_MatrixMultiplication_Foundation_exactWords_card
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical
namespace OAIAllFieldsSeparation
end OAIAllFieldsSeparation

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Character
end OAI.MatrixMultiplication.AuxiliarySeparation.Character
open OAI.MatrixMultiplication.AuxiliarySeparation.Character

namespace OAI.MatrixMultiplication.ConditionalLabels
end OAI.MatrixMultiplication.ConditionalLabels
open OAI.MatrixMultiplication.ConditionalLabels

namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.Foundation

namespace OAI.MatrixMultiplication.Foundation.FiniteControl
end OAI.MatrixMultiplication.Foundation.FiniteControl
open OAI.MatrixMultiplication.Foundation.FiniteControl

namespace OAI.MatrixMultiplication.Foundation.FiniteLaw
end OAI.MatrixMultiplication.Foundation.FiniteLaw
open OAI.MatrixMultiplication.Foundation.FiniteLaw

namespace OAI.MatrixMultiplication.Foundation.RationalLaw
end OAI.MatrixMultiplication.Foundation.RationalLaw
open OAI.MatrixMultiplication.Foundation.RationalLaw

namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation
namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_77193218a5f1
namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation



set_option linter.all false

set_option autoImplicit false

/- BEGIN all-fields module GenericNumerics -/
section AllFieldsModule12

set_option autoImplicit false

section CompatibilityAliases

universe u

/- Compatibility aliases: Lean 4.34.1 Init/Core.lean names, proved by their
   Lean 4.33.1 predecessors without changing the source statements. -/




/- From Mathlib 4.34.1 Order/Antisymmetrization.lean, unchanged proof. -/


end CompatibilityAliases



/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy -/
section NumericModule0

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators















namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]





















end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI

end NumericModule0


/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity -/
section NumericModule1

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation











@[fun_prop] theorem continuous_entropyTerm : Continuous entropyTerm :=
  Real.continuous_negMulLog





@[fun_prop] theorem continuous_finiteEntropy {A : Type*} [Fintype A] :
    Continuous (finiteEntropy : (A → ℝ) → ℝ) := by
  unfold finiteEntropy
  exact continuous_finset_sum _ fun value _ =>
    continuous_entropyTerm.comp (continuous_apply value)





theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)







namespace FiniteLaw

variable {A : Type*} [Fintype A]



















theorem entropy_tendsto {I : Type*} {l : Filter I}
    {p : I → FiniteLaw A} {q : FiniteLaw A}
    (h : ∀ a, Tendsto (fun i => (p i).mass a) l (𝓝 (q.mass a))) :
    Tendsto (fun i => finiteEntropy (p i).mass) l (𝓝 (finiteEntropy q.mass)) :=
  tendsto_finiteEntropy_of_tendsto h

end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI

end NumericModule1


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Laws -/
section NumericModule2

namespace OAI

/-!
# Probability laws for the polynomial tensor inequalities

The determinant filtration uses an arbitrary binary law, while the three-sector
filtration uses the uniform law on three branches.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation















end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end NumericModule2


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Optimization -/
section NumericModule3

namespace OAI

/-!
# Entropy optimization for finitely many sectors

The normalized weights `q = A / (A + B)` and `1 - q = B / (A + B)`
make the entropy-weighted geometric mean equal to `A + B`. This is the
scalar identity used in Section 5.1 of the auxiliary-separation argument.
The same calculation also applies to an arbitrary nonempty finite family.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation











end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule3


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.ProductBounds -/
section NumericModule4

namespace OAI

/-!
# Combining the scalar sector bounds

Pointwise character bounds multiply over a finite family of leg orders. After
normalization by the sum of the singleton exponents, the entropy identity gives
the midpoint-concavity bound for the profile.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation





end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule4


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ConcaveSlopes -/
section NumericModule5

namespace OAI

/-!
# Slopes of positive discretely concave sequences

The row sequences in Section 6 have decreasing consecutive increments. A
nonnegative sequence cannot have a negative increment of this kind: every later
increment would be at least as negative. Consequently the increments converge
to a nonnegative limit, and the sequence divided by its index has the same limit.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology















end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule5


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ProfileSlopes -/
section NumericModule6

namespace OAI

/-!
# Shifted tripling and diagonal increments

These are the two estimates on the limiting row slopes used in Section 6.
Iteration retains the additive shift in the tripling inequality. Symmetry
then expresses a diagonal step as one increment in each of two adjacent rows.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology



















end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule6


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison -/
section NumericModule7

namespace OAI

/-!
# Comparing power growth

The last scalar step of the auxiliary-separation argument compares a
fourth-power lower bound for the cube of the diagonal profile with its
dimension upper bound.  Powers of two suffice to compare the exponents, so
the argument needs no asymptotic estimates or approximation of constants.
-/

namespace MatrixMultiplication.AuxiliarySeparation







end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule7


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Profile -/
section NumericModule8

namespace OAI

/-!
# Growth of the scalar profile

This file proves the scalar implication of Section 6 (Lemma 6.1). The profile
properties are explicit hypotheses: the construction of a profile from a tensor
character and the proof of those properties are separate arguments.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology



namespace ScalarProfile









end ScalarProfile



end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule8


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PermutationProduct -/
section NumericModule9

namespace OAI

/-!
# Products over the six permutations of three tensor legs

The symmetrized quantity in Section 5 uses every permutation of the three
tensor legs. Composing by a fixed permutation preserves this product. For
the exponent calculation, each original leg occurs twice in any fixed slot.
These are finite identities; they do not assume that an individual tensor
character is invariant under exchanging its legs.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation



namespace LegPermutation





























end LegPermutation

end MatrixMultiplication.AuxiliarySeparation

end OAI

end NumericModule9


/- OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexFactorialLogBounds -/
section NumericModule10

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology



























end MatrixMultiplication.Foundation

end OAI

end NumericModule10


/- OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteControl -/
section NumericModule11

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation
namespace FiniteControl

open scoped BigOperators







theorem exists_common_bank_multiple {Node : Type*} [Fintype Node]
    (denominator blockSize : Node → ℕ)
    (denominator_pos : ∀ node, 0 < denominator node)
    (blockSize_pos : ∀ node, 0 < blockSize node) :
    ∃ bank : ℕ, 0 < bank ∧
      ∀ node, denominator node * blockSize node ∣ bank := by
  classical
  refine ⟨∏ node, denominator node * blockSize node, ?_, ?_⟩
  · exact Finset.prod_pos fun node _ =>
      Nat.mul_pos (denominator_pos node) (blockSize_pos node)
  · intro node
    exact Finset.dvd_prod_of_mem (fun node => denominator node * blockSize node)
      (Finset.mem_univ node)

theorem exists_exact_rational_tiling {Node : Type*} [Fintype Node]
    (weight : Node → ℚ) (nonnegative : ∀ node, 0 ≤ weight node)
    (blockSize : Node → ℕ) (blockSize_pos : ∀ node, 0 < blockSize node) :
    ∃ bank : ℕ, 0 < bank ∧ ∀ node, ∃ copies : ℕ,
      (bank : ℚ) * weight node = (copies * blockSize node : ℕ) := by
  obtain ⟨bank, bank_pos, divisible⟩ := exists_common_bank_multiple
    (fun node => (weight node).den) blockSize
    (fun node => (weight node).den_pos) blockSize_pos
  refine ⟨bank, bank_pos, ?_⟩
  intro node
  obtain ⟨multiple, hmultiple⟩ := divisible node
  refine ⟨multiple * (weight node).num.toNat, ?_⟩
  have hnum : ((weight node).num.toNat : ℚ) = ((weight node).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (nonnegative node))
  have hden : ((weight node).den : ℚ) ≠ 0 := by
    exact_mod_cast (weight node).den_ne_zero
  calc
    (bank : ℚ) * weight node =
        (bank : ℚ) * (((weight node).num : ℚ) / ((weight node).den : ℚ)) := by
      rw [(weight node).num_div_den]
    _ = ((multiple * (weight node).num.toNat) * blockSize node : ℕ) := by
      rw [hmultiple]
      push_cast
      rw [hnum]
      field_simp [hden]





end FiniteControl
end MatrixMultiplication.Foundation

end OAI

end NumericModule11


/- OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexRationalTypes -/
section NumericModule12

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators



namespace RationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]



@[simp] theorem toFiniteLaw_mass (p : RationalLaw A) (a : A) :
    p.toFiniteLaw.mass a = (p.mass a : ℝ) := rfl

theorem exists_exact_counts (p : RationalLaw A) :
    ∃ D : ℕ, 0 < D ∧ ∃ counts : A → ℕ,
      (∑ a, counts a) = D ∧
      ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a := by
  classical
  obtain ⟨D, hD, hcopies⟩ := FiniteControl.exists_exact_rational_tiling
    p.mass p.nonneg (fun _ => 1) (fun _ => Nat.zero_lt_one)
  choose counts hcounts using hcopies
  have hc : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a := by
    intro a
    simpa using (hcounts a).symm
  refine ⟨D, hD, counts, ?_, hc⟩
  have hsum : (∑ a, (counts a : ℚ)) = (D : ℚ) := by
    simp_rw [hc]
    rw [← Finset.mul_sum, p.total, mul_one]
  exact_mod_cast hsum





theorem exact_counts_real_mass (p : RationalLaw A) {D : ℕ} (hD : 0 < D)
    {counts : A → ℕ}
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (a : A) :
    (counts a : ℝ) / (D : ℝ) = p.toFiniteLaw.mass a := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  apply (div_eq_iff hDr).2
  have hc : (counts a : ℝ) = (D : ℝ) * (p.mass a : ℝ) := by
    exact_mod_cast hcounts a
  simpa only [toFiniteLaw_mass, mul_comm] using hc

theorem exists_type_representation (p : RationalLaw A) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      ∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a := by
  obtain ⟨D, hD, counts, hsum, hcounts⟩ := _root_.OAIExtractedProof_77193218a5f1.OAI.MatrixMultiplication.Foundation.RationalLaw.exists_exact_counts p
  refine ⟨counts, by simpa only [hsum] using hD, ?_⟩
  intro a
  rw [hsum]
  exact _root_.OAIExtractedProof_77193218a5f1.OAI.MatrixMultiplication.Foundation.RationalLaw.exact_counts_real_mass p hD hcounts a

end RationalLaw



namespace FiniteLaw

variable {A : Type*} [Fintype A]





end FiniteLaw

end MatrixMultiplication.Foundation

end OAI

end NumericModule12


/- OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting -/
section NumericModule13

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]



















theorem exactWords_card_pos (counts : A → ℕ) : 0 < Fintype.card (ExactWords counts) := by
  rw [exactWords_card]
  exact Nat.multinomial_pos Finset.univ counts



end MatrixMultiplication.Foundation

end OAI

end NumericModule13


/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy -/
section NumericModule14

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]









































namespace RationalLaw



end RationalLaw

end MatrixMultiplication.Foundation

end OAI

end NumericModule14


/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity -/
section NumericModule15
namespace OAI.MatrixMultiplication.ConditionalLabels
open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology Classical
variable {A : Type*} [Fintype A]
theorem exists_rational_law_sequence (p : FiniteLaw A) :
    ∃ q : ℕ → RationalLaw A,
      ∀ a, Tendsto (fun n => (q n).toFiniteLaw.mass a) atTop (𝓝 (p.mass a)) := by
  have hexists (n : ℕ) := p.exists_rational_approximation
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose q _support close using hexists
  refine ⟨q, fun a => ?_⟩
  have hdifference : Tendsto
      (fun n => (q n).toFiniteLaw.mass a - p.mass a) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.norm_eq_abs, RationalLaw.toFiniteLaw_mass] using (close n a).le
  simpa only [sub_add_cancel, zero_add] using hdifference.add_const (p.mass a)


end OAI.MatrixMultiplication.ConditionalLabels

end NumericModule15


/- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Tag -/
section NumericModule16

namespace OAI

/-!
# The entropy limit for matched types

The finite hypothesis in this file is an inequality at every integral type.
The conclusion follows by first repeating a fixed type, and then approximating
an arbitrary probability law by rational laws. No entropy inequality is
included in the finite hypothesis.
-/

noncomputable section

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

namespace MatrixMultiplication.AuxiliarySeparation

variable {A : Type*} [Fintype A] [DecidableEq A]



theorem typeContribution_pos (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (t : ℕ) :
    0 < typeContribution values p counts t := by
  unfold typeContribution
  exact mul_pos
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p)
    (Finset.prod_pos (fun a _ => pow_pos (hvalues a) _))





/-- A finite bound on each repetition of a fixed type implies its logarithmic
entropy bound; the fixed loss `C` disappears in the limit. -/
theorem log_type_bound (values : A → ℝ) (p source C : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hD : 0 < ∑ a, counts a)
    (hfinite : ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
      ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a) ≤
        Real.log source := by
  apply (Real.le_log_iff_exp_le hsource).2
  apply exp_le_of_tendsto_log_div hsource hC
    (tendsto_id.atTop_mul_const' hD)
    (Eventually.of_forall (typeContribution_pos values p counts hvalues))
  · simpa only [Nat.cast_mul, id_eq] using typeContribution_rate values p counts hvalues hD
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    exact hfinite t ht

/-- Rational laws can be represented by one exact integral type. -/
theorem rational_log_tag_of_finite_type_bounds
    (q : RationalLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy q.toFiniteLaw.mass +
      ∑ a, q.toFiniteLaw.mass a * Real.log (values a) ≤ Real.log source := by
  obtain ⟨counts, hD, hmass⟩ := _root_.OAIExtractedProof_77193218a5f1.OAI.MatrixMultiplication.Foundation.RationalLaw.exists_type_representation q
  have h := log_type_bound values p source C counts hvalues hsource hC hD
    (hfinite counts hD)
  simpa only [hmass] using h

/-- Integral type bounds imply the tag inequality on the whole finite
probability simplex, including laws with zero coordinates. -/
theorem log_tag_of_finite_type_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy q.mass +
      ∑ a, q.mass a * Real.log (values a) ≤ Real.log source := by
  obtain ⟨r, hr⟩ := MatrixMultiplication.ConditionalLabels.exists_rational_law_sequence q
  have hlinear : Tendsto
      (fun n => ∑ a, (r n).toFiniteLaw.mass a * Real.log (values a)) atTop
      (𝓝 (∑ a, q.mass a * Real.log (values a))) :=
    tendsto_finset_sum Finset.univ (fun a _ => (hr a).mul_const _)
  have hlimit := ((FiniteLaw.entropy_tendsto hr).const_mul p).add hlinear
  exact le_of_tendsto hlimit (Eventually.of_forall (fun n =>
    rational_log_tag_of_finite_type_bounds (r n) values p source C
      hvalues hsource hC hfinite))

/-- Exponentiating gives the entropy-weighted geometric-mean form. -/
theorem tag_of_finite_type_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, values a ^ q.mass a ≤ source := by
  have h := Real.exp_le_exp.mpr
    (log_tag_of_finite_type_bounds q values p source C hvalues hsource hC hfinite)
  rw [Real.exp_log hsource, Real.exp_add, Real.exp_sum] at h
  convert h using 1
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [Real.rpow_def_of_pos (hvalues a), mul_comm]



/-- The geometric-mean formulation from finite inequalities for integral types. -/
theorem tag_of_integral_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p * ∏ a, values a ^ counts a ≤
        C * source ^ (∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, values a ^ q.mass a ≤ source := by
  apply tag_of_finite_type_bounds q values p source C hvalues hsource hC
  intro counts hD t ht
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a := by
    rw [Finset.mul_sum]
  have hpositive : 0 < ∑ a, t * counts a := by
    rw [hsum]
    exact Nat.mul_pos ht hD
  simpa only [typeContribution, hsum] using hfinite (fun a => t * counts a) hpositive


end MatrixMultiplication.AuxiliarySeparation
end
end OAI

end NumericModule16


end AllFieldsModule12
/- END all-fields module GenericNumerics -/

/- BEGIN all-fields module GenericTags -/
section AllFieldsModule21

open OAIAllFieldsSeparation


section TagModule0

namespace OAI

/-!
# Recovering tensors from their supported coordinate subspaces

If a tensor has support inside three injectively embedded coordinate sets, it
is exactly the extension by zero of its pullback to those sets. Characters
therefore have the same value on the ambient tensor and this smaller tensor.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

open MatrixMultiplication.Foundation
open scoped Classical

variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']



namespace Character



end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end TagModule0


section TagModule1

namespace OAI

/-!
# Padding shared-input tensors with different branch dimensions

The finite separation construction uses fixed ambient coordinate spaces on
each leg. A family with a common first leg and varying second and third legs
embeds into that setting without changing any character values. The extra
coordinates introduced by padding have zero coefficients.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable {M : ℕ} {X : Type} {Y Z : Fin M → Type}
variable [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]



















namespace Character





end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule1


section TagModule2

namespace OAI

/-!
# Recovering branch tags from coordinate support

When both non-shared coordinates determine a branch label, adding explicit
matching branch tags does not change a character's value. The tags can be
recovered by independent coordinate maps, and forgetting them recovers the
original coefficientwise sum of branches.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable {M : ℕ} {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]



namespace Character



end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule2


section TagModule3
namespace OAI
noncomputable section
open MatrixMultiplication.Foundation
open scoped BigOperators Topology
namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
namespace Character

variable {I X Y Z : Type} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [Fintype Z]
  {BX BY BZ : I → Type}
  [∀ a, Fintype (BX a)] [∀ a, Fintype (BY a)] [∀ a, Fintype (BZ a)]



/-- The entropy-weighted tag bound, once the finite matched-type tensor
comparison has been established. -/
theorem tag_of_integral_type_comparison (χ : (Character 𝕜))
    (q : FiniteLaw I) (T : Tensor 𝕜 X Y Z)
    (B : ∀ a, Tensor 𝕜 (BX a) (BY a) (BZ a)) (p : ℝ)
    (hT : T ≠ 0) (hB : ∀ a, B a ≠ 0)
    (hfinite : ∀ counts : I → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p *
          ∏ a, χ.value (B a) ^ counts a ≤
        5 * χ.value T ^ (∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, χ.value (B a) ^ q.mass a ≤
      χ.value T :=
  MatrixMultiplication.AuxiliarySeparation.tag_of_integral_bounds q (fun a => χ.value (B a)) p
    (χ.value T) 5 (fun a => lt_of_lt_of_le zero_lt_one (χ.one_le_value (hB a)))
    (lt_of_lt_of_le zero_lt_one (χ.one_le_value hT)) (by norm_num) hfinite

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule3


section TagModule4

namespace OAI

/-!
# The shared-input tensor tag inequality

Exact type words in a power of a matched-sector tensor are obtained by explicit
coordinate pullbacks. Their character values depend only on the type counts.
The finite auxiliary separation inequality therefore supplies the integral
bounds required by the entropy limit.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable {s : ℕ} {X Y Z : Type}
  [Fintype X] [Fintype Y] [Fintype Z]















omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- A nonzero branch remains visible in the tensor with a shared first leg. -/
theorem sharedFirstTensor_ne_zero_of_branch (B : Fin s → Tensor 𝕜 X Y Z)
    (a : Fin s) (ha : B a ≠ 0) : sharedFirstTensor B ≠ 0 := by
  intro h
  apply ha
  funext x y z
  have hxyz := congrFun (congrFun (congrFun h x) (a, y)) (a, z)
  simpa only [sharedFirstTensor, ↓reduceIte, Pi.zero_apply] using hxyz

/-- The actual shared-input tensor tag inequality, including probability laws
with zero coordinates. The branch labels are disjoint on the second and third
legs, while the first coordinate is shared. -/
theorem Character.sharedFirst_tag (χ : (Character 𝕜))
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor 𝕜 X Y Z)
    (hB : ∀ a, B a ≠ 0) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstTensor B) := by
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
    subst s
    have htotal := q.total
    simp at htotal
  have hT : sharedFirstTensor B ≠ 0 :=
    sharedFirstTensor_ne_zero_of_branch B ⟨0, hs⟩ (hB ⟨0, hs⟩)
  apply _root_.OAIExtractedProof_77193218a5f1.OAI.MatrixMultiplication.AuxiliarySeparation.Character.tag_of_integral_type_comparison χ q (sharedFirstTensor B) B χ.pX hT hB
  intro counts _hcounts
  simpa only [Fintype.card_eq_nat_card] using χ.integral_type_comparison B counts



section Dependent

variable {U V : Fin s → Type} [∀ a, Fintype (U a)] [∀ a, Fintype (V a)]





end Dependent

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule4


end AllFieldsModule21
/- END all-fields module GenericTags -/

end OAIExtractedProof_77193218a5f1

theorem solution.{u_1} :
    ∀ {𝕜 : Type u_1} [inst : Field 𝕜] [IsAlgClosed 𝕜] {s : ℕ} {X Y Z : Type} [inst_2 : Fintype X] [inst_3 : Fintype Y]
  [inst_4 : Fintype Z] (χ : OAI.MatrixMultiplication.AuxiliarySeparation.Character 𝕜)
  (q : OAI.MatrixMultiplication.Foundation.FiniteLaw (Fin s))
  (B : Fin s → OAI.MatrixMultiplication.Foundation.Tensor 𝕜 X Y Z),
  (∀ (a : Fin s), B a ≠ 0) →
    Real.exp (χ.pX * OAI.MatrixMultiplication.Foundation.finiteEntropy q.mass) * ∏ a : Fin s, χ.value (B a) ^ q.mass a ≤
      χ.value (OAIAllFieldsSeparation.sharedFirstTensor B)
:= @OAIExtractedProof_77193218a5f1.OAI.MatrixMultiplication.AuxiliarySeparation.Character.sharedFirst_tag
