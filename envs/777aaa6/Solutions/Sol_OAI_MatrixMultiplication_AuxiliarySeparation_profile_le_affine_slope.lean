-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.profile_le_affine_slope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:13:12.733494+00:00
-- url     : https://prove2.me/submissions/df453f58-7607-44b5-8026-87c5ac2a380a

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
import Definitions.Def_OAI429_GenericNumerics
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_c209d67e1fe4


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































namespace FiniteLaw

variable {A : Type*} [Fintype A]





















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



/-- Starting at a positive index, affine tripling escapes to infinity. -/
theorem shiftedTriplingIndex_lower (c h : ℕ) (hh : 1 ≤ h) (j : ℕ) :
    h + j ≤ shiftedTriplingIndex c h j := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      simp only [shiftedTriplingIndex]
      omega

theorem shiftedTriplingIndex_tendsto (c h : ℕ) (hh : 1 ≤ h) :
    Tendsto (shiftedTriplingIndex c h) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  change j ≤ shiftedTriplingIndex c h j
  have := shiftedTriplingIndex_lower c h hh j
  omega

/-- The exact affine oai_arithmetic_solution, written without truncated natural subtraction. -/
theorem shiftedTriplingIndex_cast (c h j : ℕ) :
    (shiftedTriplingIndex c h j : ℝ) + (c : ℝ) / 2 =
      (3 : ℝ) ^ j * ((h : ℝ) + (c : ℝ) / 2) := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      simp only [shiftedTriplingIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        pow_succ]
      nlinarith

/-- Iterating the tripling inequality multiplies the profile by powers of three. -/
theorem shiftedTripling_profile_lower {P : ℕ → ℝ} {c h : ℕ} (hh : 1 ≤ h)
    (htrip : ∀ n : ℕ, 1 ≤ n → 3 * P n ≤ P (3 * n + c)) (j : ℕ) :
    (3 : ℝ) ^ j * P h ≤ P (shiftedTriplingIndex c h j) := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      have hj : 1 ≤ shiftedTriplingIndex c h j := by
        have := shiftedTriplingIndex_lower c h hh j
        omega
      have hstep := htrip (shiftedTriplingIndex c h j) hj
      simp only [shiftedTriplingIndex, pow_succ]
      nlinarith

/-- A row with a limiting linear slope and shifted tripling lies below the
corresponding affine multiple of that slope. -/
theorem profile_le_affine_slope {P : ℕ → ℝ} {g : ℝ} {c h : ℕ}
    (hh : 1 ≤ h)
    (htrip : ∀ n : ℕ, 1 ≤ n → 3 * P n ≤ P (3 * n + c))
    (hlim : Tendsto (fun n : ℕ => P n / (n : ℝ)) atTop (𝓝 g)) :
    P h ≤ ((h : ℝ) + (c : ℝ) / 2) * g := by
  have hpow : Tendsto (fun j : ℕ => (3 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hzero : Tendsto (fun j : ℕ => ((c : ℝ) / 2) / (3 : ℝ) ^ j)
      atTop (𝓝 0) := hpow.const_div_atTop _
  have hindex : Tendsto
      (fun j : ℕ => (shiftedTriplingIndex c h j : ℝ) / (3 : ℝ) ^ j)
      atTop (𝓝 ((h : ℝ) + (c : ℝ) / 2)) := by
    have heq (j : ℕ) :
        (shiftedTriplingIndex c h j : ℝ) / (3 : ℝ) ^ j =
          (h : ℝ) + (c : ℝ) / 2 - ((c : ℝ) / 2) / (3 : ℝ) ^ j := by
      have hj := shiftedTriplingIndex_cast c h j
      have hp : (3 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      nlinarith
    simpa only [heq, sub_zero] using tendsto_const_nhds.sub hzero
  have hproduct := (hlim.comp (shiftedTriplingIndex_tendsto c h hh)).mul hindex
  have hprofile : Tendsto
      (fun j : ℕ => P (shiftedTriplingIndex c h j) / (3 : ℝ) ^ j)
      atTop (𝓝 (g * ((h : ℝ) + (c : ℝ) / 2))) := by
    apply hproduct.congr'
    apply Eventually.of_forall
    intro j
    have hj : (shiftedTriplingIndex c h j : ℝ) ≠ 0 := by
      have := shiftedTriplingIndex_lower c h hh j
      exact_mod_cast (show shiftedTriplingIndex c h j ≠ 0 by omega)
    dsimp only [Function.comp_def]
    field_simp
  have hbound : ∀ j : ℕ, P h ≤ P (shiftedTriplingIndex c h j) / (3 : ℝ) ^ j := by
    intro j
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) j)).mpr
    simpa only [mul_comm] using shiftedTripling_profile_lower hh htrip j
  simpa only [mul_comm] using ge_of_tendsto hprofile (Eventually.of_forall hbound)







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






















end MatrixMultiplication.AuxiliarySeparation
end
end OAI

end NumericModule16


end AllFieldsModule12
/- END all-fields module GenericNumerics -/

end OAIExtractedProof_c209d67e1fe4

theorem solution :
    ∀ {P : ℕ → ℝ} {g : ℝ} {c h : ℕ},
  1 ≤ h →
    (∀ (n : ℕ), 1 ≤ n → 3 * P n ≤ P (3 * n + c)) →
      Filter.Tendsto (fun (n : ℕ) => P n / ↑n) Filter.atTop (nhds g) → P h ≤ (↑h + ↑c / 2) * g
:= @OAIExtractedProof_c209d67e1fe4.OAI.MatrixMultiplication.AuxiliarySeparation.profile_le_affine_slope
