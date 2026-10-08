-- Prove2me | solution 1 for parent_simplex_case_BC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:12:01.132987+00:00
-- url     : https://prove2.me/submissions/5479c111-f647-4c09-86cb-53b35b28bedc

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
import Definitions.Def_OAI429_FixedPointTheorems_cubical_sperner_prep
import Theorems.Thm_child_simplex_char
import Theorems.Thm_monotone_1_of_simplex
import Theorems.Thm_parent_injective
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical


namespace OAIExtractedProof_dc3c8fed55eb


set_option linter.all false

set_option autoImplicit false

section AllFieldsModule0/- BEGIN FixedPointTheorems.cubical_sperner_prep -/
section AbstractModule10

/-!
# Cubical simplices and boundary incidence

The grid simplices of a labelled cube are classified by their boundary coordinates.
Coordinate-change counts order their vertices and determine the number of parent simplices,
providing the incidence identities used in the cubical Sperner argument.
-/


open Classical



namespace SpernerCube





end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}





















section simplex_properties









end simplex_properties



section simplex_child

























end simplex_child

section cases_ABCD







lemma parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use 0
    exact h4
  }
  have h4 : J 0 ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1)
  }
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by {
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  }
  intro j1 hj1 k1
  apply And.intro
  {
    rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    {
      simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    }
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  }
  {
    have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      rw [← hn1]; simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    have e2 : (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 := by
      simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [e1, e2] at h6
    rw [congrFun h6 k1]
    exact (h3 k1).2
  }
}



















































end cases_ABCD







end AbstractModule10


end AllFieldsModule0

end OAIExtractedProof_dc3c8fed55eb

theorem solution :
    ∀ (SC : SpernerCube) {n1 : Nat}
  {hn1 :
    @Eq Nat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      SC.n}
  (I :
    Fin
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      SC.G),
  simplex SC n1 I →
    ∀
      (J :
        Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          SC.G),
      @Eq
          (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            SC.G)
          I
          (@delete_vertex SC n1 hn1
            (@OfNat.ofNat
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (nat_lit 0)
              (@Fin.instOfNat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@instNeZeroNatHAdd_1 SC.n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                (nat_lit 0)))
            J) →
        @Ne SC.G
            (J
              (@OfNat.ofNat
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 SC.n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0))))
            (I
              (@OfNat.ofNat
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 n1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0)))) →
          (∀ (k : Fin SC.n),
              And
                (@LE.le
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.p
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@instLEFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.p
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (J
                    (@OfNat.ofNat
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (nat_lit 0)
                      (@Fin.instOfNat
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@instNeZeroNatHAdd_1 SC.n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (nat_lit 0)))
                    k)
                  (I
                    (@OfNat.ofNat
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (nat_lit 0)
                      (@Fin.instOfNat
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n1
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@instNeZeroNatHAdd_1 n1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (nat_lit 0)))
                    k))
                (@LE.le Nat instLENat
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.p
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (I (Fin.last n1) k))
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@Fin.val
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.p
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (J
                        (@OfNat.ofNat
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (nat_lit 0)
                          (@Fin.instOfNat
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) SC.n
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@instNeZeroNatHAdd_1 SC.n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (nat_lit 0)))
                        k))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
            @is_face SC n1 I J
:= @OAIExtractedProof_dc3c8fed55eb.parent_simplex_case_BC
