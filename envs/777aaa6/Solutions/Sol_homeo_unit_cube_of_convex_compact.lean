-- Prove2me | solution 1 for homeo_unit_cube_of_convex_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:06:10.826271+00:00
-- url     : https://prove2.me/submissions/0ec844fb-14ba-4131-92dd-f19fb6d1786b

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
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical


namespace OAIExtractedProof_7a8483dc576a


set_option linter.all false

set_option autoImplicit false

section AllFieldsModule0/- BEGIN FixedPointTheorems.convex_homeos -/
section AbstractModule13

/-!
# Homeomorphisms of compact convex sets

Compact convex sets are reduced to unit balls in their affine spans and then to
finite-dimensional cubes. These homeomorphisms transfer the cubical fixed-point
theorem to arbitrary nonempty compact convex domains.
-/


lemma homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by {
  have h1 := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni
  have h2 : Bornology.IsBounded s := IsCompact.isBounded hcmpct
  cases (h1 h2)
  rename_i e he
  have h4 := closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct)
  have e2 := Homeomorph.image e s
  rw [h4] at he
  rw [he.2.1] at e2
  exact Nonempty.intro e2
}

theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by {
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹' (Metric.closedBall (0:W) 1)
  have hpL : pL = L.toHomeomorph ⁻¹' (Metric.closedBall (0:W) 1) := rfl
  have h4 : Convex ℝ pL := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have h5 : IsCompact pL := by {
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  }
  have h6 : (interior pL).Nonempty := by {
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    use 0
    rw [interior_closedBall]
    {simp only [Metric.mem_ball, dist_self, zero_lt_one]}
    {exact Ne.symm (zero_ne_one' ℝ)}
  }
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 := by {
    rw [hpL]
    exact L.toHomeomorph.sets hpL
  }
  have h7 := homeo_unit_ball _ h4 h5 h6
  cases h7
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1
}

lemma unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x; simp [Set.mem_Icc, Pi.le_def]
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    rw [interior_Icc]; exact ⟨1/2, by norm_num, by norm_num⟩

lemma homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by {
  have := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  let s2 := g1 ⁻¹' s
  let s3 := g2.symm ⁻¹' s2
  have h32 : Convex ℝ s3 := by {
    exact hcvx.affine_preimage
      ((affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  }
  have h34 : (interior s3).Nonempty := by {
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
    unfold s3
    rw [←AffineIsometryEquiv.coe_toAffineEquiv]
    rw [← AffineSubspace.comap_span]
    rw [affineSpan_coe_preimage_eq_top]
    rfl
  }
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by {
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  }
  have h5 : Set.MapsTo g3 s3 s := by {
    intro w h1
    unfold s3 s2 at h1
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  }
  have h6 : Function.Surjective (Set.MapsTo.restrict g3 s3 s h5) := by {
    refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
    refine Set.SurjOn.comp_right ?_ ?_
    exact AffineIsometryEquiv.surjective g2.symm
    intro v h1
    refine (Set.mem_image g1 (g1 ⁻¹' s) v).mpr ?_
    have h11 : v ∈ affineSpan ℝ s := mem_affineSpan ℝ h1
    use ⟨v, h11⟩
    simp only [Set.mem_preimage]
    apply And.intro h1 rfl
  }
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective h6
  have h31 : IsCompact s3 := by {
    have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
    simp only [Set.image_univ, EquivLike.range_eq_univ] at h51
    apply isCompact_iff_isCompact_univ.mpr
    apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
  }
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 h31 h34
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := (Module.finrank_fin_fun ℝ).symm
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  let e5 := (e1.symm.trans e2).trans (e4.trans e3.symm)
  use k
  exact Nonempty.intro e5
}

end AbstractModule13


end AllFieldsModule0

end OAIExtractedProof_7a8483dc576a

theorem solution.{u_1} :
    ∀ {V : Type u_1} [inst : NormedAddCommGroup V]
  [inst_1 : @NormedSpace Real V Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup V inst)]
  [@FiniteDimensional Real V Real.instDivisionRing (@NormedAddCommGroup.toAddCommGroup V inst)
      (@NormedSpace.toModule Real V Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup V inst) inst_1)]
  (s : Set V),
  @Convex Real V Real.semiring Real.partialOrder
      (@ESeminormedAddCommMonoid.toAddCommMonoid V
        (@UniformSpace.toTopologicalSpace V
          (@PseudoMetricSpace.toUniformSpace V
            (@SeminormedAddCommGroup.toPseudoMetricSpace V (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
        (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
          (@UniformSpace.toTopologicalSpace V
            (@PseudoMetricSpace.toUniformSpace V
              (@SeminormedAddCommGroup.toPseudoMetricSpace V (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
          (@NormedAddCommGroup.toENormedAddCommMonoid V inst)))
      (@SMulZeroClass.toSMul Real V
        (@AddZero.toZero V
          (@AddZeroClass.toAddZero V
            (@AddMonoid.toAddZeroClass V
              (@ESeminormedAddMonoid.toAddMonoid V
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                (@ESeminormedAddCommMonoid.toESeminormedAddMonoid V
                  (@UniformSpace.toTopologicalSpace V
                    (@PseudoMetricSpace.toUniformSpace V
                      (@SeminormedAddCommGroup.toPseudoMetricSpace V
                        (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                  (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
                    (@UniformSpace.toTopologicalSpace V
                      (@PseudoMetricSpace.toUniformSpace V
                        (@SeminormedAddCommGroup.toPseudoMetricSpace V
                          (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                    (@NormedAddCommGroup.toENormedAddCommMonoid V inst)))))))
        (@DistribSMul.toSMulZeroClass Real V
          (@AddMonoid.toAddZeroClass V
            (@ESeminormedAddMonoid.toAddMonoid V
              (@UniformSpace.toTopologicalSpace V
                (@PseudoMetricSpace.toUniformSpace V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
              (@ESeminormedAddCommMonoid.toESeminormedAddMonoid V
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
                  (@UniformSpace.toTopologicalSpace V
                    (@PseudoMetricSpace.toUniformSpace V
                      (@SeminormedAddCommGroup.toPseudoMetricSpace V
                        (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                  (@NormedAddCommGroup.toENormedAddCommMonoid V inst)))))
          (@DistribMulAction.toDistribSMul Real V Real.instMonoid
            (@ESeminormedAddMonoid.toAddMonoid V
              (@UniformSpace.toTopologicalSpace V
                (@PseudoMetricSpace.toUniformSpace V
                  (@SeminormedAddCommGroup.toPseudoMetricSpace V
                    (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
              (@ESeminormedAddCommMonoid.toESeminormedAddMonoid V
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
                  (@UniformSpace.toTopologicalSpace V
                    (@PseudoMetricSpace.toUniformSpace V
                      (@SeminormedAddCommGroup.toPseudoMetricSpace V
                        (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                  (@NormedAddCommGroup.toENormedAddCommMonoid V inst))))
            (@Module.toDistribMulAction Real V Real.semiring
              (@ESeminormedAddCommMonoid.toAddCommMonoid V
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                (@ENormedAddCommMonoid.toESeminormedAddCommMonoid V
                  (@UniformSpace.toTopologicalSpace V
                    (@PseudoMetricSpace.toUniformSpace V
                      (@SeminormedAddCommGroup.toPseudoMetricSpace V
                        (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
                  (@NormedAddCommGroup.toENormedAddCommMonoid V inst)))
              (@NormedSpace.toModule Real V Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup V inst)
                inst_1)))))
      s →
    @IsCompact V
        (@UniformSpace.toTopologicalSpace V
          (@PseudoMetricSpace.toUniformSpace V
            (@SeminormedAddCommGroup.toPseudoMetricSpace V (@NormedAddCommGroup.toSeminormedAddCommGroup V inst))))
        s →
      @Set.Nonempty V s →
        ∃ (k : Nat),
          Nonempty.{max 1 (u_1 + 1)}
            (@Homeomorph (@Set.Elem V s)
              (@Set.Elem (Fin k → Real)
                (@Set.Icc (Fin k → Real)
                  (@Pi.preorder (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instPreorder)
                  (@OfNat.ofNat (Fin k → Real) (nat_lit 0)
                    (@Zero.toOfNat0 (Fin k → Real)
                      (@Pi.instZero (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instZero)))
                  (@OfNat.ofNat (Fin k → Real) (nat_lit 1)
                    (@One.toOfNat1 (Fin k → Real)
                      (@Pi.instOne (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instOne)))))
              (@instTopologicalSpaceSubtype V (fun (x : V) => @Membership.mem V (Set V) (@Set.instMembership V) s x)
                (@UniformSpace.toTopologicalSpace V
                  (@PseudoMetricSpace.toUniformSpace V
                    (@SeminormedAddCommGroup.toPseudoMetricSpace V
                      (@NormedAddCommGroup.toSeminormedAddCommGroup V inst)))))
              (@instTopologicalSpaceSubtype (Fin k → Real)
                (fun (x : Fin k → Real) =>
                  @Membership.mem (Fin k → Real) (Set (Fin k → Real)) (@Set.instMembership (Fin k → Real))
                    (@Set.Icc (Fin k → Real)
                      (@Pi.preorder (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instPreorder)
                      (@OfNat.ofNat (Fin k → Real) (nat_lit 0)
                        (@Zero.toOfNat0 (Fin k → Real)
                          (@Pi.instZero (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instZero)))
                      (@OfNat.ofNat (Fin k → Real) (nat_lit 1)
                        (@One.toOfNat1 (Fin k → Real)
                          (@Pi.instOne (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) => Real.instOne))))
                    x)
                (@Pi.topologicalSpace (Fin k) (fun (a : Fin k) => Real) fun (i : Fin k) =>
                  @UniformSpace.toTopologicalSpace Real
                    (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
:= @OAIExtractedProof_7a8483dc576a.homeo_unit_cube_of_convex_compact
