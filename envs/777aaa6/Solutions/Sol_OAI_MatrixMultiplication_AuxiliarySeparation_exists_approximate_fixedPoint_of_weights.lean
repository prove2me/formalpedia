-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.exists_approximate_fixedPoint_of_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:28:52.7144+00:00
-- url     : https://prove2.me/submissions/38cbade3-fbc1-47bd-b596-1121beec7e2e

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
import Definitions.Def_OAI429_FixedPointTheorems_apply_cubical_sperner
import Definitions.Def_OAI429_OAI_LinearAlgebra_MatrixMultiplication_AuxiliarySeparation_Convex_FixedPoint
import Theorems.Thm_fixed_point_unit_cube
import Theorems.Thm_homeo_unit_cube_of_convex_compact
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_0955819d7c02


set_option linter.all false

set_option autoImplicit false

section AllFieldsModule0/- BEGIN FixedPointTheorems.brouwer -/
section AbstractModule14



/-!
# Brouwer's fixed-point theorem

The unit-cube fixed-point theorem is transported along a homeomorphism of a
nonempty compact convex set. The resulting theorem is also expressed using
`Function.IsFixedPt` and the set of fixed points.
-/


theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}





end AbstractModule14


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FixedPoint -/
section AbstractModule15


namespace OAI

/-! Fixed points of continuous maps on compact convex sets of real-valued functions. -/

namespace MatrixMultiplication.AuxiliarySeparation

open Set
open scoped BigOperators



private theorem weightSimplex_convex (J : Type*) [Fintype J] :
    Convex ℝ (weightSimplex J) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    simpa using hab

private theorem weightSimplex_compact (J : Type*) [Fintype J] :
    IsCompact (weightSimplex J) := by
  have hc : IsClosed (weightSimplex J) := by
    change IsClosed ({w : J → ℝ | ∀ j, 0 ≤ w j} ∩ {w | ∑ j, w j = 1})
    have hn : IsClosed {w : J → ℝ | ∀ j, 0 ≤ w j} := by
      simp only [setOf_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const
        (continuous_apply j : Continuous (fun w : J → ℝ => w j))
    exact hn.inter
      (isClosed_eq (continuous_finset_sum _ fun _ _ => continuous_apply _) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro w hw
  constructor
  · exact hw.1
  · intro j
    calc
      w j ≤ ∑ k, w k := Finset.single_le_sum (fun k _ => hw.1 k) (Finset.mem_univ j)
      _ = 1 := hw.2

/-- A finite continuous system of barycentric weights gives an approximate fixed point.
The approximation is measured on any prescribed finite set of coordinates. -/
theorem exists_approximate_fixedPoint_of_weights
    {I J : Type*} [Fintype J] [Nonempty J]
    {K : Set (I → ℝ)} (hK : Convex ℝ K) (f : C(K, K))
    (a : J → K) (w : J → C(K, ℝ))
    (hw0 : ∀ j x, 0 ≤ w j x) (hw1 : ∀ x, ∑ j, w j x = 1)
    (s : Finset I) (ε : ℝ)
    (hclose : ∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| ≤ ε) :
    ∃ x : K, ∀ i ∈ s, |(f x).val i - x.val i| ≤ ε := by
  classical
  let D := weightSimplex J
  let b : D → K := fun v =>
    ⟨∑ j, v.val j • (a j).val,
      hK.sum_mem (fun j _ => v.property.1 j) v.property.2 (fun j _ => (a j).property)⟩
  have hb : Continuous b := by
    apply Continuous.subtype_mk
    exact continuous_finset_sum _ fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).smul continuous_const
  let q : K → D := fun x => ⟨fun j => w j x, (fun j => hw0 j x), hw1 x⟩
  have hq : Continuous q := by
    exact (continuous_pi fun j => (w j).continuous).subtype_mk _
  let g : C(D, D) := ⟨fun v => q (f (b v)), hq.comp (f.continuous.comp hb)⟩
  have hDne : D.Nonempty := by
    let j₀ : J := Classical.choice inferInstance
    refine ⟨Pi.single j₀ 1, ?_, ?_⟩
    · intro j
      by_cases h : j = j₀ <;> simp [Pi.single_apply, h, eq_comm]
    · simp
  obtain ⟨v, hv⟩ := brouwer_fixed_point D (weightSimplex_convex J)
    (weightSimplex_compact J) hDne g
  let x := b v
  have hwv (j : J) : w j (f x) = v.val j := congrArg (fun t : D => t.val j) hv
  refine ⟨x, fun i hi => ?_⟩
  have hx : x.val i - (f x).val i = ∑ j, v.val j * ((a j).val i - (f x).val i) := by
    change (∑ j, v.val j • (a j).val) i - (f x).val i = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, v.property.2, one_mul]
  rw [abs_sub_comm, hx]
  calc
    |∑ j, v.val j * ((a j).val i - (f x).val i)|
        ≤ ∑ j, |v.val j * ((a j).val i - (f x).val i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, v.val j * |(a j).val i - (f x).val i| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (v.property.1 j)]
    _ ≤ ∑ j, v.val j * ε := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : v.val j = 0
      · simp [hj]
      · exact mul_le_mul_of_nonneg_left
          (hclose (f x) j (by rwa [hwv]) i hi) (v.property.1 j)
    _ = ε := by rw [← Finset.sum_mul, v.property.2, one_mul]













end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule15


end AllFieldsModule0

end OAIExtractedProof_0955819d7c02

theorem solution.{u_1, u_2} :
    ∀ {I : Type u_1} {J : Type u_2} [inst : Fintype J] [Nonempty J] {K : Set (I → Real)},
  @Convex Real (I → Real) Real.semiring Real.partialOrder
      (@Pi.addCommMonoid I (fun (a : I) => Real) fun (i : I) => Real.instAddCommMonoid)
      (@Function.hasSMul I Real Real
        (@Algebra.toSMul Real Real Real.instCommSemiring (@CommSemiring.toSemiring Real Real.instCommSemiring)
          (@Algebra.id Real Real.instCommSemiring)))
      K →
    ∀
      (f :
        @ContinuousMap (@Set.Elem (I → Real) K) (@Set.Elem (I → Real) K)
          (@instTopologicalSpaceSubtype (I → Real)
            (fun (x : I → Real) => @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
            (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
              @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
          (@instTopologicalSpaceSubtype (I → Real)
            (fun (x : I → Real) => @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
            (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
              @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
      (a : J → @Set.Elem (I → Real) K)
      (w :
        J →
          @ContinuousMap (@Set.Elem (I → Real) K) Real
            (@instTopologicalSpaceSubtype (I → Real)
              (fun (x : I → Real) => @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
              (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
            (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))),
      (∀ (j : J) (x : @Set.Elem (I → Real) K),
          @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
            (@DFunLike.coe
              (@ContinuousMap (@Set.Elem (I → Real) K) Real
                (@instTopologicalSpaceSubtype (I → Real)
                  (fun (x : I → Real) =>
                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                    @UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
              (@Set.Elem (I → Real) K) (fun (x : @Set.Elem (I → Real) K) => Real)
              (@ContinuousMap.instFunLike (@Set.Elem (I → Real) K) Real
                (@instTopologicalSpaceSubtype (I → Real)
                  (fun (x : I → Real) =>
                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                    @UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
              (w j) x)) →
        (∀ (x : @Set.Elem (I → Real) K),
            @Eq Real
              (∑ j : J,
                @DFunLike.coe
                  (@ContinuousMap (@Set.Elem (I → Real) K) Real
                    (@instTopologicalSpaceSubtype (I → Real)
                      (fun (x : I → Real) =>
                        @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                      (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                        @UniformSpace.toTopologicalSpace Real
                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                    (@UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                  (@Set.Elem (I → Real) K) (fun (x : @Set.Elem (I → Real) K) => Real)
                  (@ContinuousMap.instFunLike (@Set.Elem (I → Real) K) Real
                    (@instTopologicalSpaceSubtype (I → Real)
                      (fun (x : I → Real) =>
                        @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                      (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                        @UniformSpace.toTopologicalSpace Real
                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                    (@UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                  (w j) x)
              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
          ∀ (s : Finset I) (ε : Real),
            (∀ (x : @Set.Elem (I → Real) K) (j : J),
                @Ne Real
                    (@DFunLike.coe
                      (@ContinuousMap (@Set.Elem (I → Real) K) Real
                        (@instTopologicalSpaceSubtype (I → Real)
                          (fun (x : I → Real) =>
                            @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                          (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                            @UniformSpace.toTopologicalSpace Real
                              (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                        (@UniformSpace.toTopologicalSpace Real
                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                      (@Set.Elem (I → Real) K) (fun (x : @Set.Elem (I → Real) K) => Real)
                      (@ContinuousMap.instFunLike (@Set.Elem (I → Real) K) Real
                        (@instTopologicalSpaceSubtype (I → Real)
                          (fun (x : I → Real) =>
                            @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                          (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                            @UniformSpace.toTopologicalSpace Real
                              (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                        (@UniformSpace.toTopologicalSpace Real
                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                      (w j) x)
                    (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
                  ∀ (i : I),
                    @Membership.mem I (Finset I) (@SetLike.instMembership (Finset I) I (@Finset.instSetLike I)) s i →
                      @LE.le Real Real.instLE
                        (@abs Real Real.lattice Real.instAddGroup
                          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                            (@Subtype.val (I → Real)
                              (fun (x : I → Real) =>
                                @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                              (a j) i)
                            (@Subtype.val (I → Real)
                              (fun (x : I → Real) =>
                                @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                              x i)))
                        ε) →
              ∃ (x : @Set.Elem (I → Real) K),
                ∀ (i : I),
                  @Membership.mem I (Finset I) (@SetLike.instMembership (Finset I) I (@Finset.instSetLike I)) s i →
                    @LE.le Real Real.instLE
                      (@abs Real Real.lattice Real.instAddGroup
                        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                          (@Subtype.val (I → Real)
                            (fun (x : I → Real) =>
                              @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                            (@DFunLike.coe
                              (@ContinuousMap (@Set.Elem (I → Real) K) (@Set.Elem (I → Real) K)
                                (@instTopologicalSpaceSubtype (I → Real)
                                  (fun (x : I → Real) =>
                                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                                (@instTopologicalSpaceSubtype (I → Real)
                                  (fun (x : I → Real) =>
                                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
                              (@Set.Elem (I → Real) K) (fun (x : @Set.Elem (I → Real) K) => @Set.Elem (I → Real) K)
                              (@ContinuousMap.instFunLike (@Set.Elem (I → Real) K) (@Set.Elem (I → Real) K)
                                (@instTopologicalSpaceSubtype (I → Real)
                                  (fun (x : I → Real) =>
                                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)))
                                (@instTopologicalSpaceSubtype (I → Real)
                                  (fun (x : I → Real) =>
                                    @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                                  (@Pi.topologicalSpace I (fun (a : I) => Real) fun (i : I) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))))
                              f x)
                            i)
                          (@Subtype.val (I → Real)
                            (fun (x : I → Real) =>
                              @Membership.mem (I → Real) (Set (I → Real)) (@Set.instMembership (I → Real)) K x)
                            x i)))
                      ε
:= @OAIExtractedProof_0955819d7c02.OAI.MatrixMultiplication.AuxiliarySeparation.exists_approximate_fixedPoint_of_weights
