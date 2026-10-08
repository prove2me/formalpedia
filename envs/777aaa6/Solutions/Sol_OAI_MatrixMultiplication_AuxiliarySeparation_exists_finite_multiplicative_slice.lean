-- Prove2me | solution 1 for OAI.MatrixMultiplication.AuxiliarySeparation.exists_finite_multiplicative_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:33:36.381714+00:00
-- url     : https://prove2.me/submissions/70f93799-8e51-4e12-988a-54c89bc83ca1

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
import Definitions.Def_OAI429_OAI_LinearAlgebra_MatrixMultiplication_AuxiliarySeparation_Spectrum_MultiplicativeStates
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_compact_convex_fixedPoint
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical

namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation
namespace OAI.MatrixMultiplication.AuxiliarySeparation
end OAI.MatrixMultiplication.AuxiliarySeparation
open _root_.OAI
open _root_.OAI.MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAIExtractedProof_b8af684711b1
namespace OAI.MatrixMultiplication.Foundation
end OAI.MatrixMultiplication.Foundation



set_option linter.all false

set_option autoImplicit false

section AllFieldsModule0/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FixedPoint -/
section AbstractModule15


namespace OAI

/-! Fixed points of continuous maps on compact convex sets of real-valued functions. -/

namespace MatrixMultiplication.AuxiliarySeparation

open Set
open scoped BigOperators



















/-- An unbundled form of the product-space fixed-point theorem. -/
theorem compact_convex_fixedPoint_of_continuous {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (f : K → K) (hf : Continuous f) : ∃ x : K, f x = x :=
  compact_convex_fixedPoint hKcompact hKconvex hKne ⟨f, hf⟩

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule15


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.MultiplicativeStates -/
section AbstractModule16


namespace OAI

/-! Multiplicative states obtained by normalizing translates of additive states. -/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S]



theorem normalizedTranslate_continuousOn {K : Set (S → ℝ)} (z : S)
    (hz : ∀ f ∈ K, f z ≠ 0) :
    Continuous (fun f : K => normalizedTranslate z f.val) := by
  apply continuous_pi
  intro x
  exact ((continuous_apply (z * x)).comp continuous_subtype_val).div
    ((continuous_apply z).comp continuous_subtype_val) (fun f => hz f.val f.property)





theorem frozenConstraint_isClosed (z : S) (c : ℝ) :
    IsClosed (frozenConstraint z c) := by
  unfold frozenConstraint
  simp only [setOf_forall]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_apply (z * x)) (continuous_const.mul (continuous_apply x))



theorem frozenSlice_isCompact {C : Set (S → ℝ)} (hC : IsCompact C) (z : S) (c : ℝ) :
    IsCompact (frozenSlice C z c) :=
  hC.inter_right (frozenConstraint_isClosed z c)

theorem frozenConstraint_convex (z : S) (c : ℝ) :
    Convex ℝ (frozenConstraint z c) := by
  intro f hf g hg a b _ _ _ x
  change a * f (z * x) + b * g (z * x) = c * (a * f x + b * g x)
  rw [hf x, hg x]
  ring

theorem frozenSlice_convex {C : Set (S → ℝ)} (hC : Convex ℝ C) (z : S) (c : ℝ) :
    Convex ℝ (frozenSlice C z c) :=
  hC.inter (frozenConstraint_convex z c)

theorem normalizedTranslate_mem_frozenConstraint {z w : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) :
    normalizedTranslate w f ∈ frozenConstraint z c := by
  intro x
  change f (w * (z * x)) / f w = c * (f (w * x) / f w)
  rw [show w * (z * x) = z * (w * x) by ac_rfl, hf (w * x)]
  ring

theorem frozenSlice_mapsTo_normalizedTranslate {C : Set (S → ℝ)} {z w : S} {c : ℝ}
    (hC : MapsTo (normalizedTranslate w) C C) :
    MapsTo (normalizedTranslate w) (frozenSlice C z c) (frozenSlice C z c) := by
  intro f hf
  exact ⟨hC hf.1, normalizedTranslate_mem_frozenConstraint hf.2⟩

theorem frozenConstraint_value {z : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) (hf1 : f 1 = 1) : f z = c := by
  simpa only [mul_one, hf1] using hf 1



theorem normalizedTranslate_eq_mem_frozenConstraint {z : S} {f : S → ℝ}
    (hfz : f z ≠ 0) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) := by
  intro x
  have hx : f (z * x) / f z = f x := congrFun hf x
  exact (div_eq_iff hfz).mp hx |>.trans (mul_comm _ _)

theorem normalizedTranslate_eq_nonzero {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) : f z ≠ 0 := by
  intro hfz
  have hx := congrFun hf 1
  simp [normalizedTranslate, hfz, hf1] at hx

theorem normalizedTranslate_eq_mem_frozenConstraint_of_normalized {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) :=
  normalizedTranslate_eq_mem_frozenConstraint (normalizedTranslate_eq_nonzero hf1 hf) hf

theorem normalizedTranslate_eq_mem_frozenSlice {C : Set (S → ℝ)} {z : S} {f : S → ℝ}
    (hfC : f ∈ C) (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenSlice C z (f z) :=
  ⟨hfC, normalizedTranslate_eq_mem_frozenConstraint_of_normalized hf1 hf⟩

/-- Every finite collection of multiplication identities holds throughout a
nonempty compact convex subset that remains invariant under all translates. -/
theorem exists_finite_multiplicative_slice {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K)
    (t : Finset {z : S // z ≠ 0}) :
    ∃ C : Set (S → ℝ), C ⊆ K ∧ C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
      (∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) C C) ∧
      ∀ f ∈ C, ∀ z ∈ t, ∀ x, f (z.val * x) = f z.val * f x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      exact ⟨K, Subset.rfl, hKne, hKcompact, hKconvex, hKmap, by simp⟩
  | @insert z t hzt ih =>
      obtain ⟨C, hCK, hCne, hCcompact, hCconvex, hCmap, hCt⟩ := ih
      let P : C → C := fun f =>
        ⟨normalizedTranslate z.val f.val, hCmap z.val z.property f.property⟩
      have hP : Continuous P := by
        apply Continuous.subtype_mk
        exact normalizedTranslate_continuousOn z.val
          (fun f hf => hKnonzero f (hCK hf) z.val z.property)
      obtain ⟨g, hg⟩ := compact_convex_fixedPoint_of_continuous
        hCcompact hCconvex hCne P hP
      have hg' : normalizedTranslate z.val g.val = g.val := congrArg Subtype.val hg
      let c : ℝ := g.val z.val
      let D := frozenSlice C z.val c
      have hDC : D ⊆ C := fun _ hf => hf.1
      have hDK : D ⊆ K := hDC.trans hCK
      refine ⟨D, hDK, ?_, frozenSlice_isCompact hCcompact z.val c,
        frozenSlice_convex hCconvex z.val c, ?_, ?_⟩
      · exact ⟨g.val, normalizedTranslate_eq_mem_frozenSlice g.property
          (hKnorm g.val (hCK g.property)) hg'⟩
      · intro w hw
        exact frozenSlice_mapsTo_normalizedTranslate (hCmap w hw)
      · intro f hf w hw x
        rcases Finset.mem_insert.mp hw with rfl | hwt
        · have hfc : f w.val = c := frozenConstraint_value hf.2 (hKnorm f (hDK hf))
          rw [hfc]
          exact hf.2 x
        · exact hCt f (hDC hf) w hwt x







end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end AbstractModule16


end AllFieldsModule0

end OAIExtractedProof_b8af684711b1

theorem solution.{u_1} :
    ∀ {S : Type u_1} [inst : CommSemiring S] {K : Set (S → ℝ)},
  IsCompact K →
    Convex ℝ K →
      K.Nonempty →
        (∀ f ∈ K, f 1 = 1) →
          (∀ f ∈ K, ∀ (z : S), z ≠ 0 → f z ≠ 0) →
            (∀ (z : S), z ≠ 0 → Set.MapsTo (OAI.MatrixMultiplication.AuxiliarySeparation.normalizedTranslate z) K K) →
              ∀ (t : Finset { z : S // z ≠ 0 }),
                ∃ C ⊆ K,
                  C.Nonempty ∧
                    IsCompact C ∧
                      Convex ℝ C ∧
                        (∀ (z : S),
                            z ≠ 0 →
                              Set.MapsTo (OAI.MatrixMultiplication.AuxiliarySeparation.normalizedTranslate z) C C) ∧
                          ∀ f ∈ C, ∀ z ∈ t, ∀ (x : S), f (↑z * x) = f ↑z * f x
:= @OAIExtractedProof_b8af684711b1.OAI.MatrixMultiplication.AuxiliarySeparation.exists_finite_multiplicative_slice
