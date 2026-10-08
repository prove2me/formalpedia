-- Prove2me | solution 1 for strong_cubical_sperner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:24:30.412588+00:00
-- url     : https://prove2.me/submissions/bd50e8e1-5c8f-4597-b9f4-18f3ff748c43

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
import Definitions.Def_OAI429_FixedPointTheorems_cubical_sperner
import Definitions.Def_OAI429_FixedPointTheorems_cubical_sperner_prep
import Theorems.Thm_boundary_is_A_or_B
import Theorems.Thm_case_B_parent_count
import Theorems.Thm_child_map_surj_on
import Theorems.Thm_complete_child_uniq
import Theorems.Thm_handshake_1
import Theorems.Thm_incomplete_childs
import Theorems.Thm_induction_start
import Theorems.Thm_parent_count
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical


namespace OAIExtractedProof_434a8eace084


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



























































end cases_ABCD



lemma case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)



end AbstractModule10


/- BEGIN FixedPointTheorems.cubical_sperner -/
section AbstractModule11


/-!
# The cubical Sperner lemma

Boundary incidence counts give an odd number of completely labelled simplices.
The induction restricts a labelled cube to its boundary face; the resulting
existence theorem supplies the simplices used in the fixed-point argument.
-/


open Classical

section completeness











lemma complete_boundary_face_last {SC n1} {hn1 : n1 + 1 = SC.n} (I : Fin (n1 + 1) → SC.G)
    (hcbf : complete_boundary_face SC I) :
    ∀ i, ∀ j, j.1 + 1 = SC.n →  (I i j).1 = SC.p := by {
  intro i j hj
  revert i
  have h3 := @boundary_is_A_or_B SC n1 hn1 I hcbf.1
  have h1 : j.1 = n1 := by omega
  have h4 : ∀ n2, n2 ≤ n1 → ∃ i, SC.RL (I i) = n2 := by {
    intro n2 hn2
    rw [← Set.mem_range, hcbf.2.2]
    simp only [Set.mem_setOf_eq, hn2]
  }
  have h6 (j2 : Fin SC.n) : j2.1 ≤ n1 := by omega
  cases h3
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    exfalso
    obtain ⟨i, hi⟩ := h4 j2.1 (h6 j2)
    have h5 := ((SC.rl_proper (I i)).2 j2).1 (hj2 i)
    exact h5 hi
  }
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    have hj3 i : (I i j2).1 = SC.p := by {
      rw [hj2 i]
      exact Fin.val_last SC.p
    }
    suffices h3 : j = j2 by {
      intro i
      rw [h3, hj3 i]
    }
    have h3 := SC.rl_proper
    obtain ⟨i, hi⟩ := h4 n1 (Nat.le_refl n1)
    have h5 := ((SC.rl_proper (I i)).2 j2).2 (hj3 i)
    rw [hi] at h5
    ext
    rw [h1]
    exact Nat.le_antisymm h5 (h6 j2)
  }
}

end completeness

section handshake

variable {A B : Type*}
variable [Fintype A] [Fintype B]







end handshake

lemma odd_of_boundary_faces SC {n1} {hn1 : n1 + 1 = SC.n}:
    Odd (Finset.card { I : Fin (n1 + 1) → SC.G | complete_boundary_face SC I})
    → Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  apply handshake_1 (is_face SC)
  apply @complete_child_uniq SC n1 hn1
  apply @incomplete_childs SC n1 hn1
  apply @parent_count SC n1 hn1
  {
    intro I
    rfl
  }
  exact fun _ h1 ↦ h1.1
  exact fun _ _ h1 ↦ h1.2.1
}

section induction_step

variable (SC : SpernerCube)
variable {n1 : ℕ}







lemma child_map_inj {hn1 : n1 + 1 = SC.n }: Function.Injective (@child_map SC n1) := by {
  intro v1 v2 h1
  ext i
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  rw [← child_map_applied SC v1]
  rw [← child_map_applied SC v2]
  rwa [h1]
  exact hn1
}





end induction_step



theorem strong_cubical_sperner (k: ℕ ) : ∀ (SC : SpernerCube), k = SC.n →
    Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  induction' k with k hind
  {
    intro SC hk
    exact induction_start SC hk
  }
  {
    intro SC1 hk1
    apply @odd_of_boundary_faces SC1 k hk1
    let SC2 := @child_cube SC1 k hk1
    have hnz : NeZero SC1.n := by {
      rw [← hk1]
      exact instNeZeroNatHAdd_1
    }
    have h2 := hind SC2 rfl
    apply Eq.mpr _ h2
    apply congrArg
    let f1 : SC2.G → SC1.G := child_map SC1
    let f2 : (Fin (k+1)→ SC2.G) → (Fin (k+1)→ SC1.G) := fun a ↦ fun b ↦ f1 (a b)
    have hf1inj : Function.Injective f1 := by {
      apply child_map_inj SC1
      rw [← hk1]
      rfl
    }
    symm
    have hcomp I : complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 SC2.n I := by {
      unfold complete_boundary_face complete_simplex
      have h_last j k: j.1 + 1 = SC1.n → f2 I k j = SC1.p := by {
        apply child_map_last
      }
      have h_bf : simplex SC1 k (f2 I) ↔ is_boundary_face SC1 (f2 I) ∧ simplex SC1 k (f2 I):= by {
        simp only [iff_and_self]
        intro hs
        apply @case_B_boundary SC1 k hk1
        exact hs
        use (Fin.ofNat _ k)
        intro i
        ext
        apply h_last
        simp [← hk1]
      }
      rw [← and_assoc, ←h_bf]
      have h3 : SC2.n = k := rfl
      apply and_congr
      apply and_congr
      {
        apply Iff.intro
        {
          intro h4 i1 i2 h5
          exact h4 (congrArg f1 h5)
        }
        {
          intro h4 i1 i2 h5
          apply h4
          apply hf1inj h5
        }
      }
      {
        simp only [h3]
        apply forall₂_congr
        intro i hi1
        apply Iff.intro
        {
          intro h4 j
          have h6 k : (f2 I k (Fin.ofNat _ j.1)) = (I k j) := by {
            unfold f2
            apply child_map_applied
            rw [← hk1]
            rfl
          }
          change (I (Fin.ofNat (k + 1) i) j).val ≤
            (I (Fin.ofNat (k + 1) (i + 1)) j).val ∧
            (I (Fin.last k) j).val ≤ (I 0 j).val + 1
          rw [← h6, ← h6, ←h6, ← h6]
          exact h4 (Fin.ofNat _ j.1)
        }
        {
          intro h4 j
          by_cases h5 : j.1 + 1 = SC1.n
          {
            rw [h_last, h_last, h_last, h_last]
            simp only [le_refl, le_add_iff_nonneg_right, zero_le,
              and_self]
            repeat' exact h5
          }
          {
            have h7 : j.1 < SC2.n := by {
              rw [h3]
              have h6 := j.2
              simp only [← hk1] at h5 h6
              omega
            }
            have hn02 : NeZero SC2.n := by {
              exact NeZero.of_gt hi1
            }
            let j2 : Fin SC2.n := (Fin.ofNat _ j.1)
            have h8 : j = (Fin.ofNat _ j2.1) := by {
              unfold j2
              simp only [Fin.ofNat_eq_cast,]
              rw [Fin.val_cast_of_lt]
              exact Eq.symm (Fin.cast_val_eq_self j)
              exact h7
            }
            have h6 k : (f2 I k j) = (I k j2) := by {
              unfold f2
              rw [h8]
              apply child_map_applied
              exact hk1
            }
            rw [h6, h6, h6, h6]
            exact h4 j2
          }
        }
      }
      exact Eq.congr_right rfl
    }
    change ∀ I, complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 k I at hcomp
    change ({I : Fin (k + 1) → SC2.G | complete_simplex SC2 k I} : Finset _).card =
      ({I : Fin (k + 1) → SC1.G | complete_boundary_face SC1 I} : Finset _).card
    apply Finset.card_nbij f2
    {
      intro I hI
      have hI' : complete_simplex SC2 k I := by
        simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using hI
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        using (hcomp I).mpr hI'
    }
    {
      intro I1 h41 I2 h42 h5
      ext i
      apply hf1inj
      exact congrFun h5 i
    }
    {
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      intro J
      simp only [Set.mem_setOf_eq, Set.mem_image]
      intro h3
      have h4 : ∃ I, f2 I = J := by {
        suffices h6 : ∀ i, ∃ ii, f1 ii = J i by {
          obtain ⟨I, h5⟩  := axiomOfChoice h6
          use I
          ext i
          exact h5 i
        }
        intro i
        have h5 := @child_map_surj_on SC1 k hk1
        apply h5
        exact @complete_boundary_face_last SC1 k hk1 J h3 i
      }
      obtain ⟨I, h4⟩ := h4
      use I
      simp only [h4, and_true]
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        using (hcomp I).mp (h4 ▸ h3)
    }
  }

}



end AbstractModule11


end AllFieldsModule0

end OAIExtractedProof_434a8eace084

theorem solution :
    ∀ (k : ℕ) (SC : SpernerCube),
  k = SC.n → Odd (Finset.card (α := Fin (SC.n + 1) → SC.G) {I : Fin (SC.n + 1) → SC.G | complete_simplex SC SC.n I})
:= @OAIExtractedProof_434a8eace084.strong_cubical_sperner
