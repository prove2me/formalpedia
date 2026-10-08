-- Prove2me | solution 1 for mme_omega_le_225
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T05:44:30.13232+00:00
-- url     : https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134

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
import Definitions.Def_mme_omega
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

set_option linter.all false

set_option autoImplicit false

/- BEGIN all-fields module GenericAbstract -/
section AllFieldsModule0

set_option autoImplicit false

section CompatibilityAliases

universe u

/- Compatibility aliases: Lean 4.34.1 Init/Core.lean names, proved by their
   Lean 4.33.1 predecessors without changing the source statements. -/
private theorem GenericAbstract_ite_eq_left {c : Prop} {h : Decidable c} (hc : c)
    {α : Sort u} {t e : α} : ite c t e = t := if_pos hc
private theorem GenericAbstract_ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c)
    {α : Sort u} {t e : α} : ite c t e = e := if_neg hnc
private theorem GenericAbstract_dite_eq_left {c : Prop} {h : Decidable c} (hc : c)
    {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = t hc := dif_pos hc
private theorem GenericAbstract_dite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c)
    {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = e hnc := dif_neg hnc
/- From Mathlib 4.34.1 Order/Antisymmetrization.lean, unchanged proof. -/
private theorem GenericAbstract_toAntisymmetrization_eq {α : Type u} (r : α → α → Prop)
    [IsPreorder α r] (a b : α) :
    toAntisymmetrization r a = toAntisymmetrization r b ↔ AntisymmRel r a b :=
  Quotient.eq

end CompatibilityAliases



/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.NormalizedStates -/
section AbstractModule0


namespace OAI

/-!
# Compact convex spaces of normalized additive states

These are the closed linear constraints in Appendix A. The nonemptiness of
this state space, and its instantiation by the tensor restriction semiring,
are separate statements.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- Additive restriction-monotone states with a fixed detector inequality. -/
def normalizedStates (R : S → ℝ) (d : S) (k : ℝ) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧
    (∀ x, k * f x ≤ f (d * x))}

theorem normalizedStates_isClosed (R : S → ℝ) (d : S) (k : ℝ) :
    IsClosed (normalizedStates R d k) := by
  unfold normalizedStates
  have hb : IsClosed {f : S → ℝ | ∀ x, 0 ≤ f x ∧ f x ≤ R x} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro x
    exact (isClosed_le continuous_const (continuous_apply x)).inter
      (isClosed_le (continuous_apply x) continuous_const)
  have hn : IsClosed {f : S → ℝ | f 1 = 1} :=
    isClosed_eq (continuous_apply 1) continuous_const
  have ha : IsClosed {f : S → ℝ | ∀ x y, f (x + y) = f x + f y} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y))
        ((continuous_apply x).add (continuous_apply y))
  have hm : IsClosed {f : S → ℝ | ∀ x y, x ≤ y → f x ≤ f y} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => isClosed_le (continuous_apply x) (continuous_apply y)
  have hd : IsClosed {f : S → ℝ | ∀ x, k * f x ≤ f (d * x)} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun x =>
      isClosed_le (continuous_const.mul (continuous_apply x)) (continuous_apply (d * x))
  exact hb.inter (hn.inter (ha.inter (hm.inter hd)))

theorem normalizedStates_isCompact (R : S → ℝ) (d : S) (k : ℝ) :
    IsCompact (normalizedStates R d k) := by
  apply (isCompact_univ_pi (fun x => isCompact_Icc (a := (0 : ℝ)) (b := R x))).of_isClosed_subset
    (normalizedStates_isClosed R d k)
  intro f hf x _
  exact hf.1 x

theorem normalizedStates_convex (R : S → ℝ) (d : S) (k : ℝ) :
    Convex ℝ (normalizedStates R d k) := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change 0 ≤ a * f x + b * g x ∧ a * f x + b * g x ≤ R x
    constructor
    · exact add_nonneg (mul_nonneg ha (hf.1 x).1) (mul_nonneg hb (hg.1 x).1)
    · calc
        a * f x + b * g x ≤ a * R x + b * R x :=
          add_le_add (mul_le_mul_of_nonneg_left (hf.1 x).2 ha)
            (mul_le_mul_of_nonneg_left (hg.1 x).2 hb)
        _ = R x := by rw [← add_mul, hab, one_mul]
  · change a * f 1 + b * g 1 = 1
    rw [hf.2.1, hg.2.1, mul_one, mul_one, hab]
  · intro x y
    change a * f (x + y) + b * g (x + y) =
      (a * f x + b * g x) + (a * f y + b * g y)
    rw [hf.2.2.1, hg.2.2.1]
    ring
  · intro x y hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 x y hxy) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.1 x y hxy) hb)
  · intro x
    change k * (a * f x + b * g x) ≤ a * f (d * x) + b * g (d * x)
    calc
      k * (a * f x + b * g x) = a * (k * f x) + b * (k * g x) := by ring
      _ ≤ a * f (d * x) + b * g (d * x) :=
        add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.2 x) ha)
          (mul_le_mul_of_nonneg_left (hg.2.2.2.2 x) hb)

theorem state_zero {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) : f 0 = 0 := by
  have h := hf.2.2.1 0 0
  rw [zero_add] at h
  linarith

theorem state_nat_mul {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) (n : ℕ) (x : S) :
    f ((n : S) * x) = (n : ℝ) * f x := by
  induction n with
  | zero => simp [state_zero hf]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hf.2.2.1, ih]
    push_cast
    ring

theorem state_one_le {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) {z : S} (hz : 1 ≤ z) : 1 ≤ f z := by
  simpa only [hf.2.1] using hf.2.2.2.1 1 z hz

/-- Translation followed by normalization preserves every state constraint.
The two order hypotheses are exactly those supplied by tensor multiplication
and the finite rank bound in the restriction semiring. -/
theorem state_rescale {R : S → ℕ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates (fun x => (R x : ℝ)) d k) (z : S)
    (hz : 1 ≤ z)
    (hmulmono : ∀ x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ x : S, z * x ≤ (R x : S) * z) :
    (fun x => f (z * x) / f z) ∈ normalizedStates (fun x => (R x : ℝ)) d k := by
  have hfz : 0 < f z := lt_of_lt_of_le zero_lt_one (state_one_le hf hz)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨div_nonneg (hf.1 (z * x)).1 hfz.le, ?_⟩
    apply (div_le_iff₀ hfz).mpr
    have h := hf.2.2.2.1 (z * x) ((R x : S) * z) (hdom x)
    simpa only [state_nat_mul hf] using h
  · simp [mul_one, ne_of_gt hfz]
  · intro x y
    change f (z * (x + y)) / f z = f (z * x) / f z + f (z * y) / f z
    rw [mul_add, hf.2.2.1, add_div]
  · intro x y hxy
    exact div_le_div_of_nonneg_right (hf.2.2.2.1 _ _ (hmulmono x y hxy)) hfz.le
  · intro x
    have h := hf.2.2.2.2 (z * x)
    have hc : d * (z * x) = z * (d * x) := by ring
    rw [hc] at h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hfz.le

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end AbstractModule0


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalSpan -/
section AbstractModule1



namespace OAI

/-!
# Descent of rational linear systems

A rational linear system which has a real oai_arithmetic_solution also has a rational oai_arithmetic_solution.
The proof applies a rational-linear projection from the reals onto the rationals.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- A rational-linear functional on the reals taking `1` to `1`. -/
theorem exists_ratLinear_one :
    ∃ p : ℝ →ₗ[ℚ] ℚ, p 1 = 1 :=
  Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)

/-- A rational-linear projection from the reals to the rationals. -/
theorem exists_ratLinear_retraction :
    ∃ p : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, p (q : ℝ) = q := by
  obtain ⟨p, hp⟩ := exists_ratLinear_one
  refine ⟨p, fun q ↦ ?_⟩
  have h := p.map_smul q (1 : ℝ)
  simpa [hp] using h

/-- Solvability of a finite rational linear system descends from real to rational
coefficients. The set of equations need not be finite. -/
theorem exists_rat_solution_of_real {I : Type*} {J : Type*} [Fintype I]
    (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ q : I → ℚ, ∀ j, ∑ i, q i * A i j = b j := by
  obtain ⟨p, hp⟩ := exists_ratLinear_retraction
  obtain ⟨x, hx⟩ := h
  refine ⟨fun i ↦ p (x i), fun j ↦ ?_⟩
  have heq := congrArg p (hx j)
  simp only [map_sum, hp] at heq
  convert heq using 1
  apply Finset.sum_congr rfl
  intro i _
  have hmul := p.map_smul (A i j) (x i)
  simpa only [Rat.smul_def, smul_eq_mul, mul_comm] using hmul.symm

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule1


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalDenominators -/
section AbstractModule2



namespace OAI

/-!
# Clearing denominators in nonnegative rational families
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Every natural multiple of a denominator clears its nonnegative rational. -/
theorem exists_nat_eq_mul_rat_of_den_dvd {q : ℚ} (hq : 0 ≤ q)
    {D : ℕ} (hD : q.den ∣ D) :
    ∃ c : ℕ, (D : ℚ) * q = (c : ℚ) := by
  obtain ⟨k, rfl⟩ := hD
  refine ⟨k * q.num.toNat, ?_⟩
  have hnum : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  push_cast
  rw [hnum]
  calc
    (q.den : ℚ) * k * q = k * ((q.den : ℚ) * q) := by ring
    _ = k * (q.num : ℚ) := by rw [Rat.den_mul_eq_num]

/-- A finite nonnegative rational family has a common positive denominator
which turns every coefficient into a natural number. -/
theorem exists_nat_mul_eq_nat {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ, ∀ i, (D : ℚ) * q i = (c i : ℚ) := by
  classical
  let D : ℕ := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
  have hc : ∀ i, ∃ c : ℕ, (D : ℚ) * q i = (c : ℚ) := by
    intro i
    exact exists_nat_eq_mul_rat_of_den_dvd (hq i)
      (Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (Finset.mem_univ i))
  choose c hc using hc
  exact ⟨D, hD, c, hc⟩

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule2


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalCone -/
section AbstractModule3





namespace OAI

/-!+# Rational nonnegative certificates

Finite rational linear systems with a nonnegative real oai_arithmetic_solution have a
nonnegative rational oai_arithmetic_solution. Affinely independent convex representations
allow a rational-linear projection to preserve the coefficients exactly.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Coordinatewise inclusion of rational vectors into real vectors. -/
def rationalVectorCast {J : Type*} (v : J → ℚ) : J → ℝ := fun j ↦ v j

@[simp] theorem rationalVectorCast_apply {J : Type*} (v : J → ℚ) (j : J) :
    rationalVectorCast v j = (v j : ℝ) := rfl

/-- In an affinely independent rational family, the coefficients of a real
convex representation of a rational point are rational. -/
theorem exists_rat_convex_weights_of_affineIndependent
    {I J : Type*} [Fintype I] (v : I → J → ℚ) (b : J → ℚ)
    (w : I → ℝ)
    (hpos : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (heq : ∑ i, w i • rationalVectorCast (v i) = rationalVectorCast b)
    (hind : AffineIndependent ℝ (fun i ↦ rationalVectorCast (v i))) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      ∑ i, q i • v i = b := by
  classical
  obtain ⟨p, hp⟩ := exists_ratLinear_retraction
  have hpone : p 1 = 1 := by simpa using hp 1
  let q : I → ℚ := fun i ↦ p (w i)
  have hqsum : ∑ i, q i = 1 := by
    simpa only [q, map_sum, hpone] using congrArg p hsum
  have hqeq : ∑ i, q i • v i = b := by
    funext j
    have hj := congrFun heq j
    simp only [Finset.sum_apply, Pi.smul_apply, rationalVectorCast_apply,
      smul_eq_mul] at hj
    have hj' := congrArg p hj
    simp only [map_sum, hp] at hj'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    convert hj' using 1
    apply Finset.sum_congr rfl
    intro i _
    have hm := p.map_smul (v i j) (w i)
    simpa only [q, Rat.smul_def, smul_eq_mul, mul_comm] using hm.symm
  have hqsumReal : ∑ i, (q i : ℝ) = 1 := by exact_mod_cast hqsum
  have hqeqReal :
      ∑ i, (q i : ℝ) • rationalVectorCast (v i) = rationalVectorCast b := by
    funext j
    have hj := congrFun hqeq j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
    simpa only [Finset.sum_apply, Pi.smul_apply, rationalVectorCast_apply,
      smul_eq_mul] using (show (∑ i, (q i : ℝ) * (v i j : ℝ)) = (b j : ℝ) by
        exact_mod_cast hj)
  have hqw : ∀ i, (q i : ℝ) = w i := by
    intro i
    exact hind.eq_of_sum_eq_sum (s := Finset.univ)
      (hqsumReal.trans hsum.symm) (hqeqReal.trans heq.symm) i (Finset.mem_univ i)
  refine ⟨q, ?_, hqsum, hqeq⟩
  intro i
  exact_mod_cast (hqw i ▸ hpos i : 0 ≤ (q i : ℝ))

/-- Taking the convex hull of rational vectors in real space does not create
new rational points. -/
theorem rationalVectorCast_mem_convexHull_descend
    {J : Type*} {s : Set (J → ℚ)} {b : J → ℚ}
    (h : rationalVectorCast b ∈ convexHull ℝ (rationalVectorCast '' s)) :
    b ∈ convexHull ℚ s := by
  classical
  obtain ⟨I, hI, z, w, hz, hind, hpos, hsum, heq⟩ :=
    eq_pos_convex_span_of_mem_convexHull h
  let : Fintype I := hI
  have hv : ∀ i, ∃ v ∈ s, rationalVectorCast v = z i := by
    intro i
    exact hz (Set.mem_range_self i)
  choose v hv hvc using hv
  obtain ⟨q, hqpos, hqsum, hqeq⟩ :=
    exists_rat_convex_weights_of_affineIndependent v b w (fun i ↦ (hpos i).le)
      hsum (by simpa only [hvc] using heq) (by simpa only [hvc] using hind)
  exact mem_convexHull_of_exists_fintype q v hqpos hqsum hv hqeq

/-- A rational point in the real cone generated by a finite rational family
already lies in the rational cone generated by that family. -/
theorem mem_rationalCone_of_nonneg_real_solution
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (x : I → ℝ) (hxpos : ∀ i, 0 ≤ x i)
    (hxeq : ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    b ∈ PointedCone.span ℚ (Set.range A) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, x i)
  have hNpos : (0 : ℝ) < N :=
    (Finset.sum_nonneg fun i _ ↦ hxpos i).trans_lt hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hNrat : (N : ℚ) ≠ 0 := by exact_mod_cast hNne
  let scaled : J → ℚ := fun j ↦ b j / N
  let v : Option I → J → ℚ := fun i ↦ match i with
    | none => 0
    | some i => A i
  let w : Option I → ℝ := fun i ↦ match i with
    | none => 1 - (∑ i, x i) / N
    | some i => x i / N
  have hwpos : ∀ i, 0 ≤ w i := by
    intro i
    cases i with
    | none =>
      change 0 ≤ 1 - (∑ i, x i) / N
      exact sub_nonneg.mpr ((div_le_one hNpos).2 hN.le)
    | some i => exact div_nonneg (hxpos i) hNpos.le
  have hwsum : ∑ i, w i = 1 := by
    simp only [Fintype.sum_option, w, ← Finset.sum_div]
    ring
  have hweq : ∑ i, w i • rationalVectorCast (v i) = rationalVectorCast scaled := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_option, w, v, rationalVectorCast_apply, Pi.zero_apply,
      Rat.cast_zero, mul_zero, zero_add, scaled, Rat.cast_div, Rat.cast_natCast]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hxeq]
  let s : Set (J → ℚ) := insert 0 (Set.range A)
  have hv : ∀ i, rationalVectorCast (v i) ∈ rationalVectorCast '' s := by
    intro i
    refine ⟨v i, ?_, rfl⟩
    cases i with
    | none => exact Set.mem_insert 0 _
    | some i => exact Set.mem_insert_of_mem 0 (Set.mem_range_self i)
  have hcReal : rationalVectorCast scaled ∈
      convexHull ℝ (rationalVectorCast '' s) :=
    mem_convexHull_of_exists_fintype w (fun i ↦ rationalVectorCast (v i))
      hwpos hwsum hv hweq
  have hcRat : scaled ∈ convexHull ℚ s :=
    rationalVectorCast_mem_convexHull_descend hcReal
  have hs : s ⊆ PointedCone.span ℚ (Set.range A) := by
    intro a ha
    rcases ha with rfl | ha
    · exact Submodule.zero_mem _
    · exact PointedCone.subset_span ha
  have hscaled : scaled ∈ PointedCone.span ℚ (Set.range A) :=
    convexHull_min hs (PointedCone.convex _) hcRat
  have hscale : (N : ℚ) • scaled = b := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, scaled]
    field_simp
  rw [← hscale]
  exact PointedCone.smul_mem _ (Nat.cast_nonneg N) hscaled

/-- Nonnegative solvability of a finite rational linear system descends from
real coefficients to rational coefficients. The equation index type may be
infinite. -/
theorem exists_nonneg_rat_solution_of_real
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ ∀ j, ∑ i, q i * A i j = b j := by
  obtain ⟨x, hxpos, hxeq⟩ := h
  have hb := mem_rationalCone_of_nonneg_real_solution A b x hxpos hxeq
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ({x : ℚ // 0 ≤ x})).1 hb
  refine ⟨fun i ↦ (q i : ℚ), fun i ↦ (q i).property, ?_⟩
  intro j
  have hj := congrFun hq j
  simpa only [Finset.sum_apply, Pi.smul_apply, ← Nonneg.coe_smul, smul_eq_mul] using hj

/-- Clearing denominators turns a nonnegative real oai_arithmetic_solution of a rational
system into a positive integer multiple with natural coefficients. -/
theorem exists_nat_scaled_solution_of_nonneg_real
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℚ) * A i j = (D : ℚ) * b j := by
  obtain ⟨q, hqpos, hqeq⟩ := exists_nonneg_rat_solution_of_real A b h
  obtain ⟨D, hDpos, c, hc⟩ := exists_nat_mul_eq_nat q hqpos
  refine ⟨D, hDpos, c, fun j ↦ ?_⟩
  calc
    ∑ i, (c i : ℚ) * A i j = ∑ i, ((D : ℚ) * q i) * A i j := by simp only [hc]
    _ = (D : ℚ) * ∑ i, q i * A i j := by rw [Finset.mul_sum]; simp only [mul_assoc]
    _ = (D : ℚ) * b j := by rw [hqeq]

/-- Integer form of finite cone certificate extraction. This is the form used
when the selected additive relations have integral coefficients. -/
theorem exists_nat_scaled_int_solution_of_nonneg_real
    {I J : Type*} [Fintype I] (A : I → J → ℤ) (b : J → ℤ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = (D : ℤ) * b j := by
  obtain ⟨x, hxpos, hxeq⟩ := h
  obtain ⟨D, hDpos, c, hc⟩ :=
    exists_nat_scaled_solution_of_nonneg_real
      (fun i j ↦ (A i j : ℚ)) (fun j ↦ (b j : ℚ))
      ⟨x, hxpos, by simpa using hxeq⟩
  refine ⟨D, hDpos, c, fun j ↦ ?_⟩
  exact_mod_cast hc j

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule3


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.ConeSupport -/
section AbstractModule4



namespace OAI

/-!
# Independent generators for a finite conical combination

Every conical combination can be expressed using a linearly independent
subfamily of its original generators.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem exists_positive_relation (A : I → E) (s : Finset I)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ g : I → ℝ, (∑ i ∈ s, g i • A i) = 0 ∧ ∃ i ∈ s, 0 < g i := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ :=
    (not_linearIndepOn_finset_iff (R := ℝ) (v := A)).mp h
  rcases lt_or_gt_of_ne hgi with hneg | hpos
  · refine ⟨fun j ↦ -g j, ?_, i, hi, neg_pos.mpr hneg⟩
    simp_rw [neg_smul, Finset.sum_neg_distrib, hg, neg_zero]
  · exact ⟨g, hg, i, hi, hpos⟩

private theorem exists_nonneg_representation_erase [DecidableEq I] (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ i ∈ s, ∃ v : I → ℝ, (∀ j ∈ s.erase i, 0 ≤ v j) ∧
      (∑ j ∈ s.erase i, v j • A j) = ∑ j ∈ s, w j • A j := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ := exists_positive_relation A s h
  let p := s.filter fun i ↦ 0 < g i
  obtain ⟨i₀, hi₀, hmin⟩ :
      ∃ i₀ ∈ p, ∀ j ∈ p, w i₀ / g i₀ ≤ w j / g j := by
    apply p.exists_min_image
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have hgi₀ : 0 < g i₀ := (Finset.mem_filter.mp hi₀).2
  let v : I → ℝ := fun j ↦ w j - w i₀ / g i₀ * g j
  have hvi₀ : v i₀ = 0 := by simp [v, ne_of_gt hgi₀]
  refine ⟨i₀, hi₀s, v, ?_, ?_⟩
  · intro j hj
    have hjs : j ∈ s := Finset.mem_of_mem_erase hj
    dsimp [v]
    apply sub_nonneg.mpr
    by_cases hjp : j ∈ p
    · have hgj : 0 < g j := (Finset.mem_filter.mp hjp).2
      exact (le_div_iff₀ hgj).mp (hmin j hjp)
    · have hgj : g j ≤ 0 := by
        simpa only [p, Finset.mem_filter, hjs, true_and, not_lt] using hjp
      exact (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hw i₀ hi₀s) hgi₀.le) hgj).trans (hw j hjs)
  · calc
      (∑ j ∈ s.erase i₀, v j • A j) = ∑ j ∈ s, v j • A j := by
        apply Finset.sum_erase
        rw [hvi₀, zero_smul]
      _ = ∑ j ∈ s, w j • A j := by
        simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib,
          ← Finset.smul_sum, hg, smul_zero, sub_zero]

/-- A nonnegative finite combination uses a linearly independent subfamily
after possibly changing its coefficients. -/
theorem exists_nonneg_representation_linearIndependent (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ t : Finset I, t ⊆ s ∧ LinearIndependent ℝ (fun i : t ↦ A i) ∧
      ∃ v : I → ℝ, (∀ i ∈ t, 0 ≤ v i) ∧
        (∑ i ∈ t, v i • A i) = ∑ i ∈ s, w i • A i := by
  classical
  induction s using Finset.strongInductionOn generalizing w with
  | _ s ih =>
    by_cases hs : LinearIndependent ℝ (fun i : s ↦ A i)
    · exact ⟨s, Finset.Subset.refl _, hs, w, hw, rfl⟩
    · obtain ⟨i, hi, v, hv, heq⟩ := exists_nonneg_representation_erase A s w hw hs
      obtain ⟨t, hts, ht, z, hz, hzeq⟩ := ih (s.erase i) (Finset.erase_ssubset hi) v hv
      exact ⟨t, hts.trans (Finset.erase_subset _ _), ht, z, hz, hzeq.trans heq⟩

/-- Every element of a finitely generated cone belongs to the cone generated
by some linearly independent subfamily of the given generators. -/
theorem exists_linearIndependent_subcone [Fintype I] (A : I → E) {x : E}
    (hx : x ∈ PointedCone.span ℝ (Set.range A)) :
    ∃ s : Finset I, LinearIndependent ℝ (fun i : s ↦ A i) ∧
      x ∈ PointedCone.span ℝ (Set.range (fun i : s ↦ A i)) := by
  classical
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ({x : ℝ // 0 ≤ x})).mp hx
  obtain ⟨s, _, hs, v, hv, heq⟩ :=
    exists_nonneg_representation_linearIndependent A Finset.univ
      (fun i ↦ (w i : ℝ)) (fun i _ ↦ (w i).property)
  refine ⟨s, hs, ?_⟩
  have hsum : (∑ i ∈ s, v i • A i) = x := by
    exact heq.trans (by simpa only [← Nonneg.coe_smul] using hw)
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  exact PointedCone.smul_mem _ (hv i hi)
    (PointedCone.subset_span ⟨⟨i, hi⟩, rfl⟩)

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule4


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FiniteConeClosed -/
section AbstractModule5




namespace OAI

/-!
# Closed finitely generated cones
-/

open Topology

namespace MatrixMultiplication.AuxiliarySeparation

/-- A finite conic combination is a sum with nonnegative coefficients. -/
theorem mem_pointedCone_hull_range_iff {I E : Type*} [Fintype I]
    [AddCommGroup E] [Module ℝ E] (A : I → E) (x : E) :
    x ∈ PointedCone.span ℝ (Set.range A) ↔
      ∃ c : I → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • A i = x := by
  rw [PointedCone.span, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i ↦ (c i : ℝ), fun i ↦ (c i).2, hc⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨fun i ↦ ⟨c i, hc i⟩, hcx⟩

/-- The cone spanned by a finite linearly independent family is closed. -/
theorem isClosed_pointedCone_hull_range_of_linearIndependent
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : I → E) (hA : LinearIndependent ℝ A) :
    IsClosed (PointedCone.span ℝ (Set.range A) : Set E) := by
  let f := Fintype.linearCombination ℝ A
  have hf : IsClosedEmbedding f :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hA.fintypeLinearCombination_injective)
  have hnonneg : IsClosed {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter fun i ↦ isClosed_le (continuous_const : Continuous fun _ : I → ℝ ↦ (0 : ℝ)) (continuous_apply i)
  have heq : (PointedCone.span ℝ (Set.range A) : Set E) =
      f '' {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    ext x
    change x ∈ PointedCone.span ℝ (Set.range A) ↔ _
    rw [mem_pointedCone_hull_range_iff]
    simp only [Set.mem_image, Set.mem_setOf_eq]
    rfl
  rw [heq]
  exact hf.isClosedMap _ hnonneg

/-- A cone generated by a finite family of real vectors is closed. -/
theorem isClosed_pointedCone_hull_range
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : I → E) :
    IsClosed (PointedCone.span ℝ (Set.range A) : Set E) := by
  classical
  let S := {s : Finset I // LinearIndependent ℝ (fun i : s ↦ A i)}
  have heq : (PointedCone.span ℝ (Set.range A) : Set E) =
      ⋃ s : S, (PointedCone.span ℝ (Set.range (fun i : s.1 ↦ A i)) : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hx⟩ := exists_linearIndependent_subcone A hx
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
    · intro hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      apply Submodule.span_mono _ hs
      rintro _ ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
  rw [heq]
  exact isClosed_iUnion_of_finite fun s : S ↦
    isClosed_pointedCone_hull_range_of_linearIndependent _ s.2

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule5


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.Farkas -/
section AbstractModule6



namespace OAI

/-!
# Finite rational cone duality

A finite family of integral vectors admits a normalized nonnegative linear
functional whenever the negative normalizing vector has no positive integral
multiple in the monoid generated by the family.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Closed-cone separation followed by rational certificate extraction yields
a normalized nonnegative linear functional. -/
theorem exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hclosed : IsClosed (PointedCone.span ℝ
      (Set.range (fun i j ↦ (A i j : ℝ))) : Set (J → ℝ)))
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) := by
  classical
  let C : ProperCone ℝ (J → ℝ) :=
    { toSubmodule := PointedCone.span ℝ (Set.range (fun i j ↦ (A i j : ℝ)))
      isClosed' := hclosed }
  have houtside : -(fun j ↦ (u j : ℝ)) ∉ C := by
    intro hmem
    obtain ⟨x, hx⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ({x : ℝ // 0 ≤ x})).1 hmem
    have hreal : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
        ∀ j, ∑ i, x i * (A i j : ℝ) = ((-u j : ℤ) : ℝ) := by
      refine ⟨fun i ↦ (x i : ℝ), fun i ↦ (x i).property, fun j ↦ ?_⟩
      have hj := congrFun hx j
      simpa only [Finset.sum_apply, Pi.smul_apply, ← Nonneg.coe_smul,
        smul_eq_mul, Pi.neg_apply, Int.cast_neg] using hj
    obtain ⟨D, hD, c, hc⟩ :=
      exists_nat_scaled_int_solution_of_nonneg_real A (fun j ↦ -u j) hreal
    exact hno ⟨D, hD, c, fun j ↦ by simpa only [mul_neg, neg_mul] using hc j⟩
  obtain ⟨f, hf, hfu⟩ := C.hyperplane_separation_point houtside
  have hpos : 0 < f (fun j ↦ (u j : ℝ)) := by
    simpa only [map_neg, neg_neg, neg_lt_zero] using hfu
  refine ⟨(f (fun j ↦ (u j : ℝ)))⁻¹ • f.toLinearMap, ?_, fun i ↦ ?_⟩
  · simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    exact inv_mul_cancel₀ hpos.ne'
  · change 0 ≤ (f (fun j ↦ (u j : ℝ)))⁻¹ * f (fun j ↦ (A i j : ℝ))
    exact mul_nonneg (inv_nonneg.mpr hpos.le)
      (hf _ (PointedCone.subset_span (Set.mem_range_self i)))

/-- A finite integral cone either contains a positive integer multiple of the
negative normalizing vector, or admits a linear functional which is
nonnegative on the generators and takes value one on that vector. -/
theorem exists_normalized_nonneg_linear_of_no_nat_certificate
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) :=
  exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed A u
    (isClosed_pointedCone_hull_range _) hno

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule6


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Catalyst -/
section AbstractModule7


namespace OAI

/-!
# Catalysts from additive completion certificates

Equality in the Grothendieck additive group means equality after adding a
common element of the original semiring. This gives catalytic inequalities
without assuming additive cancellation.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Algebra

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- A negative-unit certificate in the additive completion gives a catalytic
inequality in the original semiring, even when its addition is not cancellative. -/
theorem exists_catalyst_of_completion_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    (m k : ℕ) (d X Y s : S) (hXY : X ≤ Y)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      GrothendieckAddGroup.of Y - GrothendieckAddGroup.of X +
        GrothendieckAddGroup.of (d * s) - k • GrothendieckAddGroup.of s) :
    ∃ D : S, D + (m : S) + d * s ≤ D + (k : S) * s := by
  let η : S →+ GrothendieckAddGroup S := GrothendieckAddGroup.of
  have hm : η (m : S) = m • η 1 := by
    rw [← nsmul_one m, map_nsmul]
  have hk : η ((k : S) * s) = k • η s := by
    rw [← nsmul_eq_mul, map_nsmul]
  have heq' : η ((m : S) + Y + d * s) = η (X + (k : S) * s) := by
    simp only [map_add, hm, hk]
    change -(m : ℤ) • η 1 = η Y - η X + η (d * s) - k • η s at heq
    simp only [neg_zsmul, natCast_zsmul] at heq
    calc
      m • η 1 + η Y + η (d * s) =
          m • η 1 + (η Y - η X + η (d * s) - k • η s) + η X + k • η s := by abel
      _ = m • η 1 + -(m • η 1) + η X + k • η s := by rw [← heq]
      _ = η X + k • η s := by abel
  obtain ⟨C, hC⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid S)).exists_of_eq heq'
  refine ⟨(C : S) + Y, ?_⟩
  calc
    ((C : S) + Y) + (m : S) + d * s = (C : S) + ((m : S) + Y + d * s) := by simp only [add_assoc, add_comm, add_left_comm]
    _ = (C : S) + (X + (k : S) * s) := hC
    _ ≤ (C : S) + (Y + (k : S) * s) :=
      hadd _ _ _ _ le_rfl (hadd _ _ _ _ hXY le_rfl)
    _ = ((C : S) + Y) + (k : S) * s := by ac_rfl

/-- A finite nonnegative integral combination of completion relations gives
one catalytic inequality. The catalyst absorbs the aggregate of the ordered
relations, and the resulting test element is the same combination of the
original test elements. -/
theorem exists_catalyst_of_completion_sum_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    {I : Type*} [Fintype I] (m k : ℕ) (d : S)
    (n : I → ℕ) (X Y Z : I → S) (hXY : ∀ i, X i ≤ Y i)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      ∑ i, n i • (GrothendieckAddGroup.of (Y i) - GrothendieckAddGroup.of (X i) +
        GrothendieckAddGroup.of (d * Z i) - k • GrothendieckAddGroup.of (Z i))) :
    ∃ D : S, D + (m : S) + d * (∑ i, n i • Z i) ≤
      D + (k : S) * (∑ i, n i • Z i) := by
  classical
  have hnsmul (a b : S) (hab : a ≤ b) (l : ℕ) : l • a ≤ l • b := by
    induction l with
    | zero => simp
    | succ l ih => simpa only [succ_nsmul] using hadd _ _ _ _ ih hab
  have hsum (t : Finset I) : ∑ i ∈ t, n i • X i ≤ ∑ i ∈ t, n i • Y i := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simpa only [Finset.sum_insert hi] using
        hadd _ _ _ _ (hnsmul (X i) (Y i) (hXY i) (n i)) ih
  apply exists_catalyst_of_completion_eq hadd m k d
    (∑ i, n i • X i) (∑ i, n i • Y i) (∑ i, n i • Z i) (hsum Finset.univ)
  convert heq using 1
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    map_sum, map_nsmul, Finset.mul_sum, mul_smul_comm, ← smul_comm k]
  rw [Finset.smul_sum]

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule7


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Coordinates -/
section AbstractModule8


namespace OAI

/-!
# Extending a finite coordinate functional

A linear functional on a finite coordinate set determines a state on the
whole index type by evaluating coordinate indicators. Its value on any
finitely supported integral vector depends only on those finite coordinates.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

/-- Extend a functional on a finite coordinate set by zero outside that set. -/
def finiteCoordinateState {S : Type*} (H : Finset S)
    (L : (H → ℝ) →ₗ[ℝ] ℝ) (x : S) : ℝ := by
  classical
  exact L (fun j : H ↦ if (j : S) = x then 1 else 0)

@[simp] theorem finiteCoordinateState_eq_zero_of_not_mem {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) {x : S} (hx : x ∉ H) :
    finiteCoordinateState H L x = 0 := by
  classical
  unfold finiteCoordinateState
  have hz : (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) = 0 := by
    funext j
    simp only [Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun h ↦ hx (h ▸ j.property)
  rw [hz, map_zero]

/-- Evaluating a finitely supported integral vector against the extended
state agrees with restricting its coordinates and applying the functional. -/
theorem linearCombination_finiteCoordinateState {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) (v : S →₀ ℤ) :
    Finsupp.linearCombination ℤ (finiteCoordinateState H L) v =
      L (fun j : H ↦ (v j : ℝ)) := by
  classical
  induction v using Finsupp.induction with
  | zero =>
    simp only [map_zero, Finsupp.zero_apply, Int.cast_zero]
    exact (L.map_zero).symm
  | single_add x n v _ _ ih =>
    rw [map_add, Finsupp.linearCombination_single, ih]
    have hsingle :
        (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) =
          n • (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) := by
      funext j
      by_cases hj : (j : S) = x
      · simp [hj]
      · simp [hj]
    have hadd :
        (fun j : H ↦ ((Finsupp.single x n + v) j : ℝ)) =
          (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) +
            (fun j : H ↦ (v j : ℝ)) := by
      funext j
      simp
    rw [hadd, map_add, hsingle, map_zsmul]
    rfl

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end AbstractModule8


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.StateObstruction -/
section AbstractModule9







namespace OAI

/-!+# Finite obstructions to normalized additive states

The state equations are homogeneous integer inequalities, except for the
normalization at the unit. Their finite certificates are interpreted in the
additive group completion, preserving catalysts in the original semiring.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- The homogeneous inequalities defining a normalized additive state. Both
signs of the additive relation are included. -/
inductive StateConstraint (S : Type*) [Preorder S] where
  | lower (x : S)
  | upper (x : S)
  | addPos (x y : S)
  | addNeg (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detector (x : S)

/-- Integer coefficient vector of a homogeneous state constraint. -/
def stateConstraintVector (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) : S →₀ ℤ := by
  classical
  exact match c with
  | .lower x => Finsupp.single x 1
  | .upper x => Finsupp.single (1 : S) (R x : ℤ) - Finsupp.single x 1
  | .addPos x y => Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1
  | .addNeg x y => -(Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1)
  | .order x y _ => Finsupp.single y 1 - Finsupp.single x 1
  | .detector x => Finsupp.single (d * x) 1 - Finsupp.single x (k : ℤ)

/-- Evaluation of a finite integer coefficient vector on a real-valued function. -/
def statePairing (f : S → ℝ) : (S →₀ ℤ) →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ f

omit [CommSemiring S] [Preorder S] in
theorem statePairing_apply (f : S → ℝ) (v : S →₀ ℤ) :
    statePairing f v = ∑ x ∈ v.support, (v x : ℝ) * f x := by
  simp [statePairing, Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul]

omit [CommSemiring S] [Preorder S] in
@[simp] theorem statePairing_single (f : S → ℝ) (x : S) (n : ℤ) :
    statePairing f (Finsupp.single x n) = (n : ℝ) * f x := by
  simp [statePairing, zsmul_eq_mul]

omit [CommSemiring S] [Preorder S] in
theorem continuous_statePairing (v : S →₀ ℤ) :
    Continuous (fun f : S → ℝ ↦ statePairing f v) := by
  simp only [statePairing_apply]
  exact continuous_finset_sum _ fun x _ ↦ continuous_const.mul (continuous_apply x)

theorem normalizedStates_iff_stateConstraint (R : S → ℕ) (d : S) (k : ℕ)
    (f : S → ℝ) :
    f ∈ normalizedStates (fun x ↦ (R x : ℝ)) d k ↔
      f 1 = 1 ∧ ∀ c : StateConstraint S, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  constructor
  · intro hf
    refine ⟨hf.2.1, ?_⟩
    intro c
    cases c with
    | lower x => simpa [stateConstraintVector] using (hf.1 x).1
    | upper x =>
      simp only [stateConstraintVector, map_sub, statePairing_single, Int.cast_natCast,
        Int.cast_one, one_mul, hf.2.1, mul_one, sub_nonneg]
      exact (hf.1 x).2
    | addPos x y => simp [stateConstraintVector, hf.2.2.1]
    | addNeg x y => simp [stateConstraintVector, hf.2.2.1]
    | order x y h => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.1 x y h
    | detector x => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.2 x
  · rintro ⟨hn, hc⟩
    refine ⟨?_, hn, ?_, ?_, ?_⟩
    · intro x
      constructor
      · simpa [stateConstraintVector] using hc (.lower x)
      · simpa [stateConstraintVector, hn, sub_nonneg] using hc (.upper x)
    · intro x y
      have hp := hc (.addPos x y)
      have hm := hc (.addNeg x y)
      simp [stateConstraintVector] at hp hm
      linarith
    · intro x y hxy
      simpa [stateConstraintVector, sub_nonneg] using hc (.order x y hxy)
    · intro x
      simpa [stateConstraintVector, sub_nonneg] using hc (.detector x)

/-- The ordinary monotonicity difference in a state constraint. -/
def stateConstraintLower (c : StateConstraint S) : S :=
  match c with
  | .lower _ => 0
  | .upper x => x
  | .order x _ _ => x
  | _ => 0

def stateConstraintUpper (R : S → ℕ) (c : StateConstraint S) : S :=
  match c with
  | .lower x => x
  | .upper x => R x
  | .order _ y _ => y
  | _ => 0

/-- The multiplier of the distinguished detector difference. -/
def stateConstraintDetector (c : StateConstraint S) : S :=
  match c with
  | .detector x => x
  | _ => 0

theorem stateConstraintLower_le_upper (R : S → ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (c : StateConstraint S) :
    stateConstraintLower c ≤ stateConstraintUpper R c := by
  cases c with
  | lower x => exact hzero x
  | upper x => exact hbound x
  | order _ _ h => exact h
  | addPos _ _ => exact le_rfl
  | addNeg _ _ => exact le_rfl
  | detector _ => exact le_rfl

/-- Interpreting a constraint in the group completion separates its ordinary
order difference from its detector difference. -/
theorem stateConstraintVector_completion (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) :
    Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))
        (stateConstraintVector R d k c) =
      Algebra.GrothendieckAddGroup.of (stateConstraintUpper R c) -
        Algebra.GrothendieckAddGroup.of (stateConstraintLower c) +
      Algebra.GrothendieckAddGroup.of (d * stateConstraintDetector c) -
        k • Algebra.GrothendieckAddGroup.of (stateConstraintDetector c) := by
  classical
  have hcast (n : ℕ) : Algebra.GrothendieckAddGroup.of (n : S) =
      n • Algebra.GrothendieckAddGroup.of (1 : S) := by
    rw [← nsmul_one, map_nsmul]
  cases c <;>
    simp [stateConstraintVector, stateConstraintLower, stateConstraintUpper,
      stateConstraintDetector, hcast, Nat.cast_smul_eq_nsmul, map_add] <;> abel

/-- In the absence of a catalytic obstruction, no positive multiple of the
negative unit is a natural combination of state-constraint vectors. -/
theorem no_stateConstraint_certificate (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) :
    ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∑ i, n i • stateConstraintVector R d k (cs i) =
        -(m : ℤ) • Finsupp.single (1 : S) (1 : ℤ) := by
  classical
  rintro ⟨m, hm, n, hn⟩
  have heq := congrArg
    (Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))) hn
  simp only [map_sum, map_nsmul, map_smul, Finsupp.linearCombination_single,
    one_smul, stateConstraintVector_completion] at heq
  obtain ⟨D, hD⟩ := exists_catalyst_of_completion_sum_eq hadd m k d n
    (fun i ↦ stateConstraintLower (cs i)) (fun i ↦ stateConstraintUpper R (cs i))
    (fun i ↦ stateConstraintDetector (cs i))
    (fun i ↦ stateConstraintLower_le_upper R hzero hbound (cs i)) heq.symm
  exact hno D _ m hm hD

/-- Every finite family of constraints supported on `H` has a normalized
oai_arithmetic_solution that vanishes outside `H`, provided no positive catalyst exists. -/
theorem finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) (H : Finset S) (hOne : (1 : S) ∈ H)
    (hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H) :
    ∃ f : S → ℝ, f 1 = 1 ∧
      (∀ i, 0 ≤ statePairing f (stateConstraintVector R d k (cs i))) ∧
      ∀ x ∉ H, f x = 0 := by
  classical
  let A : I → H → ℤ := fun i j ↦ stateConstraintVector R d k (cs i) j
  let u : H → ℤ := fun j ↦ (Finsupp.single (1 : S) (1 : ℤ)) j
  have hcert : ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∀ j, ∑ i, (n i : ℤ) * A i j = -(m : ℤ) * u j := by
    rintro ⟨m, hm, n, hn⟩
    apply no_stateConstraint_certificate R d k hzero hbound hadd hno cs
    refine ⟨m, hm, n, ?_⟩
    ext x
    by_cases hx : x ∈ H
    · have heq := hn ⟨x, hx⟩
      by_cases hx1 : (1 : S) = x <;>
        simpa [A, u, Finsupp.coe_finset_sum, Finset.sum_apply,
          Finsupp.smul_apply, nsmul_eq_mul, zsmul_eq_mul, Finsupp.single_apply, hx1] using heq
    · have hz : ∀ i, stateConstraintVector R d k (cs i) x = 0 := by
        intro i
        apply Finsupp.notMem_support_iff.mp
        exact fun h ↦ hx (hH i h)
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        hz, smul_zero, Finset.sum_const_zero]
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hx hOne
      simp [hx1]
  obtain ⟨L, hLu, hLA⟩ :=
    exists_normalized_nonneg_linear_of_no_nat_certificate A u hcert
  let f := finiteCoordinateState H L
  refine ⟨f, ?_, ?_, ?_⟩
  · have heq := linearCombination_finiteCoordinateState H L
      (Finsupp.single (1 : S) (1 : ℤ))
    simpa [f, u] using heq.trans hLu
  · intro i
    simpa only [statePairing, f, linearCombination_finiteCoordinateState, A] using hLA i
  · intro x hx
    exact finiteCoordinateState_eq_zero_of_not_mem H L hx

/-- A finite collection of state constraints can be solved while keeping all
coordinates in their rank intervals. -/
theorem bounded_finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    (F : Finset (StateConstraint S)) :
    ∃ f : S → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
      ∀ c ∈ F, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  let H : Finset S := insert 1 (F.biUnion fun c ↦ (stateConstraintVector R d k c).support)
  have hOne : (1 : S) ∈ H := Finset.mem_insert_self _ _
  let cs : F ⊕ (Bool × H) → StateConstraint S
    | .inl c => c
    | .inr (false, x) => .lower x
    | .inr (true, x) => .upper x
  have hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H := by
    intro i a ha
    cases i with
    | inl c =>
      exact Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨c, c.property, ha⟩)
    | inr i =>
      rcases i with ⟨tag, x⟩
      by_contra hnot
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hnot hOne
      have hax : a ≠ (x : S) := by
        rintro rfl
        exact hnot x.property
      have ha0 := Finsupp.mem_support_iff.mp ha
      cases tag <;>
        simp [cs, stateConstraintVector, ha1, hax] at ha0
  obtain ⟨f, hf1, hfc, hfzero⟩ :=
    finite_stateConstraint_solution R d k hzero hbound hadd hno cs H hOne hH
  refine ⟨f, ?_, hf1, ?_⟩
  · intro x
    by_cases hx : x ∈ H
    · have hlo := hfc (.inr (false, ⟨x, hx⟩))
      have hhi := hfc (.inr (true, ⟨x, hx⟩))
      constructor
      · simpa [cs, stateConstraintVector] using hlo
      · simpa [cs, stateConstraintVector, hf1, sub_nonneg] using hhi
    · rw [hfzero x hx]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
  · intro c hc
    exact hfc (.inl ⟨c, hc⟩)

/-- Absence of positive scalar-gain catalysts guarantees the existence of a
normalized additive monotone state satisfying the detector inequality. -/
theorem normalizedStates_nonempty_of_no_catalyst (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s) :
    (normalizedStates (fun x ↦ (R x : ℝ)) d k).Nonempty := by
  let B : Set (S → ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R x}
  let K : Set (S → ℝ) := B ∩ {f | f 1 = 1}
  let t : StateConstraint S → Set (S → ℝ) :=
    fun c ↦ {f | 0 ≤ statePairing f (stateConstraintVector R d k c)}
  have hBcompact : IsCompact B :=
    isCompact_pi_infinite (fun x ↦ isCompact_Icc (a := (0 : ℝ)) (b := (R x : ℝ)))
  have hKcompact : IsCompact K :=
    hBcompact.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have htclosed : ∀ c, IsClosed (t c) := fun c ↦
    isClosed_le continuous_const (continuous_statePairing (stateConstraintVector R d k c))
  have hfinite : ∀ F : Finset (StateConstraint S), (K ∩ ⋂ c ∈ F, t c).Nonempty := by
    intro F
    obtain ⟨f, hfb, hf1, hfc⟩ :=
      bounded_finite_stateConstraint_solution R d k hzero hbound hadd hno F
    refine ⟨f, ⟨hfb, hf1⟩, ?_⟩
    simp only [Set.mem_iInter]
    exact hfc
  obtain ⟨f, hfK, hft⟩ := hKcompact.inter_iInter_nonempty t htclosed hfinite
  refine ⟨f, (normalizedStates_iff_stateConstraint R d k f).mpr ?_⟩
  exact ⟨hfK.2, fun c ↦ Set.mem_iInter.mp hft c⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end AbstractModule9


/- BEGIN FixedPointTheorems.cubical_sperner_prep -/
section AbstractModule10

/-!
# Cubical simplices and boundary incidence

The grid simplices of a labelled cube are classified by their boundary coordinates.
Coordinate-change counts order their vertices and determine the number of parent simplices,
providing the incidence identities used in the cubical Sperner argument.
-/


open Classical

structure SpernerCube where
  n : ℕ
  p : ℕ
  RL : (Fin n → Fin (p+1)) → ℕ
  rl_proper : ∀ (I: Fin n → Fin (p+1) ), RL I ≤ n ∧
      ∀ (k : Fin n), (I k = 0 → RL I ≠ k.1) ∧ (I k = p → RL I ≤ k.1)

namespace SpernerCube

def G (SC : SpernerCube) := Fin SC.n → Fin (SC.p+1)

instance Gfin (SC : SpernerCube): Fintype SC.G := by {
  exact Pi.instFintype
}

end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}

def simplex (m:ℕ ) (I : Fin (m+1)→ SC.G) := Function.Injective I
    ∧ ∀ i < m, ∀ j : Fin SC.n, (I (Fin.ofNat _ i) j).1 ≤ (I (Fin.ofNat _ (i+1)) j).1
    ∧ (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1

def complete_simplex (m:ℕ ) (I : Fin (m+1) → SC.G ) := simplex SC m I
    ∧ Set.range (fun (i:Fin (m+1))↦ SC.RL (I i)) = {j : ℕ | j ≤ m}

def is_face I J :=
    simplex SC n1 I ∧ simplex SC SC.n J ∧ Set.range I ⊆ Set.range J

def is_boundary_face I := ∃! J, @is_face SC n1 I J

def complete_boundary_face I := is_boundary_face SC I ∧ complete_simplex SC n1 I

def case_A (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = 0

def case_B (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = Fin.last SC.p

def case_C (I : Fin (n1 +1) → SC.G) :=
    ∃ j, ∃ (q : Fin (SC.p + 1)), (q ≠ 0 ∧ q ≠ Fin.last SC.p ) ∧ ∀ k, I k j = q

def case_D (I : Fin (n1 +1) → SC.G) := ∀ j, ∀ q, ∃ k,I k j ≠ q

lemma one_of_ABCD (I : Fin (n1 +1) → SC.G) :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by {
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  {
    apply Or.inl
    use j
    rwa [← q0]
  }
  by_cases qp : q = Fin.last SC.p
  {
    apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  }
  suffices h3 : case_C SC I by {
    simp only [h3, true_or, or_true]
  }
  use j, q
}

section simplex_properties

lemma monotone_1_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
    (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by {
  intro j
  let f := fun i ↦ I i j
  have h2 := @Fin.monotone_iff_le_succ m _ _ f
  suffices h3 : Monotone f by exact (h3 h1)
  rw [h2]
  clear i1 i2 h1
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp only [Fin.val_fin_le] at h3
  convert h3 <;> ext <;> simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt]
}

lemma monotone_2_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1)) :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j := by {
  apply Iff.intro
  {
    intro h1 j
    apply monotone_1_of_simplex _ I hs i1 i2 h1
  }
  {
    intro h1
    by_contra h2
    have h3 : i1 ≠ i2 := ne_of_not_le h2
    apply h3
    apply hs.1
    apply funext
    intro j
    apply le_antisymm (h1 j)
    apply monotone_1_of_simplex _ _ hs i2 i1 (le_of_not_ge h2)
  }
}

lemma last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by {
  cases m
  simp only [Fin.last_zero, Fin.isValue, le_add_iff_nonneg_right, zero_le]
  rename_i m
  have h3 : 0 < m + 1 := by omega
  exact (hs.2 0 h3 j).2
}

lemma le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by {
  have h1 := last_of_simplex SC I hs j
  apply le_trans _ (le_trans h1 _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  apply Nat.add_le_add_right
  apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2)
}

end simplex_properties

lemma p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by {
  simp only [ne_eq, Fin.last_eq_zero_iff]
  intro h1
  let v : Fin SC.n → Fin (SC.p + 1) := fun _ ↦ 0
  have h3 : NeZero SC.n := by {
    rw [←hn1]
    exact instNeZeroNatHAdd_1
  }
  have h4 : v 0 = 0 := by {rfl}
  have h2 := (SC.rl_proper v).2 0
  simp only [Fin.val_zero, ne_eq, h1, Fin.val_eq_zero_iff, nonpos_iff_eq_zero] at h2
  exact h2.1 h4 (h2.2 h4)
}

section simplex_child

def insert_index (j : Fin (SC.n+1)) (a: Fin (n1 +1 )) : Fin (SC.n+1) :=
{ val := if a.val < j.val then a.val else a.val+1,
  isLt := by {
    by_cases hlt : a.val < j.val
    {
      simp only [hlt, ↓reduceIte]
      exact Nat.lt_trans hlt j.2
    }
    {
      simp only [hlt, ↓reduceIte, add_lt_add_iff_right]
      rw [← hn1]
      exact a.2
    }
} }

def delete_vertex (j: Fin (SC.n+1)) (I : Fin (SC.n+1)→ SC.G) : Fin (n1 + 1) → SC.G :=
  fun a ↦ I (@insert_index SC n1 hn1 j a)

lemma insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by {
  apply Fin.ne_of_val_ne
  unfold insert_index
  by_cases hlt : a.val < j.val
  {
    simp only [hlt, ↓reduceIte]
    omega
  }
  {
    simp only [hlt, ↓reduceIte, ne_eq]
    omega
  }
}

lemma almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k := by {
  unfold insert_index
  by_cases hlt : a.1 < j.1
  {
    use (Fin.ofNat _ a.1)
    have h2 : a.1 = (Fin.ofNat (n1 + 1) a.1) := by {
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt]
      rw [hn1]
      apply lt_of_lt_of_le hlt
      exact Fin.is_le j
    }
    simp only [← h2, hlt]
    rfl
  }
  {
    have h2 : j.1 < a.1 := by {
      have := Fin.val_ne_of_ne (id (Ne.symm h))
      omega
    }
    let a1 := a.1 - 1
    have h3 : a1 + 1 = a.1 := by {
      show a.1 - 1 + 1 = a.1
      omega
    }
    let a1f := Fin.ofNat (n1 + 1) a1
    use a1f
    ext
    have h4 : a1 < n1 +1 := by {
      have h5 := a.2
      show a.1 - 1 < n1 + 1
      omega
    }
    have h6 : a1f.1 = a1 := by {
      unfold a1f
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact h4
    }
    have h5 : ¬ (a1f < j.1) := by {
      simp only [not_lt, h6]
      show j.1 ≤ a.1 - 1
      omega
    }
    simp only [h5, ↓reduceIte]
    rw [← h3, h6]
  }
}

lemma insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by {
  intro a b h1
  have h2 : a.1 < b.1 := by {exact h1}
  have h21 : a.1 < b.1 + 1 := by omega
  unfold insert_index
  by_cases h3 : a.1 < j.1
  {
    by_cases h4 : b.1 < j.1
    repeat {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
      assumption
    }
  }
  {
    by_cases h4 : b.1 < j.1
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
  }
}

lemma insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by {
  apply StrictMono.injective
  apply insert_index_strict_mono
}

lemma delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by {
  by_contra h2
  obtain ⟨k, h3 ⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  apply @insert_index_ne SC n1 hn1 i1 k
  apply hs.1
  nth_rewrite 2 [h3]
  exact (congrFun h1) k
}

lemma delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) := by {
  apply And.intro
  {
    intro k1 k2 h2
    apply insert_index_inj SC i
    apply hs.1 h2
  }
  {
    intro i2 hi2 j
    unfold delete_vertex
    apply And.intro
    {
      apply monotone_1_of_simplex SC J hs
      rw [StrictMono.le_iff_le]
      {
        simp only [Fin.ofNat_eq_cast]
        apply Fin.natCast_mono hi2
        exact Nat.le_add_right i2 1
      }
      apply insert_index_strict_mono
    }
    apply le_add_one_of_simplex SC J hs
  }
}

lemma delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J := by {
  apply And.intro
  {
    apply delete_vertex_simplex
    exact hs
  }
  {
    apply And.intro hs
    intro c hc
    obtain ⟨ i2, hi2 ⟩ := hc
    use @insert_index SC n1 hn1 i i2
    exact hi2
  }
}

lemma is_id_of_strict_mono (m: ℕ ) (f : Fin m → Fin m) (hsm : StrictMono f)
    : ∀ k, f k = k := by {
  suffices h1 : ∀ (a : ℕ), ∀ k, k.1 < a → f k = k by {
    intro k
    exact h1 m k k.2
  }
  intro a
  induction' a with a ha
  {
    intro k h1
    omega
  }
  {
    have h1 : Function.Injective f := by {exact StrictMono.injective hsm}
    have h2 : Function.Surjective f := Finite.surjective_of_injective h1
    intro k hk
    have h3 j : j < k → f j = j := by {
      intro hj
      apply ha
      omega
    }
    by_cases h4 : f k < k
    apply h1 (h3 (f k) h4)
    simp only [not_lt] at h4
    apply le_antisymm _ h4
    obtain ⟨l, h9⟩ := h2 k
    suffices h8 : k ≤ l by {rwa [← hsm.le_iff_le, h9] at h8}
    by_contra! h6
    have h7 := h3 l h6
    rw [h9] at h7
    rw [h7] at h6
    exact (lt_self_iff_false l).mp h6
  }
}

lemma is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by {
  have h31 : Function.Injective f := by {exact hsm.injective}
  have hns : ∃ j, ∀ i, f i ≠ j := by {
    by_contra! h1
    have h2 : Function.Surjective f := by {exact h1 }
    have h5 : Function.Bijective f :=  And.intro h31 h2
    have h4 := Nat.card_eq_of_bijective f h5
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_right_cancel_iff] at h4
    rw [h4] at hn1
    simp only [Nat.add_eq_left, one_ne_zero] at hn1
  }
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by {
    intro k1
    apply almost_surjective_of_insert_index
    exact hj k1
  }
  obtain ⟨g, hg⟩ := axiomOfChoice h1
  have h2 : StrictMono g := by {
    intro k1 k2
    contrapose!
    intro h4
    rw [←hsm.le_iff_le, hg k1, hg k2]
    have h5 := @insert_index_strict_mono SC n1 hn1 j
    rw [h5.le_iff_le]
    exact h4
  }
  have h3 := is_id_of_strict_mono _ g h2
  ext1 k
  rw [hg k, h3 k]
}

lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by {
  apply Iff.intro
  {
    intro h1
    have h2 : ∃ (f : Fin (n1+1) → Fin (SC.n+1)), ∀ k, I k = J (f k) := by {
      have h2 := h1.2.2
      have h3 : ∀ k, ∃ j, I k = J j := by {
        intro k
        have h4 : I k ∈ Set.range I := by {
          exact Set.mem_range_self k
        }
        have h3 := h2 h4
        obtain ⟨j, hj⟩ := h2 h4
        use j
        exact hj.symm
      }
      apply axiom_of_choice h3
    }
    obtain ⟨f, hf ⟩ := h2
    have h31 : Function.Injective f := by {
      intro k1 k2 h2
      apply h1.1.1
      rw [hf k1, hf k2, h2]
    }
    have h3 : StrictMono f := by {
      apply Monotone.strictMono_of_injective _ h31
      intro k1 k2 h2
      rw [monotone_2_of_simplex SC J hs]
      rw [← hf k1, ← hf k2]
      rwa [←monotone_2_of_simplex SC I h1.1]
    }
    obtain ⟨j, hj⟩ := is_insert_index_of_strict_mono SC f h3
    use j
    ext k
    unfold delete_vertex
    rw [hf k, hj]
  }
  {
    intro h1
    obtain ⟨ i, hi⟩ := h1
    rw [hi]
    apply @delete_vertex_is_face SC _ _ J hs
  }
}

end simplex_child

section cases_ABCD

lemma insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by {
  have h1 : ∀ j2, ∃ w, (j2 = j → w = v)
      ∧ ∀ i, @insert_index SC n1 hn1 j i = j2 → I i = w := by {
    intro j2
    by_cases h1 : j2 = j
    {
      use v
      simp only [implies_true, true_and]
      intro i
      have h3 : @insert_index SC n1 hn1 j i ≠ j := by {apply insert_index_ne}
      simp only [h1, h3, IsEmpty.forall_iff]
    }
    {
      have h3 : ∃ i, j2 = @insert_index SC n1 hn1 j i := by {
        apply almost_surjective_of_insert_index
        exact h1
      }
      obtain ⟨ i, hi⟩ := h3
      use (I i)
      simp only [h1, IsEmpty.forall_iff, true_and]
      intro i2 h2
      congr!
      apply insert_index_inj SC j
      rw [h2, hi]
    }
  }
  obtain ⟨J, h2⟩ := axiomOfChoice h1
  use J
  apply And.intro
  {
    ext i
    exact (h2 (@insert_index SC n1 hn1 j i)).2 i rfl
  }
  exact (h2 j).1 rfl
}

lemma surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by {
  unfold insert_index
  have h2 : i.1 < j.1 := by omega
  have h3 : (i+1).1 = i.1 + 1 := by {
    refine Fin.val_add_one_of_lt ?_
    simp only [Nat.succ_eq_add_one]
    show i.1 < n1
    have h6 := Fin.val_lt_last hj1
    omega
  }
  apply And.intro
  {
    simp only [h2, ↓reduceIte]
    exact hij
  }
  simp only [h3, hij, lt_self_iff_false, ↓reduceIte]
}

lemma parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by {
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3
    := by {apply almost_surjective_of_insert_index}
  intro j1 j2 h4
  have h7 j3 : J j3 = J j → j3 = j := by {
      intro h7
      by_contra h51
      apply h2
      obtain ⟨i3, hi3⟩ := h5 j3 h51
      use i3
      rw [←h7,h1,hi3]
      rfl
  }
  by_cases h8 : j1 = j
  {
    rw [h8, h7 j2]
    rw [←h8,h4]
  }
  by_cases h9 : j2 = j
  {
    rw [h9, h7 j1]
    rw [←h9,h4]
  }
  obtain ⟨i1, hi1⟩ := h5 j1 h8
  obtain ⟨i2, hi2⟩ := h5 j2 h9
  suffices h11 : i1 = i2 by {rw [hi1,hi2,h11] }
  apply hs.1
  rw [h1]
  unfold delete_vertex
  rw [← hi1,← hi2, h4]
}

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

lemma parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h4 : J j ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm _ (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  }
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by {
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by {
      simp only [Fin.ofNat_eq_cast, Fin.val_last]
      rw [Fin.val_cast_of_lt]
      exact h6
      rwa [←hn1] at h6
    }
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    exact Nat.lt_add_right 1 h6
  }
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  {
    rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    {
      rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    }
    have h16 : j1+1 = SC.n := by omega
    have h13 : Fin.ofNat _ j1 = Fin.last n1 := by {
      suffices h15 : j1 = n1 by {
        simp only [h15, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
      }
      omega
    }
    have h14 : Fin.ofNat _ (j1+1) = j := by {
      rw [hj]
      simp only [h16, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    }
    rw [h13,h14]
    exact (h3 k1).1
  }
  {
    have h7 : J 0 = I 0 := by {
      have h6 := h5 0 (Nat.zero_lt_of_lt hj1)
      simp only [Fin.ofNat_eq_cast] at h6
      exact h6
    }
    rw [h7,←hj]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3 := by {
    apply almost_surjective_of_insert_index
  }
  have h6 j3 : j3 ≠ j → ∃ i3, I i3 = J j3 := by {
    intro h7
    obtain ⟨i3, hi3⟩ := h5 j3 h7
    use i3
    rw [h1, hi3]
    rfl
  }
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  {
    simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
    rw [h1] at h5
    unfold delete_vertex at h5
    have h6 : (@insert_index SC n1 hn1 j i).1 + 1 = j := by {
      unfold insert_index
      have h7 : i.1 < j.1 := by omega
      simp only [h7, ↓reduceIte]
      exact hij
    }
    by_cases h8 : i2 = j.1
    {
      convert h5.2
      simp only [h8, Fin.cast_val_eq_self]
      have h11 : j ≠ Fin.last SC.n := by {
        suffices h12 : j.1 ≠ SC.n by exact Ne.symm (Fin.ne_of_val_ne (Ne.symm h12))
        rw [←h8]
        exact Nat.ne_of_lt h4
      }
      have h9 := @surround_index SC n1 hn1 j i hij h11
      rw [h8, h9.2]
      exact Fin.cast_val_eq_self (insert_index SC j (i + 1))
    }
    by_cases h9 : i2 + 1 = j.1
    {
      rw [←h9] at h6
      simp only [Nat.add_right_cancel_iff] at h6
      convert h5.1
      rw [←h6]
      simp only [Fin.cast_val_eq_self]
      rw [h9]
      simp only [Fin.cast_val_eq_self]
    }
    have h11 : ∃ i3, (Fin.ofNat _ i2) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h8
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      apply lt_trans h4 (lt_add_one SC.n)
    }
    have h12 : ∃ i3, (Fin.ofNat _ (i2+1)) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h9
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      omega
    }
    simp only [Fin.ofNat_eq_cast] at h11 h12
    obtain ⟨i3, hi3⟩ := h11
    obtain ⟨i4, hi4⟩ := h12
    rw [hi3, hi4]
    suffices h21 : I i3 k2 ≤ I i4 k2 by {rwa [h1] at h21}
    apply monotone_1_of_simplex SC I hs
    have h21 : StrictMono (@insert_index SC n1 hn1 j) := by {
      apply insert_index_strict_mono
    }
    rw [←h21.le_iff_le]
    rw [←hi3, ← hi4]
    refine (Fin.natCast_le_natCast ?_ h4).mpr ?_
    exact Nat.le_of_succ_le h4
    exact Nat.le_succ i2
  }
  {
    have h11 : (J (Fin.last SC.n) k2).1 ≤ (I (Fin.last n1) k2).1 := by {
      simp only [Fin.val_fin_le]
      by_cases h12 : Fin.last SC.n = j
      {
        rw [h12]
        apply le_trans h5.2
        apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
      }
      obtain ⟨ i3, hi3⟩ := h6 _ h12
      rw [←hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
    }
    have h13 := last_of_simplex SC I hs k2
    apply le_trans h11 (le_trans h13 _)
    simp only [add_le_add_iff_right, Fin.val_fin_le]
    by_cases h14 : 0 = j
    {
      rw [h14]
      apply le_trans _ h5.1
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
    {
      obtain ⟨i3, hi3⟩ := h6 _ h14
      rw [← hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
  }
}

noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}

lemma ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by {
  unfold coord_change_count
  rw [←Finset.card_union_of_disjoint]
  congr
  apply Finset.ext_iff.mpr
  intro k2
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [←Decidable.not_and_iff_not_or_not]
  apply Iff.intro
  {
    intro h3 h4
    apply h3
    rw [h4.1, h4.2]
  }
  {
    intro h2 h3
    apply h2
    have h4 := monotone_1_of_simplex SC I hs i1 i2 h1.1 k2
    have h5 := monotone_1_of_simplex SC I hs i2 i3 h1.2 k2
    rw [h3] at h4 ⊢
    suffices h1 : I i3 k2 = I i2 k2 by exact ⟨h1, Eq.symm h1⟩
    exact Fin.le_antisymm h4 h5
  }
  {
    apply Finset.disjoint_filter.mpr
    intro k1 hk1 h2 h3
    apply h3
    have h4 : ∀ k, I i1 k ≤ I i2 k :=  monotone_1_of_simplex SC I hs i1 i2 h1.1
    have h5 : I i1 k1 < I i2 k1 := lt_of_le_of_ne (h4 k1) h2
    have h6 : (I i3 k1).1 ≤ (I i1 k1).1 + 1 := by {
      apply le_add_one_of_simplex _ _ hs
    }
    apply le_antisymm ( monotone_1_of_simplex SC I hs i2 i3 h1.2 k1)
    apply le_trans h6 h5
  }
}

lemma ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by {
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  simp only [ne_eq, nonpos_iff_eq_zero, Finset.card_eq_zero] at h2
  apply funext
  intro k
  rw [Finset.filter_eq_empty_iff] at h2
  simp only [Finset.mem_univ, Decidable.not_not, forall_const] at h2
  apply h2
}

noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )
    := ⟨ coord_change_count SC (I 0) (I i), by {
      refine Nat.lt_succ_of_le ?_
      exact card_finset_fin_le {i_1 | I 0 i_1 ≠ I i i_1}
    } ⟩

lemma ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by {
  intro i1 i2 h1
  unfold ccc_fun
  simp only [Fin.mk_lt_mk]
  have h3 : 0 ≤ i1 ∧ i1 ≤ i2 := ⟨ (Fin.zero_le i1), (Fin.le_of_lt h1) ⟩
  rw [ccc_add SC I hs 0 i1 i2 h3]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1
}

lemma ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by {
  apply is_insert_index_of_strict_mono
  apply ccc_fun_strict_mono SC I hs
}

lemma ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by {
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    rw [Fin.ext_iff]
    change Finset.card {k : Fin SC.n | I 0 k ≠ I (Fin.last m) k} = SC.n ↔ _
    have hcard := Finset.card_eq_iff_eq_univ
      {k : Fin SC.n | I 0 k ≠ I (Fin.last m) k}
    simpa only [Fintype.card_fin, Finset.eq_univ_iff_forall,
      Finset.mem_filter, Finset.mem_univ, true_and] using hcard
  }
  apply Iff.trans _ h1.symm
  unfold case_D
  apply Iff.intro
  {
    intro h2 k1
    obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    intro h3
    apply hi2
    apply le_antisymm
    {
      rw [h3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2)
    }
    exact monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1
  }
  {
    contrapose!
    intro h2
    obtain ⟨k2, ⟨q, hq⟩ ⟩ := h2
    use k2
    rw [hq, hq]
  }
}

lemma last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by {
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  unfold case_D at h2
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  apply Nat.add_one_le_of_lt
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  have h4 := monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k
  apply lt_of_lt_of_le _ h4
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm
}

lemma delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by {
  let I := @delete_vertex SC n1 hn1 j1 J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by { exact h2.1}
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j1
  }
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  {
    simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by {
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, zero_add]
      simp only [Fin.val_one']
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_of_pos_left scnpos
    }
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by {
      unfold I
      rw [h1, ← hi1]
      simp only [Fin.val_last]
    }
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by {
      apply ccc_pos _ _ hs
      simp only [ne_eq, Fin.zero_eq_one_iff, Nat.add_eq_right]
      omega
    }
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by {
      simp only [← h8]
      apply ccc_add SC J hs
      simp only [Fin.zero_le, true_and]
      suffices h9 : j3 ≠ j1 by {
        rw [h4] at h9
        exact Fin.one_le_of_ne_zero h9
      }
      apply insert_index_ne
    }
    have h10 : c2 + SC.n ≤ SC.n := by {
      rw [←h9]
      exact Fin.is_le (ccc_fun SC J j3)
    }
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  }
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by {
    unfold I delete_vertex
    congr!
    unfold insert_index
    simpa only [Fin.val_zero, Fin.val_pos_iff, zero_add, Fin.mk_eq_zero,
        ite_eq_left_iff, not_lt,Fin.le_zero_iff, one_ne_zero, imp_false]
  }
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by {
    unfold ccc_fun
    simp [h2]
    congr
    rw [hi1]
    rfl
  }
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne
}

lemma case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by {
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    unfold ccc_fun coord_change_count
    simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Fin.zero_eta]
  }
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  apply Iff.intro
  {
    intro h3 h4
    apply @insert_index_ne SC n1 hn1 j (Fin.last n1)
    rw [h3,h4]
  }
  {
    intro h3
    have h32 : Fin.last SC.n ≠ j := fun a ↦ h3 (Eq.symm a)
    obtain ⟨i2, hi2⟩  := @almost_surjective_of_insert_index SC n1 hn1 j (Fin.last SC.n) h32
    apply le_antisymm
    exact Fin.le_last (insert_index SC j (Fin.last n1))
    rw [hi2]
    have h4 := @insert_index_strict_mono SC n1 hn1 j
    rw [h4.le_iff_le]
    exact Fin.le_last i2
  }
}

lemma case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by exact h2.1
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j
  }
  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  {
    rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  }
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  rw [hj2, ← h1.2 h2]
}

lemma same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by {
  apply Iff.intro (fun a ↦ congrFun a j)
  intro h2
  ext j2
  by_cases h3 : j2 = j
  rw [h3,h2]
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  rw [hi1]
  exact congrFun h1 i1
}

lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by {
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    exact h1
  }
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by {
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    rw [← ha]
    simp only [Fin.val_succ, Nat.add_right_cancel_iff]
    use ⟨ a.1, by {rw [hn1]; exact a.2}⟩
  }
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := by {
    refine Fin.le_of_lt ?_
    refine Fin.lt_add_one_iff.mpr ?_
    show i1.1 < n1
    have h3 := Fin.val_lt_last h2.2
    omega
  }
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by {
    rw [Fin.le_def, Fin.le_def, ←h11.2]
    apply And.intro
    rw [←h11.1]
    apply Nat.le_add_right
    apply Nat.le_add_right
  }
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by {
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by {
      rw [← h11.2, ←h11.1]
    }
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by {
      apply ccc_add SC I hs
      simp only [Fin.zero_le, true_and, h32]
    }
    rw [← hj1, h4 ] at h3
    simp only [Nat.add_left_cancel_iff] at h3
    exact h3.symm
  }
  have h4 : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by {
    unfold coord_change_count at h3
    rw [Finset.card_eq_two] at h3
    convert h3
    simp only [ne_eq]
    rw [←Finset.coe_eq_pair]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  }
  obtain ⟨k1, ⟨k2, h4⟩ ⟩ := h4
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := by {
    have h5 := Set.mem_insert k1 {k2}
    rwa [←h4.2] at h5
  }
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := by {
    have h5 : k2 ∈ ({k1, k2} : Set _) := Set.mem_insert_of_mem k1 rfl
    rwa [←h4.2] at h5
  }
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by {
    intro h21
    let ins : SC.G := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 : ∀ k, I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by {
      intro k
      unfold ins
      have h13 : I i1 k3 ≤ I (i1+1) k3 := monotone_1_of_simplex SC I hs _ _ h32 k3
      by_cases h12 : k = k3
      simp only [h12, ↓reduceIte, le_refl, and_true, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k3
      simp only [h12, ↓reduceIte, le_refl, true_and, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k
    }
    have h22 : J3 j1 k3 ≠ I i1 k3 := by {
      rw [hJ3.2]
      unfold ins
      simp only [↓reduceIte, ne_eq]
      exact h21.symm
    }
    have h23 : ∃ k4, k3 ≠ k4 ∧ I i1 k4 ≠ I (i1+1) k4 := by {
      by_cases h24 : k3 = k1
      use k2
      rw [h24]
      apply And.intro h4.1 hk2
      use k1
    }
    have h7 : ins ∉ Set.range I := by {
      intro h9
      obtain ⟨i2,hi2⟩ := h9
      rw [forall_and, ← hi2] at h6
      rw [← monotone_2_of_simplex _ _ hs,← monotone_2_of_simplex _ _ hs] at h6
      have h13 : i2 = i1 ∨ i2 = i1 + 1 := by {
        refine (WCovBy.le_and_le_iff ?_).mp h6
        apply And.intro h32
        intro i3 h33
        simp only [not_lt]
        exact Fin.add_one_le_of_lt h33
      }
      cases' h13 with h13 h13
      apply h22
      rw [hJ3.2, ←hi2, h13]
      obtain ⟨k4, hk4⟩ := h23
      apply hk4.2
      rw [←h13, hi2]
      unfold ins
      simp only [right_eq_ite_iff]
      intro h33
      exact False.elim $ hk4.1 h33.symm
    }
    use J3
    apply And.intro hJ3.1 (And.intro _ h22)
    apply @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1
    rwa [hJ3.2]
    rwa [hJ3.2]
  }
  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 : I = @delete_vertex SC n1 hn1 j1 J3 → is_face SC I J3
    → ∀ k, I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by {
    intro h14 h13 k3
    rw [h14]
    apply And.intro
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2
  }
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by {
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by {
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      symm
      apply insert_index_ne
    }
    apply And.intro
    {
      apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    }
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro h9.2.2.symm ( And.intro h23.symm hk4)
  }
  refine Finset.card_eq_two.mpr ?_
  use J1, J2
  apply And.intro
  {
    have h71 := (h7 J1 k1 hJ1).2 k2 h4.1
    intro h9
    apply hJ2.2.2
    rw [←h9, h71]
  }
  apply subset_antisymm
  {
    intro J3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    intro hJ3
    have h14 := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    obtain ⟨j2, hj2⟩ := h14
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := h13.2 (h15.mp h1).1
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    have h18 : ∃ k5, J3 j1 k5 ≠ I i1 k5 := by {
      suffices h19 : J3 j1 ≠ I i1 by exact Function.ne_iff.mp h19
      intro h19
      apply @insert_index_ne SC n1 hn1 j1 i1
      apply hJ3.2.1.1
      rw [h19, hj2]
      rfl
    }
    obtain ⟨k5, hk5⟩ := h18
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    clear h15 h13
    have h19 : k5 = k1 ∨ k5 = k2 := by {
      have h21 : I i1 k5 ≠ I (i1+1) k5 := by {
        rw [←h73.1]
        exact hk5.symm
      }
      exact h4.2.subset h21
    }
    have h20 (J4 : _ → SC.G) : (J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4)
        → J3 j1 = J4 j1:= by {
      intro h21
      apply funext
      intro k6
      by_cases h22 : k5 = k6
      rw [←h22,h21.1,h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    }
    cases h19
    left
    rename_i h21
    apply h20
    rwa [h21]
    right
    rename_i h21
    apply h20
    rwa [h21]
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  }
  {
    refine Finset.insert_subset ?_ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ1.2.1
    simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ2.2.1
  }
}

lemma unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by {
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by {
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    simp only [Fin.val_last]
    by_cases h11 : n1 < j.1
    simp only [h11, ↓reduceIte, le_refl]
    simp only [h11, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
  }
  have h6 : 2 ≤ sᶜ.card := by {
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    use k2
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ,h2, and_self, true_and]
    use k1
    apply And.intro _ h3.symm
    rw [h1,h1]
  }
  have h7 := add_le_add h4 h6
  simp only [Finset.card_add_card_compl, Fintype.card_fin] at h7
  rw [←hn1,add_le_add_iff_left] at h7
  simp only [Nat.not_ofNat_le_one] at h7
}

lemma case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by {
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hAC
      rw [←hABC 0,h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.le_last (I (Fin.last n1) k2)
  }
  let ins2 : SC.G := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := by {
    apply Fin.val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact h1 k
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by {
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by {
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    }
    simp only [left_eq_add, Fin.one_eq_zero_iff, Nat.add_eq_right] at h11
    apply @p_ne_zero_of_cube SC n1 hn1
    simp only [Fin.last_eq_zero_iff, h11]
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    {
      rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    }
    rw [h2 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1)]
  rw [hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  rw [h5, h2 k1]
  suffices h6 : I 0 = J2 0 by {rw [h6]}
  rw [hJ2.1]
  unfold delete_vertex insert_index
  congr!
  simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
    not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
  rw [←hn1]
  omega
}

lemma case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    congr!
    simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
        not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
    rw [←hn1]
    omega
  }
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [h3 k1,←h4,hk1 0] at h5
  contrapose! h5
  exact lt_add_one SC.p
}

lemma case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by {
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hBC
      rw [←hABC (Fin.last n1),h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.zero_le (I 0 k2)
  }
  let ins2 : SC.G := fun k ↦ (I (Fin.last n1) k) - 1
  have h22 k := Fin.val_sub_one_of_ne_zero (h1 k)
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by {
    rw [h22]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by {
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by {
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    }
    simp only [Nat.add_eq_left, one_ne_zero] at h11
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_BC SC I hs J1 hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    rw [Fin.le_def, ←add_le_add_iff_right 1, h21 k2]
    exact le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2
    rw [h21 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by {
    rw [hJ2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  rw [←h6, ←h21 k1] at h5
  omega
}

lemma zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by {
  simp only [ne_eq, Fin.zero_eq_last_iff]
  rw [←hn1]
  omega
}

lemma case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←h3 k1,← h4,hk1]
  rfl
}

lemma case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by {
  have hnd : ¬ case_D SC I := by {
    contrapose! hABC
    exact hABC k1 q
  }
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  apply Iff.intro
  {
    intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · exact hn1
    · exact h1.2.1
  }
  {
    intro h1
    rw [←or_and_right] at h1
    exact h1.2
  }
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  rw [←h2.1,←h3.1]
}

lemma case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  exact hn1
}

lemma case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 h4
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1
}

lemma case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1
}

end cases_ABCD

lemma boundary_is_A_or_B {hn1 : n1 + 1 = SC.n} I (hbf : @is_boundary_face SC n1 I)
    : case_A SC I ∨ case_B SC I := by {
  have hs : simplex SC n1 I := by {
    obtain ⟨J,hJ⟩ := hbf
    exact hJ.1.1
  }
  unfold is_boundary_face at hbf
  rw [Fintype.existsUnique_iff_card_one] at hbf
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  assumption
  cases' h1 with h1 h1
  rw [@case_C_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
  rw [@case_D_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
}

lemma case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)

lemma parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) :
    Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} ∈ {c | c = 1 ∨ c = 2} := by {
  simp only [Set.mem_setOf_eq]
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  left
  cases' h1 with h2 h2
  exact @case_A_parent_count SC n1 hn1 I hs h2
  exact @case_B_parent_count SC n1 hn1 I hs h2
  right
  cases' h1 with h2 h2
  exact @case_C_parent_count SC n1 hn1 I hs h2
  exact @case_D_parent_count SC n1 hn1 I hs h2
}

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

lemma complete_simplex_iff {SC} m I(hs : simplex SC m I) :
    complete_simplex SC m I ↔ ∀ c, c ≤ m → ∃ i, SC.RL (I i) = c := by {
  apply Iff.intro
  {
    intro h1 c hc
    rwa [← Set.mem_range, h1.2, Set.mem_setOf_eq]
  }
  {
    intro c1
    apply And.intro hs
    refine Set.toFinset_inj.mp ?_
    refine (Finset.eq_iff_card_ge_of_superset ?_).mp ?_
    {
      simp only [Set.toFinset_range, Set.toFinset_subset, Finset.coe_image, Finset.coe_univ,
        Set.image_univ]
      intro c hc
      simp only [Set.mem_range, c1 c hc]
    }
    let f1 := fun (j : ℕ ) ↦ SC.RL (I (Fin.ofNat _ j))
    apply Finset.card_le_card_of_surjOn f1
    intro j h1
    simp only [Set.toFinset_range, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at h1
    obtain ⟨ i, hi⟩ := h1
    use i
    simp only [Set.coe_toFinset, Set.mem_setOf_eq]
    apply And.intro (Fin.is_le i)
    unfold f1
    rw [← hi]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
  }
}

lemma rl_inj_of_complete {SC} m I (hcs : complete_simplex SC m I):
    ∀ i1 i2, SC.RL (I i1) = SC.RL (I i2) → i1 = i2 := by {
  let f1 : Fin (m+1) → Fin (m+1) := fun j ↦ Fin.ofNat _ (SC.RL (I j))
  suffices h1 : Function.Injective f1 by {
    intro i1 i2 h2
    apply h1
    unfold f1
    rw [h2]
  }
  have h2 := hcs.2
  apply Function.Surjective.injective_of_finite
  rfl
  rw [complete_simplex_iff _ _ hcs.1] at hcs
  intro c
  obtain ⟨a, ha⟩ := hcs c (Fin.is_le c)
  use a
  unfold f1
  rw [ha]
  exact Fin.cast_val_eq_self c
}

lemma char_complete_face {SC n1 hn1} I J (hs : simplex SC SC.n J) :
    complete_simplex SC n1 I ∧ is_face SC I J
    ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J
    ∧ ∀ (c:ℕ ), c ≤ n1 → ∃ i2, i2 ≠ i ∧ SC.RL (J i2) = c := by {
  apply Iff.intro
  {
    rw [child_simplex_char]
    intro h1
    obtain ⟨i, hi1 ⟩ := h1.2
    use i
    apply And.intro hi1
    intro c hc
    have h2 := (complete_simplex_iff n1 I h1.1.1).mp h1.1 c hc
    obtain ⟨j, hj⟩ := h2
    rw [← hj, hi1]
    unfold delete_vertex
    use @insert_index SC n1 hn1 i j
    apply And.intro _ rfl
    apply insert_index_ne
    exact hn1
    exact hs
  }
  {
    intro h1
    obtain ⟨i, hi1 ⟩ := h1
    have hface : is_face SC I J := by {
      rw [child_simplex_char]
      use i
      exact hi1.1
      exact hs
    }
    apply And.intro _ hface
    rw [complete_simplex_iff n1 I hface.1]
    intro c hc
    obtain ⟨i2, hi2⟩ := hi1.2 c hc
    have h3 := @almost_surjective_of_insert_index SC n1 hn1 i i2 hi2.1
    obtain ⟨j, hj⟩ := h3
    use j
    rw [hi1.1, ← hi2.2, hj]
    rfl
  }
}

lemma complete_child_uniq {SC n1} {hn1 : n1 + 1 = SC.n} J (hcs : complete_simplex SC SC.n J) :
    ∃! (I : Fin (n1+1) → SC.G), complete_simplex SC n1 I ∧ is_face SC I J := by {
  have h4 : ∃ i, SC.RL (J i) = SC.n := by {
    rw [← Set.mem_range, hcs.2]
    simp only [Set.mem_setOf_eq, le_refl]
  }
  obtain ⟨ i, hi⟩ := h4
  let I := @delete_vertex SC n1 hn1 i J
  have hs2 : simplex SC n1 I := by {
    apply delete_vertex_simplex
    exact hcs.1
  }
  use I
  have h1 : complete_simplex SC n1 I ∧ is_face SC I J := by
  {
    rw [@char_complete_face SC n1 hn1 _ _ hcs.1]
    use i
    apply And.intro rfl
    rw [complete_simplex_iff] at hcs
    {
      intro c hc
      have h3 : c ≤ SC.n := by omega
      obtain ⟨i2, hi2 ⟩ := hcs c h3
      use i2
      apply And.intro _ hi2
      intro h4
      rw [h4, hi, ← hn1] at hi2
      rw [← hi2] at hc
      revert hc
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, imp_self]
    }
    {
      exact hcs.1
    }
  }
  simp only
  apply And.intro h1
  intro I2 h2
  rw [@char_complete_face SC n1 hn1 _ _ hcs.1] at h2
  obtain ⟨ i2, hi2 ⟩ := h2
  have h2 : SC.RL (J i2) = SC.n := by {
    let c2 := SC.RL (J i2)
    suffices h3 : ¬ (c2 ≤ n1) by {
      apply le_antisymm (SC.rl_proper (J i2)).1
      omega
    }
    intro h2
    obtain ⟨i3, hi3⟩ := hi2.2 c2 h2
    apply hi3.1
    apply rl_inj_of_complete SC.n J hcs
    exact hi3.2
  }
  suffices h3 : i2 = i by {
    rw [hi2.1, h3]
  }
  apply rl_inj_of_complete SC.n J hcs
  rw [h2]
  exact (Eq.symm hi)
}

lemma incomplete_childs {SC n1} {hn1 : n1 + 1 = SC.n} J (hs : simplex SC SC.n J)
    (hnc : ¬ complete_simplex SC SC.n J):
    Even (Finset.card { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}) := by {
  let S : Finset _:= { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}
  let c := S.card
  suffices h1 : c > 0 → c = 2 by {
    suffices h2 : Even c by {exact h2}
    by_cases h3 : c > 0
    rw [h1 h3]
    exact even_two
    use 0
    omega
  }
  intro cpos
  have h1 : Finset.Nonempty S := by {
    apply Finset.card_ne_zero.mp
    omega
  }
  obtain ⟨I1, h1 ⟩ := h1
  have hI1S := h1
  unfold S at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  obtain ⟨i1, hi1 ⟩ := (@char_complete_face SC n1 hn1 I1 J hs).mp h1
  apply Finset.card_eq_two.mpr
  have h2 : SC.RL (J i1) ≤ n1 := by {
    by_contra h3
    apply hnc
    rw [complete_simplex_iff _ _ hs]
    intro c hc
    by_cases h4 : c ≤ n1
    {
      obtain ⟨i2, hi2 ⟩ := hi1.2 c h4
      use i2
      exact hi2.2
    }
    {
      use i1
      have h6 : c = SC.n := le_antisymm hc (le_of_eq_of_le hn1.symm (not_le.mp h4))
      rw [h6]
      apply le_antisymm (SC.rl_proper (J i1)).1
      exact le_of_eq_of_le hn1.symm (not_le.mp h3)
    }
  }
  obtain ⟨i2, hi2⟩ := hi1.2 (SC.RL (J i1)) h2
  let I2 := @delete_vertex SC n1 hn1 i2 J
  have hI2S : I2 ∈ S := by {
    unfold S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [@char_complete_face SC n1 hn1 I2 J hs]
    use i2
    apply And.intro rfl
    intro c hc
    obtain ⟨i3, hi3⟩ := hi1.2 c hc
    by_cases h4 : i3 = i2
    {
      use i1
      rw [← hi3.2,h4, hi2.2]
      exact And.intro hi2.1.symm rfl
    }
    {
      use i3
      exact And.imp_left (fun a ↦ h4) hi3
    }
  }
  use I1, I2
  apply And.intro
  {
    intro h3
    apply hi2.1
    apply @delete_vertex_inj SC n1 hn1 J hs
    rw [← hi1.1, h3]
  }
  ext I3
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply Iff.intro
  {
    intro h3
    unfold S at h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
    have h31 := h3
    rw [@char_complete_face SC n1 hn1 I3 J hs] at h3
    obtain ⟨ i3, hi3 ⟩ := h3
    by_contra h4
    simp only [not_or] at h4
    rw [hi1.1] at h4
    have h7 : ∀ i4, ¬ (I3 = @delete_vertex SC n1 hn1 i4 J) → i4 ≠ i3 := by {
      intro i4 h8 h9
      apply h8
      rw [hi3.1, h9]
    }
    have h5 := @almost_surjective_of_insert_index SC n1 hn1 i3
    obtain ⟨ k1, hk1 ⟩ := h5 i1 (h7 i1 h4.1)
    obtain ⟨ k2, hk2 ⟩ := h5 i2 (h7 i2 h4.2)
    apply hi2.1
    suffices h7 : k1 = k2 by {
      rw [hk1, hk2, h7]
    }
    apply rl_inj_of_complete n1 I3 h31.1
    rw [hi3.1]
    unfold delete_vertex
    rw [← hk1, ← hk2]
    exact hi2.2.symm
  }
  {
    intro h5
    cases h5
    rename_i h9
    rwa [h9]
    rename_i h9
    rwa [h9]
  }
}

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

lemma handshake_3 (r : A → B → Prop) (c : A → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    : Odd (Finset.card {a | c a}) ↔ Odd (∑ a, Finset.card {b | r a b}) := by {
  rw [Finset.odd_sum_iff_odd_card_odd]
  rw [iff_eq_eq]
  congr
  ext a
  exact h1 a
}

lemma handshake_2 (r : A → B → Prop)
    (c : A → Prop) (d : B → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    (h2 : ∀ b, d b ↔ Odd (Finset.card {a | r a b})) :
    Odd (Finset.card {a | c a}) → Odd (Finset.card {b | d b}) := by {
  intro h3
  have h5 : ∑ a, Finset.card {b | r a b} = ∑ b, Finset.card {a | r a b} := by {
    apply Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  }
  let r2 b a := r a b
  rw [handshake_3 r2 d h2, ←h5]
  rwa [←handshake_3 r c h1]
}

lemma handshake_1 (r : A → B → Prop)
    (c1 c2 c3: A → Prop) (d1 d2: B → Prop)
    (h1 : ∀ b, d1 b → ∃! a, c2 a ∧ r a b)
    (h2 : ∀ b, d2 b → ¬ d1 b → Even (Finset.card { a | c2 a ∧ r a b}))
    (h3 : ∀ a, c3 a → Finset.card { b | r a b} ∈ {c | c = 1 ∨ c = 2})
    (h5 : ∀ a, c1 a ↔ (∃! b, r a b) ∧ c2 a)
    (h6 : ∀ a, c2 a → c3 a) (h7 : ∀ b, ∀ a, r a b → d2 b)
    : Odd (Finset.card {a : A | c1 a}) → Odd (Finset.card {b : B | d1 b}) := by {
  let r2 a b := c2 a ∧ r a b
  apply handshake_2 r2
  {
    intro a
    rw [h5]
    by_cases p1 : c2 a
    unfold r2
    simp only [p1, and_true, true_and]
    rw [Fintype.existsUnique_iff_card_one]
    apply Iff.intro
    {
      intro p2
      use 0
      rwa [mul_zero, zero_add]
    }
    {
      intro p2
      have p3 := h3 a (h6 a p1)
      simp only [Set.mem_setOf_eq] at p3
      cases p3
      rename_i p4
      exact p4
      rename_i p4
      rw [p4] at p2
      exfalso
      revert p2
      simp only [imp_false, Nat.not_odd_iff_even, even_two]
    }
    {
      unfold r2
      simp only [p1, and_false, false_and, Finset.filter_false, Finset.card_empty, Nat.not_odd_zero]
    }
  }
  {
    intro b
    by_cases p1 : d1 b
    {
      simp only [p1, true_iff]
      use 0
      rw [mul_zero, zero_add]
      rw [← Fintype.existsUnique_iff_card_one]
      exact h1 b p1
    }
    {
      simp only [p1, false_iff]
      intro p2
      have p5 : Finset.Nonempty {a | r2 a b} := by {
        have p3 : Odd (Finset.card { a | r2 a b}) := by {
          convert p2
        }
        apply Finset.card_ne_zero.mp
        intro p4
        revert p3
        rw [p4]
        simp only [Nat.not_odd_zero, imp_self]
      }
      have p3 : d2 b := by {
        obtain ⟨a, p6⟩ := p5
        apply h7 b a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at p6
        exact p6.2
      }
      revert p2
      have p4 := h2 b p3 p1
      simp only [imp_false, Nat.not_odd_iff_even]
      convert p4
    }
  }
}

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

def child_map (v : Fin n1 → Fin (SC.p+1) ) : SC.G := fun i ↦
  match n1 with
  | 0 => Fin.last SC.p
  | Nat.succ _ => if i.1 + 1 = SC.n then Fin.last SC.p else v (Fin.ofNat _ i.1)

lemma child_map_last (v : Fin n1 → Fin (SC.p +1 ))
    : ∀ j, j.1 + 1 = SC.n → child_map SC v j = SC.p := by {
  intro j hj
  unfold child_map
  cases n1
  rfl
  simp only [hj, ↓reduceIte, Fin.val_last]
}

lemma child_map_applied [NeZero SC.n] {hn1 : n1 + 1 = SC.n} (v : Fin n1 → Fin (SC.p + 1))
    : ∀ (i : Fin n1), child_map SC v (Fin.ofNat _ i.1) = v i := by {
  intro i
  dsimp only [child_map]
  cases n1
  exact Fin.elim0 i
  rename_i n2
  simp only [Nat.succ_eq_add_one]
  have h5 : i.1 + 1 < SC.n := by omega
  have h2 : i.1 < SC.n := by omega
  have h3 := Fin.val_cast_of_lt h2
  rw [Fin.ofNat_eq_cast, h3]
  have h6 : i.1 + 1 ≠ SC.n := by omega
  simp only [h6, ↓reduceIte, Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
}

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

lemma child_map_surj_on {hn1 : n1 + 1 = SC.n} w
    (h1 : ∀ j, j.1 + 1 = SC.n → w j = SC.p)
    : ∃ v, @child_map SC n1 v = w := by {
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  let v2 : Fin n1 → Fin (SC.p +1) := fun i ↦ w (Fin.ofNat _ i.1)
  use v2
  apply funext
  intro i
  unfold child_map
  cases n1
  {
    simp only
    have h2 := h1 0
    simp only [Fin.val_zero, zero_add] at h2 hn1
    have h3 : i = 0 := by {
      have h4 := i.2
      simp only [← hn1] at h4
      ext
      simp only [Fin.val_zero]
      exact Nat.lt_one_iff.mp h4
    }
    rw [h3]
    exact Fin.eq_of_val_eq (id (Eq.symm (h2 hn1)))
  }
  {
    rename_i n2
    have h2 := h1 i
    by_cases h3 : i.1 +1 = SC.n
    {
      simp only [h3, ↓reduceIte]
      exact Eq.symm (Fin.eq_of_val_eq (h1 i h3))
    }
    simp only [h3, ↓reduceIte, Nat.succ_eq_add_one]
    unfold v2
    congr
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt]
    exact Fin.cast_val_eq_self i
    have h4 := i.2
    simp only [← hn1] at h3 h4
    omega
  }
}

def child_cube {hn1 : n1 + 1 = SC.n}: SpernerCube where
  n := n1
  p := SC.p
  RL := fun v ↦ SC.RL (child_map SC v)
  rl_proper := by {
    intro v
    have h0 : NeZero SC.n := by {
      rw [← hn1]
      exact instNeZeroNatHAdd_1
    }
    have h1 := child_map_last SC v
    have h2 := SC.rl_proper (child_map SC v)
    apply And.intro
    {
      have h3 := (h2.2 (Fin.ofNat _ n1)).2
      have h4 : n1 < SC.n := by omega
      simp only [Fin.ofNat_eq_cast] at h3
      rw [Fin.val_cast_of_lt h4] at h3
      apply h3
      apply child_map_last
      rw [Fin.val_cast_of_lt h4]
      exact hn1
    }
    intro i
    have h3 := h2.2 (Fin.ofNat _ i.1)
    rw [child_map_applied] at h3
    have h4 : (Fin.ofNat SC.n i.1).1 = i.1 := by {
      apply Fin.val_cast_of_lt
      omega
    }
    rwa [h4] at h3
    exact hn1
  }

end induction_step

lemma induction_start (SC : SpernerCube) (h0 : 0 = SC.n)
    : Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  use 0
  simp only [mul_zero, zero_add]
  rw [←Fintype.existsUnique_iff_card_one]
  let b : SC.G := fun _ ↦ 0
  let a : Fin (SC.n + 1) → SC.G := fun _ ↦ b
  use a
  simp only
  have h1 (x : Fin (SC.n+1)) : x = 0 := by {
    ext
    simp only [Fin.val_zero]
    rw [← Nat.lt_one_iff]
    apply Fin.val_lt_of_le x
    rw [←h0]
  }
  have hf (j : Fin SC.n) : False := by {
    apply Fin.elim0
    rwa [h0]
  }
  apply And.intro
  apply And.intro
  apply And.intro
  {
    intro x1 x2 _
    rw [h1 x1, h1 x2]
  }
  {
    intro i hi j
    exact False.elim ( hf j )
  }
  {
    ext i
    simp only [← h0]
    simp only [Set.mem_range, nonpos_iff_eq_zero, Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    have h3 : ∀ c, SC.RL (a c) = 0 := by {
      intro c
      have h2 := (SC.rl_proper (a c)).1
      simp only [← h0] at h2
      omega
    }
    apply Iff.intro
    {
      intro h2
      cases h2
      rename_i c hc
      rw [h3 c] at hc
      exact (Eq.symm hc)
    }
    {
      intro hi0
      use 0
      rw [hi0]
      exact h3 0
    }
  }
  {
    intro a2 h2
    ext i
    apply funext
    intro j
    exact False.elim ( hf j )
  }
}

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

theorem weaker_cubical_sperner SC : ∃ I, complete_simplex SC SC.n I := by {
  have h1 := strong_cubical_sperner SC.n SC rfl
  obtain ⟨k1, hk1⟩ := h1
  have h2 : 0 < 2 * k1 + 1 := by omega
  rw [←hk1, Finset.card_pos] at h2
  obtain ⟨I, hI1⟩ := h2
  use I
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI1
  exact hI1
}

end AbstractModule11


/- BEGIN FixedPointTheorems.apply_cubical_sperner -/
section AbstractModule12


/-!
# Fixed points in the unit cube

Reduced labels encode coordinatewise displacement of a continuous cube map.
Cubical Sperner simplices on finer grids yield approximate fixed points, and
compactness of the cube supplies a genuine fixed point.
-/


open Classical

variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by {
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  {
    have h1 : @rl_point n f x = n := by {
      show rlp = n
      unfold rlp minval
      rw [he]
      simp only [Finset.min_empty]
    }
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    }
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  }
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have h1 : @rl_point n f x = m.1 := by {
    show rlp = m.1
    unfold rlp minval
    rw [hm]
  }
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  {
    intro h2
    suffices h3 : k1 ∈ s by {
      unfold s at h3
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
      exact h3
    }
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  }
  {
    intro h2
    have h3 : k1 ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, h2, and_self]
    }
    exact Finset.min_le_of_eq h3 hm
  }
}

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by {
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  {
    intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  }
  {
    intro h2
    apply (h1.2 k).2
    exact Or.inr h2
  }
}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  {
    intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  }
  {
    contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2
  }
}

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_setOf_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by {
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    apply And.intro h1.1
    intro k
    apply And.intro
    {
      intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    }
    {
      intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    }
  }

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }
}

lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by {
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := by {
    intro h4
    exact h3.2.symm.subset h4
  }
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  use x0
  intro k
  apply And.intro
  {
    apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  }
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map SC.p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  unfold x0 xk
  apply dist_discrete_map p ppos
  have h5 := le_add_one_of_simplex SC I h3.1
  intro k
  exact ⟨h5 i0 ik k, h5 ik i0 k⟩
}

theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by {
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by {
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 : ℕ → Fin n → ℝ := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := fun i ↦ (x0s i).2
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  }
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let y0 := x0s ∘ φ
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) := by {
    exact (continuous_apply k).comp continuous_subtype_val
  }
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by {
    show g k xxx ≤ g k (f xxx)
    have h6 :=  (hc2 k).seqContinuous h2.2
    have h7 := (hc2 k).seqContinuous $ f.2.seqContinuous h2.2
    apply le_of_tendsto_of_tendsto' h6 h7
    exact fun i ↦ (hx0 (φ i) k).1
  }
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by {
    show g k (f xxx) ≤ g k xxx
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := axiomOfChoice h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by {
      apply tendsto_of_tendsto_of_dist h2.2
      have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h7 _
      {
        intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      }
      exact fun _ ↦ dist_nonneg
    }
    have h7 := (hc2 k).seqContinuous h4
    have h8 := (hc2 k).seqContinuous $ f.2.seqContinuous h4
    apply le_of_tendsto_of_tendsto' h8 h7
    exact fun i ↦ (h6 i).2
  }
  use xxx
  ext k
  apply le_antisymm (h4 k) (h3 k)
}

theorem fixed_point_unit_cube_isFixedPt (f : C(@unit_cube n, @unit_cube n)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using fixed_point_unit_cube f

end AbstractModule12


/- BEGIN FixedPointTheorems.convex_homeos -/
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


/- BEGIN FixedPointTheorems.brouwer -/
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

theorem brouwer_fixed_point_isFixedPt {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using brouwer_fixed_point s hcvx hcmpct hne f

theorem brouwer_fixedPoints_nonempty {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    (Function.fixedPoints f).Nonempty := by
  exact brouwer_fixed_point_isFixedPt s hcvx hcmpct hne f

end AbstractModule14


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FixedPoint -/
section AbstractModule15


namespace OAI

/-! Fixed points of continuous maps on compact convex sets of real-valued functions. -/

namespace MatrixMultiplication.AuxiliarySeparation

open Set
open scoped BigOperators

private def weightSimplex (J : Type*) [Fintype J] : Set (J → ℝ) :=
  {w | (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1}

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

theorem exists_finite_partition_weights {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ a : Fin n → K, ∃ w : Fin n → C(K, ℝ),
      (∀ x j, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      (∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| < ε) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : K → Set K := fun a => {x | ∀ i ∈ s, |a.val i - x.val i| < ε}
  have hUo : ∀ a, IsOpen (U a) := by
    intro a
    have hUa : U a = ⋂ i ∈ s, {x : K | |a.val i - x.val i| < ε} := by
      ext x
      simp [U]
    rw [hUa]
    apply isOpen_biInter_finset
    intro i hi
    exact isOpen_lt (continuous_const.sub ((continuous_apply i).comp continuous_subtype_val)).abs continuous_const
  have hUc : (univ : Set K) ⊆ ⋃ a, U a := by
    intro x hx
    refine mem_iUnion.mpr ⟨x, ?_⟩
    intro i hi
    simpa using hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have htc : (univ : Set K) ⊆ ⋃ a : t, U a.val := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hat, hax⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨⟨a, hat⟩, hax⟩
  obtain ⟨w, hw⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun a : t => U a.val) (fun a => hUo a.val) htc
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, (fun j => (e j).val), (fun j => w (e j)), ?_, ?_, ?_⟩
  · intro x j
    exact w.nonneg (e j) x
  · intro x
    change ∑ j, w (e j) x = 1
    calc
      ∑ j, w (e j) x = ∑ a : t, w a x := e.sum_comp (fun a => w a x)
      _ = 1 := by simpa only [finsum_eq_sum_of_fintype] using w.sum_eq_one (mem_univ x)
  · intro x j hj i hi
    exact hw (e j) (subset_closure hj) i hi


theorem exists_finite_partition_weights_nonempty {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (hne : K.Nonempty) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → K, ∃ w : Fin n → C(K, ℝ),
      (∀ x j, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      (∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| < ε) := by
  obtain ⟨n, a, w, hw0, hw1, hwa⟩ := exists_finite_partition_weights hK s hε
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    obtain ⟨x, hx⟩ := hne
    simpa using hw1 ⟨x, hx⟩
  exact ⟨n, hn, a, w, hw0, hw1, hwa⟩

theorem compact_approx_limit {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (_hne : K.Nonempty) (f : K → (I → ℝ)) (hf : Continuous f)
    (happrox : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : K, ∀ i ∈ s, |f x i - x.val i| ≤ ε) :
    ∃ x : K, f x = x.val := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : (I × {ε : ℝ // 0 < ε}) → Set K :=
    fun p => {x | |f x p.1 - x.val p.1| ≤ p.2.val}
  have hclosed (p : I × {ε : ℝ // 0 < ε}) : IsClosed (C p) := by
    exact isClosed_le
      (((continuous_apply p.1).comp hf).sub
        ((continuous_apply p.1).comp continuous_subtype_val)).abs continuous_const
  have hfinite (s : Finset (I × {ε : ℝ // 0 < ε})) :
      (⋂ p ∈ s, C p).Nonempty := by
    let es : Finset ℝ := insert 1 (s.image fun p => p.2.val)
    have hes : es.Nonempty := ⟨1, by simp [es]⟩
    have he : 0 < es.min' hes := by
      rw [Finset.lt_min'_iff]
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · norm_num
      · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
        exact p.2.property
    obtain ⟨x, hx⟩ := happrox (s.image Prod.fst) (es.min' hes) he
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro p hp
    exact (hx p.1 (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).trans
      (Finset.min'_le es p.2.val (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨x, funext fun i => ?_⟩
  have hzero : |f x i - x.val i| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [C, Set.mem_setOf_eq, zero_add] using
      (Set.mem_iInter.mp hx (i, ⟨ε, hε⟩))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))


/-- Schauder--Tychonoff for an arbitrary product of real lines. Compactness of the
set, rather than finite dimensionality of the ambient space, is the hypothesis. -/
theorem compact_convex_fixedPoint {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (f : C(K, K)) : ∃ x : K, f x = x := by
  have happrox : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : K, ∀ i ∈ s, |(f x).val i - x.val i| ≤ ε := by
    intro s ε hε
    obtain ⟨n, hn, a, w, hw0, hw1, hwa⟩ :=
      exists_finite_partition_weights_nonempty hKcompact hKne s hε
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact exists_approximate_fixedPoint_of_weights hKconvex f a w
      (fun j x => hw0 x j) hw1 s ε
      (fun x j hj i hi => (hwa x j hj i hi).le)
  obtain ⟨x, hx⟩ := compact_approx_limit hKcompact hKne
    (fun x => (f x).val) (continuous_subtype_val.comp f.continuous) happrox
  exact ⟨x, Subtype.ext hx⟩

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

/-- Translate a state by multiplication, then normalize at the unit. -/
def normalizedTranslate (z : S) (f : S → ℝ) : S → ℝ :=
  fun x => f (z * x) / f z

theorem normalizedTranslate_continuousOn {K : Set (S → ℝ)} (z : S)
    (hz : ∀ f ∈ K, f z ≠ 0) :
    Continuous (fun f : K => normalizedTranslate z f.val) := by
  apply continuous_pi
  intro x
  exact ((continuous_apply (z * x)).comp continuous_subtype_val).div
    ((continuous_apply z).comp continuous_subtype_val) (fun f => hz f.val f.property)

def frozenConstraint (z : S) (c : ℝ) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = c * f x}

def frozenSlice (C : Set (S → ℝ)) (z : S) (c : ℝ) : Set (S → ℝ) :=
  C ∩ frozenConstraint z c

theorem frozenConstraint_isClosed (z : S) (c : ℝ) :
    IsClosed (frozenConstraint z c) := by
  unfold frozenConstraint
  simp only [setOf_forall]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_apply (z * x)) (continuous_const.mul (continuous_apply x))

theorem frozenSlice_isClosed {C : Set (S → ℝ)} (hC : IsClosed C) (z : S) (c : ℝ) :
    IsClosed (frozenSlice C z c) :=
  hC.inter (frozenConstraint_isClosed z c)

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

theorem frozenConstraint_normalizedTranslate_eq {z : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) (hf1 : f 1 = 1) (hfz : f z ≠ 0) :
    normalizedTranslate z f = f := by
  funext x
  change f (z * x) / f z = f x
  rw [hf x, ← frozenConstraint_value hf hf1]
  exact mul_div_cancel_left₀ (f x) hfz

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

/-- A compact convex normalized state space invariant under multiplication
translates contains a multiplicative state. Frozen eigenvalue slices preserve
convexity at each finite fixed-point step. -/
theorem exists_multiplicative_of_invariant_states {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1) (hKzero : ∀ f ∈ K, f 0 = 0)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K) :
    ∃ f ∈ K, ∀ x y, f (x * y) = f x * f y := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let F : {z : S // z ≠ 0} → Set K :=
    fun z => {f | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
  have hFclosed (z : {z : S // z ≠ 0}) : IsClosed (F z) := by
    change IsClosed {f : K | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
    simp only [setOf_forall]
    exact isClosed_iInter fun x =>
      isClosed_eq ((continuous_apply (z.val * x)).comp continuous_subtype_val)
        (((continuous_apply z.val).comp continuous_subtype_val).mul
          ((continuous_apply x).comp continuous_subtype_val))
  have hFfinite (t : Finset {z : S // z ≠ 0}) : (⋂ z ∈ t, F z).Nonempty := by
    obtain ⟨C, hCK, hCne, _, _, _, hCt⟩ := exists_finite_multiplicative_slice
      hKcompact hKconvex hKne hKnorm hKnonzero hKmap t
    obtain ⟨f, hf⟩ := hCne
    refine ⟨⟨f, hCK hf⟩, ?_⟩
    simp only [mem_iInter]
    intro z hz
    exact hCt f hf z hz
  obtain ⟨f, hf⟩ := CompactSpace.iInter_nonempty hFclosed hFfinite
  refine ⟨f.val, f.property, fun x y => ?_⟩
  by_cases hx : x = 0
  · simp [hx, hKzero f.val f.property]
  · exact mem_iInter.mp hf ⟨x, hx⟩ y

/-- Appendix A.2 for a ranked restriction semiring: once the preliminary
normalized state set is nonempty, it contains a multiplicative state. -/
theorem normalizedStates_exists_multiplicative [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ f ∈ normalizedStates (fun x => (R x : ℝ)) d k,
      ∀ x y, f (x * y) = f x * f y := by
  apply exists_multiplicative_of_invariant_states
    (normalizedStates_isCompact _ d k) (normalizedStates_convex _ d k) hne
  · exact fun _ hf => hf.2.1
  · exact fun _ hf => state_zero hf
  · intro f hf z hz
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (state_one_le hf (hunit z hz)))
  · intro z hz f hf
    exact state_rescale hf z (hunit z hz) (hmulmono z) (hdom z)

/-- The multiplicative state as a normalized monotone semiring homomorphism,
with the original rank bounds and detector inequality preserved. -/
theorem exists_monotone_semiringHom_of_normalizedStates [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ R x) ∧ k ≤ χ d := by
  obtain ⟨f, hf, hfmul⟩ :=
    normalizedStates_exists_multiplicative R d k hunit hmulmono hdom hne
  let χ : S →+* ℝ :=
    { toFun := f
      map_zero' := state_zero hf
      map_one' := hf.2.1
      map_add' := hf.2.2.1
      map_mul' := hfmul }
  refine ⟨χ, ?_, hf.1, ?_⟩
  · intro x y hxy
    exact hf.2.2.2.1 x y hxy
  · simpa only [χ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      mul_one, hf.2.1] using hf.2.2.2.2 1

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end AbstractModule16


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.SpectralLimit -/
section AbstractModule17



namespace OAI

/-!
# Removing positive slack from the spectral inequality

The positive slack in the exponent can be sent to zero with the matrix size
fixed. A bound at all positive natural sizes then removes a fixed additive
error term.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter Topology

/-- Continuity removes the positive slack in the spectral exponent. -/
theorem spectral_bound_of_positive_slack {ν k D : ℝ} {d n : ℕ}
    (hν : 0 < ν) (hn : 1 ≤ n)
    (hbound : ∀ δ : ℝ, 0 < δ →
      (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ)) ≤ (n : ℝ) * k + D) :
    (d : ℝ) ^ ν * (n : ℝ) ≤ (n : ℝ) * k + D := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    exact this.ne'
  have hδ : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdenom : Tendsto (fun m : ℕ => ν + 1 / ((m : ℝ) + 1))
      atTop (𝓝 ν) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := ν)).add hδ
  have hexponent : Tendsto (fun m : ℕ => ν / (ν + 1 / ((m : ℝ) + 1)))
      atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => ν / (ν + 1 / ((m : ℝ) + 1)))
        atTop (𝓝 (ν / ν)) := by
      exact (tendsto_const_nhds (x := ν)).div hdenom hν.ne'
    rwa [div_self hν.ne'] at h
  have hpower : Tendsto
      (fun m : ℕ => (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + 1 / ((m : ℝ) + 1))))
      atTop (𝓝 ((d : ℝ) ^ ν * (n : ℝ))) := by
    simpa using tendsto_const_nhds.mul
      ((Real.continuousAt_const_rpow hn0).tendsto.comp hexponent)
  exact le_of_tendsto' hpower fun m => hbound _ (by positivity)

/-- A fixed additive error cannot enlarge a coefficient bounded at every
positive natural size. -/
theorem coefficient_le_of_nat_mul_bound {a k D : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → a * (n : ℝ) ≤ (n : ℝ) * k + D) :
    a ≤ k := by
  by_contra h
  have hgap : 0 < a - k := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (D / (a - k)) 0)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by
    have : 0 < n := by exact_mod_cast hn0
    omega
  have hlarge : D < (n : ℝ) * (a - k) :=
    (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_left _ _) hn)
  have hsmall := hbound n hn1
  nlinarith

/-- Uniform spectral inequalities for all positive sizes and all positive
slacks force the desired coefficient bound. -/
theorem spectral_coefficient_le_of_all_nat {ν k D : ℝ} {d : ℕ}
    (hν : 0 < ν)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ δ : ℝ, 0 < δ →
      (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ)) ≤ (n : ℝ) * k + D) :
    (d : ℝ) ^ ν ≤ k := by
  apply coefficient_le_of_nat_mul_bound
  intro n hn
  exact spectral_bound_of_positive_slack hν hn (hbound n hn)

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule17


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead -/
section AbstractModule18



namespace OAI

/-!
# Removing polynomial overhead from exponential inequalities

The interpolation argument in Section 4 bounds tensor powers with an extra
linear factor. Such a factor does not change their exponential growth rate.
The statements below include eventual inequalities and constant factors, so
the same argument also removes fixed counting losses in entropy limits.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- An eventual linear prefactor cannot increase an exponential growth rate. -/
theorem le_of_eventually_pow_le_linear_mul_pow {a b K C : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ ((j : ℝ) * K + C) * a ^ j) :
    b ≤ a := by
  by_contra hba
  have hab : a < b := lt_of_not_ge hba
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hr₀ : 0 ≤ a / b := div_nonneg ha hb.le
  have hr₁ : a / b < 1 := (div_lt_one hb).2 hab
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hr₀ hr₁).mul_const K
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).const_mul C
  have hlim : Tendsto (fun j : ℕ => ((j : ℝ) * K + C) * (a / b) ^ j)
      atTop (𝓝 0) := by
    convert hlinear.add hconstant using 1 <;> try simp
    funext j
    ring
  have hbound : ∀ᶠ j : ℕ in atTop,
      1 ≤ ((j : ℝ) * K + C) * (a / b) ^ j := by
    filter_upwards [h] with j hj
    have hdiv := (div_le_div_iff_of_pos_right (pow_pos hb j)).2 hj
    simpa only [div_self (pow_ne_zero j hb.ne'), mul_div_assoc, div_pow] using hdiv
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim hbound
  linarith

/-- Removing the linear interpolation overhead from inequalities for all powers. -/
theorem le_of_pow_le_linear_mul_pow {a b K : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ ((j : ℝ) * K + 1) * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_linear_mul_pow ha (Eventually.of_forall h)

/-- Fixed multiplicative losses disappear on taking exponential growth rates. -/
theorem le_of_eventually_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ C * a ^ j) : b ≤ a := by
  apply le_of_eventually_pow_le_linear_mul_pow (K := 0) (C := C) ha
  simpa only [mul_zero, zero_add] using h

/-- An all-powers form of constant-factor removal. -/
theorem le_of_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ C * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_const_mul_pow ha (Eventually.of_forall h)

/-- In particular, the fixed factor five in the type-counting bound is harmless. -/
theorem le_of_pow_le_five_mul_pow {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ 5 * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_const_mul_pow ha (Eventually.of_forall h)

/-- A fixed counting loss does not contribute to a normalized logarithmic
growth rate. The exponent may run through any sequence tending to infinity,
including the multiples of a common denominator used for rational types. -/
theorem exp_le_of_tendsto_log_div {u : ℕ → ℝ} {n : ℕ → ℕ} {b C L : ℝ}
    (hb : 0 < b) (hC : 0 < C) (hn : Tendsto n atTop atTop)
    (hu : ∀ᶠ k in atTop, 0 < u k)
    (hlim : Tendsto (fun k => Real.log (u k) / (n k : ℝ)) atTop (𝓝 L))
    (hbound : ∀ᶠ k in atTop, u k ≤ C * b ^ n k) :
    Real.exp L ≤ b := by
  have hconstant : Tendsto (fun k => Real.log C / (n k : ℝ) + Real.log b)
      atTop (𝓝 (Real.log b)) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).comp hn).add_const
      (Real.log b)
  have hnormalized : ∀ᶠ k in atTop,
      Real.log (u k) / (n k : ℝ) ≤ Real.log C / (n k : ℝ) + Real.log b := by
    filter_upwards [hu, hbound, hn.eventually (eventually_gt_atTop 0)] with k huk hk hnk
    have hnpos : (0 : ℝ) < n k := by exact_mod_cast hnk
    have hlog := Real.log_le_log huk hk
    rw [Real.log_mul hC.ne' (pow_ne_zero _ hb.ne'), Real.log_pow] at hlog
    calc
      Real.log (u k) / (n k : ℝ) ≤
          (Real.log C + (n k : ℝ) * Real.log b) / (n k : ℝ) :=
        (div_le_div_iff_of_pos_right hnpos).2 hlog
      _ = Real.log C / (n k : ℝ) + Real.log b := by
        field_simp
  have hL : L ≤ Real.log b := le_of_tendsto_of_tendsto hlim hconstant hnormalized
  simpa only [Real.exp_log hb] using Real.exp_le_exp.mpr hL

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule18


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.MultiplicativePower -/
section AbstractModule19



namespace OAI

/-!
# Monotone multiplicative functions on the positive natural numbers

The scalar classification used in Section 3.1: positivity, multiplicativity,
and monotonicity force a function on positive natural numbers to be a real
power. No property of the function at zero is required.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Multiplicativity and positivity determine the value at one. -/
theorem positiveMultiplicative_one
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) :
    f 1 = 1 := by
  have hm := hmul 1 1 (by omega) (by omega)
  have hp := hpos 1 (by omega)
  norm_num at hm
  nlinarith

/-- A positive multiplicative function preserves natural powers. -/
theorem positiveMultiplicative_pow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : f (n ^ k) = f n ^ k := by
  induction k with
  | zero => simpa using positiveMultiplicative_one hpos hmul
  | succ k ih =>
      rw [pow_succ, hmul (n ^ k) n (pow_pos hn k) hn, ih, pow_succ]

/-- Monotonicity transfers comparisons of natural powers to the values. -/
theorem positiveMultiplicative_pow_le_pow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {j k : ℕ}
    (h : m ^ j ≤ n ^ k) : f m ^ j ≤ f n ^ k := by
  rw [← positiveMultiplicative_pow hpos hmul hm,
    ← positiveMultiplicative_pow hpos hmul hn]
  exact hmono (pow_pos hm j) (pow_pos hn k) h

/-- The same comparison after taking logarithms. -/
theorem positiveMultiplicative_log_pow_le
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {j k : ℕ}
    (h : m ^ j ≤ n ^ k) :
    (j : ℝ) * Real.log (f m) ≤ (k : ℝ) * Real.log (f n) := by
  have hv := positiveMultiplicative_pow_le_pow hpos hmul hmono hm hn h
  simpa only [Real.log_pow] using
    Real.log_le_log (pow_pos (hpos m hm) j) hv

/-- Bounds from neighboring powers of two have a fixed logarithmic error,
independent of the exponent `k`. -/
theorem positiveMultiplicative_log_error_bounds
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k : ℝ) * (Real.log (f n) * Real.log 2 -
      Real.log (n : ℝ) * Real.log (f 2)) ≤ Real.log (f 2) * Real.log 2 ∧
    (k : ℝ) * (Real.log (n : ℝ) * Real.log (f 2) -
      Real.log (f n) * Real.log 2) ≤ Real.log (f 2) * Real.log 2 := by
  have hf2 : 0 ≤ Real.log (f 2) := by
    apply Real.log_nonneg
    have hm := hmono (show (1 : ℕ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℕ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
    rwa [positiveMultiplicative_one hpos hmul] at hm
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨m, hlow, hupp⟩ :=
    exists_nat_pow_near (show 1 ≤ n ^ k from Nat.one_le_iff_ne_zero.mpr (by positivity))
      (show 1 < (2 : ℕ) by omega)
  have hflow := positiveMultiplicative_log_pow_le hpos hmul hmono
    (show 0 < (2 : ℕ) by omega) hn hlow
  have hfupp := positiveMultiplicative_log_pow_le hpos hmul hmono hn
    (show 0 < (2 : ℕ) by omega) hupp.le
  have hlow' : (2 : ℝ) ^ m ≤ (n : ℝ) ^ k := by exact_mod_cast hlow
  have hupp' : (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hupp.le
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) m) hlow'
  have hnupp := Real.log_le_log (pow_pos hnp k) hupp'
  simp only [Real.log_pow, Nat.cast_add, Nat.cast_one] at hflow hfupp hnlow hnupp
  have h₁ := mul_le_mul_of_nonneg_right hfupp hlog2
  have h₂ := mul_le_mul_of_nonneg_right hnlow hf2
  have h₃ := mul_le_mul_of_nonneg_right hnupp hf2
  have h₄ := mul_le_mul_of_nonneg_right hflow hlog2
  constructor <;> nlinarith

/-- If every natural multiple of both differences has a common upper bound,
the two real numbers coincide. -/
theorem eq_of_nat_mul_sub_bounded {x y C : ℝ}
    (hxy : ∀ k : ℕ, (k : ℝ) * (x - y) ≤ C)
    (hyx : ∀ k : ℕ, (k : ℝ) * (y - x) ≤ C) : x = y := by
  apply le_antisymm
  · by_contra h
    have hd : 0 < x - y := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (x - y))
    have hk' : C < (k : ℝ) * (x - y) := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hxy k)) hk'
  · by_contra h
    have hd : 0 < y - x := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (y - x))
    have hk' : C < (k : ℝ) * (y - x) := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hyx k)) hk'

/-- The logarithmic exponent is the same at every positive natural number. -/
theorem positiveMultiplicative_log_eq
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    Real.log (f n) = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by
  have heq : Real.log (f n) * Real.log 2 =
      Real.log (n : ℝ) * Real.log (f 2) :=
    eq_of_nat_mul_sub_bounded
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).1)
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).2)
  calc
    Real.log (f n) = (Real.log (n : ℝ) * Real.log (f 2)) / Real.log 2 :=
      (eq_div_iff (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne').2 heq
    _ = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by ring

/-- The explicit exponent in the classification of positive monotone
multiplicative functions on the positive natural numbers. -/
theorem positiveMultiplicative_eq_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    f n = (n : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnp, ← positiveMultiplicative_log_eq hpos hmul hmono hn,
    Real.exp_log (hpos n hn)]

/-- Every positive monotone multiplicative function on the positive natural
numbers is a nonnegative real power, as used in Section 3.1. -/
theorem positiveMultiplicative_is_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0)) :
    ∃ p : ℝ, 0 ≤ p ∧ ∀ n : ℕ, 0 < n → f n = (n : ℝ) ^ p := by
  refine ⟨Real.log (f 2) / Real.log 2, ?_, fun n hn =>
    positiveMultiplicative_eq_rpow hpos hmul hmono hn⟩
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply Real.log_nonneg
  have hm := hmono (show (1 : ℕ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℕ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
  rwa [positiveMultiplicative_one hpos hmul] at hm

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule19


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Product -/
section AbstractModule20


namespace OAI

/-!
# Exact growth of the product in Section 6

The paper's sequence starts at `G₁ = 1`. Here `growthProduct n` denotes
`Gₙ₊₁`. Cubing each factor gives an elementary lower bound, so no logarithmic
asymptotics are needed for this part of the argument.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- The product sequence from Section 6, indexed from zero. -/
noncomputable def growthProduct : ℕ → ℝ
  | 0 => 1
  | n + 1 => growthProduct n * (1 + 1 / (3 * ((n : ℝ) + 1)))

@[simp] theorem growthProduct_zero : growthProduct 0 = 1 := rfl

@[simp] theorem growthProduct_succ (n : ℕ) :
    growthProduct (n + 1) = growthProduct n * (1 + 1 / (3 * ((n : ℝ) + 1))) := rfl

theorem growthProduct_pos (n : ℕ) : 0 < growthProduct n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [growthProduct_succ]
    exact mul_pos ih (by positivity)

/-- Cubing one product factor dominates the corresponding telescoping factor. -/
theorem one_add_recip_three_cube_lower {a : ℝ} (ha : 0 < a) :
    1 + 1 / a ≤ (1 + 1 / (3 * a)) ^ 3 := by
  have hnonneg : 0 ≤ 1 / (3 * a) := by positivity
  have hdiv : 1 / a = 3 * (1 / (3 * a)) := by
    field_simp
  rw [hdiv]
  nlinarith [sq_nonneg (1 / (3 * a)),
    mul_nonneg (sq_nonneg (1 / (3 * a))) hnonneg]

/-- The exact lower bound `Gₙ₊₁³ ≥ n + 1`. -/
theorem growthProduct_cube_lower (n : ℕ) :
    (n : ℝ) + 1 ≤ growthProduct n ^ 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have hfactor := one_add_recip_three_cube_lower ha
    have hfactor_nonneg : 0 ≤ (1 + 1 / (3 * ((n : ℝ) + 1))) ^ 3 := by
      positivity
    have hfirst := mul_le_mul_of_nonneg_right ih hfactor_nonneg
    have hsecond := mul_le_mul_of_nonneg_left hfactor (le_of_lt ha)
    have htelescoping : ((n : ℝ) + 1) * (1 + 1 / ((n : ℝ) + 1)) =
        (n : ℝ) + 2 := by
      field_simp
      ring
    rw [growthProduct_succ, mul_pow]
    push_cast
    linarith

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule20


/- BEGIN OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Recurrence -/
section AbstractModule21

namespace OAI

/-!
# The scalar simultaneous induction in Section 6

The two diagonal inequalities imply, simultaneously, lower bounds for the
limiting row slopes and for the diagonal profile.  All profile properties
needed for this argument are expressed as hypotheses below.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- One step of the Section 6 simultaneous induction, with a positive real
index. The proof uses the diagonal increment inequality to obtain the second
conclusion as well as the first. -/
theorem growthRecurrence_step_real
    {n Dprev Dnext gprev gnext Gprev : ℝ} (hn : 0 < n)
    (hupper : Dnext ≤ ((3 * (n + 1) - 1) / 2) * gnext)
    (hincrement : Dprev + gprev + gnext ≤ Dnext)
    (hgprev : Gprev ≤ gprev)
    (hDprev : ((3 * n - 1) / 2) * Gprev ≤ Dprev) :
    (1 + 1 / (3 * n)) * Gprev ≤ gnext ∧
      ((3 * (n + 1) - 1) / 2) * ((1 + 1 / (3 * n)) * Gprev) ≤ Dnext := by
  have hden : 0 < 3 * n := by positivity
  have hbound : (3 * n + 1) * Gprev ≤ (3 * n) * gnext := by
    nlinarith
  have hidentity : (1 + 1 / (3 * n)) * Gprev =
      ((3 * n + 1) * Gprev) / (3 * n) := by
    field_simp
  have hgnew : (1 + 1 / (3 * n)) * Gprev ≤ gnext := by
    rw [hidentity]
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hbound)
  refine ⟨hgnew, ?_⟩
  have hdiagonal : ((3 * (n + 1) - 1) / 2) *
      ((1 + 1 / (3 * n)) * Gprev) =
      ((3 * n - 1) / 2) * Gprev + Gprev +
        (1 + 1 / (3 * n)) * Gprev := by
    field_simp
    ring
  rw [hdiagonal]
  linarith

/-- The natural-number form of the scalar induction step, indexed by `n + 1`
so that no truncated subtraction occurs in the recurrence. -/
theorem growthRecurrence_step
    {n : ℕ} (hn : 1 ≤ n) {Dprev Dnext gprev gnext Gprev : ℝ}
    (hupper : Dnext ≤ ((3 * ((n : ℝ) + 1) - 1) / 2) * gnext)
    (hincrement : Dprev + gprev + gnext ≤ Dnext)
    (hgprev : Gprev ≤ gprev)
    (hDprev : ((3 * (n : ℝ) - 1) / 2) * Gprev ≤ Dprev) :
    (1 + 1 / (3 * (n : ℝ))) * Gprev ≤ gnext ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) *
        ((1 + 1 / (3 * (n : ℝ))) * Gprev) ≤ Dnext := by
  apply growthRecurrence_step_real
  · exact_mod_cast (show 0 < n by omega)
  · exact hupper
  · exact hincrement
  · exact hgprev
  · exact hDprev

/-- The simultaneous slope and diagonal estimates, conditional only on the
initial values, the recurrence for `G`, and the two diagonal inequalities. -/
theorem growthRecurrence_induction
    (D g G : ℕ → ℝ)
    (hGbase : G 1 = 1)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hGstep : ∀ n : ℕ, 1 ≤ n →
      G (n + 1) = (1 + 1 / (3 * (n : ℝ))) * G n)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → G n ≤ g n ∧ ((3 * (n : ℝ) - 1) / 2) * G n ≤ D n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [hGbase]
      exact ⟨hgbase, hDbase⟩
  | succ n hn ih =>
      have hu : D (n + 1) ≤
          ((3 * ((n : ℝ) + 1) - 1) / 2) * g (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hupper (n + 1) (by omega)
      have hs := growthRecurrence_step hn hu (hincrement n hn) ih.1 ih.2
      simpa only [hGstep n hn, Nat.cast_add, Nat.cast_one] using hs

/-- A zero-indexed version of `growthRecurrence_induction`, convenient when the
initial term of the comparison sequence is stored at index zero. -/
theorem growthRecurrence_induction_shifted
    (D g H : ℕ → ℝ)
    (hHbase : H 0 = 1)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hHstep : ∀ n : ℕ,
      H (n + 1) = (1 + 1 / (3 * ((n : ℝ) + 1))) * H n)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, H n ≤ g (n + 1) ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) * H n ≤ D (n + 1) := by
  intro n
  induction n with
  | zero =>
      norm_num [hHbase]
      exact ⟨hgbase, hDbase⟩
  | succ n ih =>
      have hn : 1 ≤ n + 1 := by omega
      have hu : D (n + 1 + 1) ≤
          ((3 * (((n + 1 : ℕ) : ℝ) + 1) - 1) / 2) * g (n + 1 + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hupper (n + 1 + 1) (by omega)
      have hp : ((3 * ((n + 1 : ℕ) : ℝ) - 1) / 2) * H n ≤ D (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using ih.2
      have hs := growthRecurrence_step hn hu (hincrement (n + 1) hn) ih.1 hp
      simpa only [hHstep, Nat.cast_add, Nat.cast_one] using hs

/-- The simultaneous bounds for the explicit comparison product from Section 6. -/
theorem growthProduct_le_slope_and_diagonal
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, growthProduct n ≤ g (n + 1) ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) * growthProduct n ≤ D (n + 1) := by
  apply growthRecurrence_induction_shifted D g growthProduct
    growthProduct_zero hgbase hDbase
  · intro n
    rw [growthProduct_succ, mul_comm]
  · exact hupper
  · exact hincrement

/-- Combining the scalar induction with the elementary product estimate gives
an exact fourth-power lower bound on the cube of each diagonal value. -/
theorem diagonal_fourth_power_lower
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1))
    (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 ≤ D (n + 1) ^ 3 := by
  have hdiag := (growthProduct_le_slope_and_diagonal D g hgbase hDbase
    hupper hincrement n).2
  have hpositive := growthProduct_pos n
  have hlinear : ((n : ℝ) + 1) * growthProduct n ≤ D (n + 1) := by
    have hcoeff : (n : ℝ) + 1 ≤ (3 * ((n : ℝ) + 1) - 1) / 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hpositive)).trans hdiag
  calc
    ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) := by ring
    _ ≤ ((n : ℝ) + 1) ^ 3 * growthProduct n ^ 3 :=
      mul_le_mul_of_nonneg_left (growthProduct_cube_lower n) (by positivity)
    _ = (((n : ℝ) + 1) * growthProduct n) ^ 3 := by ring
    _ ≤ D (n + 1) ^ 3 := pow_le_pow_left₀ (by positivity) hlinear 3

/-- The diagonal fourth-power lower bound using the paper's positive indices. -/
theorem diagonal_fourth_power_lower_of_one_le
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1))
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ 4 ≤ D n ^ 3 := by
  cases n with
  | zero => omega
  | succ n =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        diagonal_fourth_power_lower D g hgbase hDbase hupper hincrement n

end MatrixMultiplication.AuxiliarySeparation

end OAI

end AbstractModule21


end AllFieldsModule0
/- END all-fields module GenericAbstract -/

/- BEGIN all-fields module GenericRank -/
section AllFieldsModule1

set_option autoImplicit false

section RankModule0
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def contract (T : Tensor K X Y Z) [Fintype X] [Fintype Y]
    (a : X → K) (b : Y → K) : Z → K :=
  fun z => ∑ x, ∑ y, T x y z * a x * b y

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

@[simp] theorem directSum_matching {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (i : ι) (x : X) (y : Y) (z : Z) :
    directSum T (i, x) (i, y) (i, z) = T i x y z := by
  simp [directSum]

theorem directSum_zero_of_left_ne {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (x : ι × X) (y : ι × Y) (z : ι × Z)
    (h : x.1 ≠ y.1) : directSum T x y z = 0 := by
  simp [directSum, h]

@[simp] theorem rankAtMost_zero : RankAtMost (0 : Tensor K X Y Z) 0 := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  funext x y z
  simp

theorem rankOne_rankAtMost (a : X → K) (b : Y → K) (c : Z → K) :
    RankAtMost (rankOne a b c) 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => c, ?_⟩
  funext x y z
  simp

theorem RankAtMost.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => f (T x y z)) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => f (a i x), fun i y => f (b i y), fun i z => f (c i z), ?_⟩
  funext x y z
  simp [rankOne]

theorem RankAtMost.scale {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (u : K) :
    RankAtMost (fun x y z => u * T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => u * a i x, b, c, ?_⟩
  funext x y z
  simp [rankOne, Finset.mul_sum, mul_assoc]

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  refine ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i), ?_⟩
  funext x y z
  exact ((Fintype.equivFin ι).symm.sum_comp
    (fun i => rankOne (a i) (b i) (c i) x y z)).symm

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [rankOne, aa, bb, cc]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  calc
    (∑ x, ∑ y, ∑ z, ∑ i, A x' x * B y' y * C z' z * T i x y z) =
        ∑ x, ∑ y, ∑ i, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z :=
      Finset.sum_comm

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  classical
  funext x y z
  simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

end Pullback

end Tensor
end MatrixMultiplication.Foundation
end OAI

end RankModule0


section RankModule1
namespace OAI.MatrixMultiplication.Foundation.Tensor
variable {K : Type*} [CommSemiring K]
def matrixMultiplication (a b c : ℕ) :
    Tensor K (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
@[simp] theorem matrixMultiplication_matching (a b c : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    matrixMultiplication (K := K) a b c (i, j) (j, k) (k, i) = 1 := by
  simp [matrixMultiplication]
end OAI.MatrixMultiplication.Foundation.Tensor

end RankModule1


section RankModule2
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

theorem matrixMultiplication_eq_matrixCoefficients (a b c : ℕ) :
    matrixMultiplication (K := K) a b c = matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) := rfl

theorem contract_matrixCoefficients [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (left : A × B → K) (right : B × C → K) (i : A) (k : C) :
    contract (matrixCoefficients A B C) left right (k, i) =
      ∑ j, left (i, j) * right (j, k) := by
  simp [contract, matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]

theorem matrixCoefficients_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (x : (A × D) × (B × E)) (y : (B × E) × (C × F)) (z : (C × F) × (A × D)) :
    product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)
      ((x.1.1, x.2.1), (x.1.2, x.2.2))
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
      ((z.1.1, z.2.1), (z.1.2, z.2.2)) =
      matrixCoefficients (A × D) (B × E) (C × F) x y z := by
  simp only [product, matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

theorem matrixCoefficients_cyclic [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : B × C) (y : C × A) (z : A × B) :
    matrixCoefficients (K := K) A B C z x y = matrixCoefficients B C A x y z := by
  have h : (z.2 = x.1 ∧ x.2 = y.1 ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩
  simp only [matrixCoefficients, h]

theorem matrixCoefficients_rank_of_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r : ℕ}
    (hproduct : RankAtMost (product (matrixCoefficients (K := K) A B C)
      (matrixCoefficients D E F)) r) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) r := by
  have h := hproduct.pullback
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  have heq : pullback
      (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
      (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      (product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)) =
      matrixCoefficients (K := K) (A × D) (B × E) (C × F) := by
    funext x y z
    exact matrixCoefficients_product x y z
  rw [heq] at h
  exact h

theorem matrixCoefficients_product_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r s : ℕ}
    (hT : RankAtMost (matrixCoefficients (K := K) A B C) r)
    (hS : RankAtMost (matrixCoefficients (K := K) D E F) s) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) (r * s) :=
  matrixCoefficients_rank_of_product (hT.product hS)

theorem matrixCoefficients_power [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (n : ℕ) (x : (Fin n → A) × (Fin n → B))
    (y : (Fin n → B) × (Fin n → C)) (z : (Fin n → C) × (Fin n → A)) :
    Tensor.power (matrixCoefficients (K := K) A B C) n
      (fun i => (x.1 i, x.2 i)) (fun i => (y.1 i, y.2 i)) (fun i => (z.1 i, z.2 i)) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) x y z := by
  simp only [Tensor.power, matrixCoefficients, Fintype.prod_boole, forall_and, ← funext_iff]

theorem matrixCoefficients_cyclic_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {r : ℕ} (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) B C A) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  rw [← matrixCoefficients_cyclic (K := K) x y z]
  rw [congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

end Tensor
end MatrixMultiplication.Foundation

end OAI

end RankModule2


section RankModule3
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι K).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

theorem directSum_matrixCoefficients_rank_lower
    {Label A B C : Type*} [Fintype Label] [Fintype A] [Fintype C]
    [DecidableEq Label] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty B] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : Label => matrixCoefficients (K := K) A B C)) r) :
    Fintype.card Label * (Fintype.card C * Fintype.card A) ≤ r := by
  classical
  let b₀ : B := Classical.choice inferInstance
  have hminor : ∀ i j : Label × (C × A),
      directSum (fun _ : Label => matrixCoefficients (K := K) A B C)
        (i.1, (i.2.2, b₀)) (i.1, (b₀, i.2.1)) j = if i = j then 1 else 0 := by
    intro i j
    simp only [directSum, matrixCoefficients]
    split_ifs <;> simp_all [Prod.ext_iff]
  have hlower := h.card_le_of_identity
    (fun i : Label × (C × A) => (i.1, (i.2.2, b₀)))
    (fun i : Label × (C × A) => (i.1, (b₀, i.2.1)))
    (fun i : Label × (C × A) => i) hminor
  simpa only [Fintype.card_prod] using hlower

theorem directSum_square_rank_lower (k n r : ℕ) (hn : 0 < n)
    (h : RankAtMost (directSum (fun _ : Fin k =>
      matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) r) :
    k * n ^ 2 ≤ r := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin, pow_two] using directSum_matrixCoefficients_rank_lower h

end Tensor
end MatrixMultiplication.Foundation

end

end OAI

end RankModule3


section RankModule4
namespace OAI

/-!
# Exact tensor rank and its matrix multiplication exponent

The rank is the least size of an exact decomposition into simple tensors. The
exponent is the infimum of the finite matrix multiplication rank ratios from
Section 3; no attainment of this real infimum is assumed.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]

/-- Every finite coefficient tensor has a finite exact rank decomposition. -/
theorem exists_rankAtMost {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y × Z → X → K := fun p x => if x = p.1 then T p.1 p.2.1 p.2.2 else 0
  let b : X × Y × Z → Y → K := fun p y => if y = p.2.1 then 1 else 0
  let c : X × Y × Z → Z → K := fun p z => if z = p.2.2 then 1 else 0
  refine ⟨Fintype.card (X × Y × Z), ?_⟩
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- Exact rank of a finite coefficient tensor. -/
def exactRank {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

/-- The least exact rank comes with an actual rank decomposition. -/
theorem exactRank_spec {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : Tensor.RankAtMost T (exactRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

/-- Every exact decomposition bounds the least rank. -/
theorem exactRank_le {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- Exact rank cannot increase under a linear restriction. -/
theorem exactRank_restrict_le {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : exactRank (Tensor.restrict A B C T) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).restrict A B C)

/-- Independent bijections of the three coordinate sets preserve exact rank. -/
theorem exactRank_reindex {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le ((exactRank_spec T).pullback ex ey ez))
  have h := exactRank_le
    ((exactRank_spec (Tensor.pullback ex ey ez T)).pullback ex.symm ey.symm ez.symm)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- Tensor product decompositions give the usual submultiplicative rank bound. -/
theorem exactRank_product_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    exactRank (Tensor.product T S) ≤ exactRank T * exactRank S :=
  exactRank_le ((exactRank_spec T).product (exactRank_spec S))

/-- Exact rank of the square matrix multiplication tensor. -/
def exactMatrixRank (K : Type*) [Field K] (n : ℕ) : ℕ := exactRank (Tensor.matrixMultiplication (K := K) n n n)

theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost (Tensor.matrixMultiplication (K := K) n n n) ((exactMatrixRank K) n) :=
  exactRank_spec _

/-- The ordinary scalar multiplication algorithm uses `n³` simple tensors. -/
theorem matrixMultiplication_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (Tensor.matrixMultiplication (K := K) n n n) (n ^ 3) := by
  classical
  let a : Fin n × Fin n × Fin n → Fin n × Fin n → K :=
    fun p x => if x = (p.1, p.2.1) then 1 else 0
  let b : Fin n × Fin n × Fin n → Fin n × Fin n → K :=
    fun p y => if y = (p.2.1, p.2.2) then 1 else 0
  let c : Fin n × Fin n × Fin n → Fin n × Fin n → K :=
    fun p z => if z = (p.2.2, p.1) then 1 else 0
  have heq : Tensor.matrixMultiplication (K := K) n n n =
      fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Tensor.matrixMultiplication,
      Fintype.sum_prod_type, Prod.ext_iff, ite_and, mul_ite]
    split_ifs <;> simp_all
  rw [heq]
  convert Tensor.rankAtMost_sum_rankOne a b c using 1
  simp [Fintype.card_prod, pow_succ, Nat.mul_assoc]

theorem exactMatrixRank_upper (n : ℕ) : (exactMatrixRank K) n ≤ n ^ 3 :=
  exactRank_le ((matrixMultiplication_rankAtMost_cubic (K := K)) n)

/-- An identity minor of the output flattening forces the quadratic lower bound. -/
theorem matrixMultiplication_rank_lower {n R : ℕ} (hn : 0 < n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication (K := K) n n n) R) : n ^ 2 ≤ R := by
  let j : Fin n := ⟨0, hn⟩
  have hminor : ∀ i k : Fin n × Fin n,
      Tensor.matrixMultiplication (K := K) n n n (i.2, j) (j, i.1) k =
        if i = k then 1 else 0 := by
    intro i k
    simp [Tensor.matrixMultiplication, Prod.ext_iff, eq_comm]
  have h := hRank.card_le_of_identity
    (fun i : Fin n × Fin n => (i.2, j))
    (fun i : Fin n × Fin n => (j, i.1)) id hminor
  simpa [Fintype.card_prod, pow_two] using h

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ (exactMatrixRank K) n :=
  (matrixMultiplication_rank_lower (K := K)) hn ((exactMatrixRank_spec (K := K)) n)

theorem exactMatrixRank_pos {n : ℕ} (hn : 0 < n) : 0 < (exactMatrixRank K) n :=
  lt_of_lt_of_le (pow_pos hn 2) ((exactMatrixRank_lower (K := K)) hn)

@[simp] theorem exactMatrixRank_zero : (exactMatrixRank K) 0 = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using (exactMatrixRank_upper (K := K)) 0)

@[simp] theorem exactMatrixRank_one : (exactMatrixRank K) 1 = 1 := by
  apply le_antisymm
  · simpa using (exactMatrixRank_upper (K := K)) 1
  · simpa using (exactMatrixRank_lower (K := K) (n := 1)) zero_lt_one

/-- The set of finite exact-rank exponents in the definition of `ν`. -/
def exactRankExponentSet (K : Type*) [Field K] : Set ℝ :=
  {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n ((exactMatrixRank K) n)}

/-- The exact-rank exponent `ν = inf_{n ≥ 2} log(R(Tₙ))/log(n)`. -/
def exactRankExponent (K : Type*) [Field K] : ℝ := sInf (exactRankExponentSet K)

theorem exactRankExponentSet_nonempty : (exactRankExponentSet K).Nonempty :=
  ⟨Real.logb 2 ((exactMatrixRank K) 2), 2, le_rfl, rfl⟩

theorem exactMatrixRank_logb_lower {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ Real.logb n ((exactMatrixRank K) n) := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < ((exactMatrixRank K) n : ℝ) := by
    exact_mod_cast (exactMatrixRank_pos (K := K)) (show 0 < n by omega)
  apply (Real.le_logb_iff_rpow_le hn1 hr).mpr
  rw [Real.rpow_two]
  exact_mod_cast (exactMatrixRank_lower (K := K)) (show 0 < n by omega)

theorem exactMatrixRank_logb_upper {n : ℕ} (hn : 2 ≤ n) :
    Real.logb n ((exactMatrixRank K) n) ≤ 3 := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < ((exactMatrixRank K) n : ℝ) := by
    exact_mod_cast (exactMatrixRank_pos (K := K)) (show 0 < n by omega)
  apply (Real.logb_le_iff_le_rpow hn1 hr).mpr
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  exact_mod_cast (exactMatrixRank_upper (K := K)) n

theorem exactRankExponentSet_bddBelow : BddBelow (exactRankExponentSet K) := by
  refine ⟨2, ?_⟩
  rintro τ ⟨n, hn, rfl⟩
  exact (exactMatrixRank_logb_lower (K := K)) hn

theorem exactRankExponent_lower : 2 ≤ (exactRankExponent K) :=
  le_csInf (exactRankExponentSet_nonempty (K := K)) (by
    rintro τ ⟨n, hn, rfl⟩
    exact (exactMatrixRank_logb_lower (K := K)) hn)

theorem exactRankExponent_le_logb {n : ℕ} (hn : 2 ≤ n) :
    (exactRankExponent K) ≤ Real.logb n ((exactMatrixRank K) n) :=
  csInf_le (exactRankExponentSet_bddBelow (K := K)) ⟨n, hn, rfl⟩

theorem exactRankExponent_upper : (exactRankExponent K) ≤ 3 :=
  ((exactRankExponent_le_logb (K := K) (n := 2)) le_rfl).trans
    ((exactMatrixRank_logb_upper (K := K) (n := 2)) le_rfl)

/-- Each matrix multiplication tensor has rank at least `n^ν`. -/
theorem exactMatrixRank_rpow_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ (exactRankExponent K) ≤ (exactMatrixRank K) n := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < ((exactMatrixRank K) n : ℝ) := by
    exact_mod_cast (exactMatrixRank_pos (K := K)) (show 0 < n by omega)
  exact (Real.le_logb_iff_rpow_le hn1 hr).mp ((exactRankExponent_le_logb (K := K)) hn)

/-- The rank lower bound includes the one-dimensional boundary case. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (exactRankExponent K) ≤ (exactMatrixRank K) n := by
  by_cases hn2 : 2 ≤ n
  · exact (exactMatrixRank_rpow_lower (K := K)) hn2
  · have hn1 : n = 1 := by omega
    simp [hn1]

/-- A strict upper bound for the infimum is witnessed by an actual finite block. -/
theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : (exactRankExponent K) < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ ((exactMatrixRank K) n : ℝ) < (n : ℝ) ^ τ := by
  obtain ⟨σ, ⟨n, hn, rfl⟩, hσ⟩ :=
    exists_lt_of_csInf_lt (exactRankExponentSet_nonempty (K := K)) hτ
  refine ⟨n, hn, ?_⟩
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < ((exactMatrixRank K) n : ℝ) := by
    exact_mod_cast (exactMatrixRank_pos (K := K)) (show 0 < n by omega)
  exact (Real.logb_lt_iff_lt_rpow hn1 hr).mp hσ

/-- Finite decompositions approximate the exact-rank exponent with any positive slack. -/
theorem exists_rankAtMost_of_exponent_slack {ε : ℝ} (hε : 0 < ε) :
    ∃ n R : ℕ, 2 ≤ n ∧ Tensor.RankAtMost (Tensor.matrixMultiplication (K := K) n n n) R ∧
      (R : ℝ) ≤ (n : ℝ) ^ ((exactRankExponent K) + ε) := by
  obtain ⟨n, hn, hR⟩ := (exists_exactMatrixRank_lt_rpow (K := K)) (lt_add_of_pos_right _ hε)
  exact ⟨n, (exactMatrixRank K) n, hn, (exactMatrixRank_spec (K := K)) n, hR.le⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end RankModule4



end AllFieldsModule1
/- END all-fields module GenericRank -/

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

private theorem sum_three_mul [Fintype X] [Fintype Y] [Fintype Z]
    (a : X → K) (b : Y → K) (c : Z → K) (t : K) :
    (∑ x, a x) * (∑ y, b y) * (∑ z, c z) * t =
      ∑ x, ∑ y, ∑ z, a x * b y * c z * t := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]

private theorem sum_six_comm [Fintype X] [Fintype Y] [Fintype Z]
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

private theorem sum_interleaved_triples {U V W : Type*}
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

/-- An empty left summand disappears under its canonical coordinates. -/
theorem sumTensor_empty_left [IsEmpty X] [IsEmpty Y] [IsEmpty Z]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.emptySum X U).symm (Equiv.emptySum Y V).symm
      (Equiv.emptySum Z W).symm (sumTensor T S) = S := by
  rfl

/-- Tensor product distributes over the first binary sum by coordinate
permutation. -/
theorem sumTensor_product (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.sumProdDistrib X U A).symm
      (Equiv.sumProdDistrib Y V B).symm (Equiv.sumProdDistrib Z W C).symm
      (Tensor.product (sumTensor T S) R) =
      sumTensor (Tensor.product T R) (Tensor.product S R) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, sumTensor]

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

/-- Scalar multiplication by one is the left unit for tensor product. -/
theorem tensorProduct_one_left (T : Tensor K X Y Z) :
    Tensor.pullback (Equiv.punitProd X).symm (Equiv.punitProd Y).symm
      (Equiv.punitProd Z).symm
      (Tensor.product (fun (_ _ _ : PUnit) => (1 : K)) T) = T := by
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

@[simp] theorem tensorClass_le_iff (T S : (FiniteTensor K)) :
    tensorClass T ≤ tensorClass S ↔ T ≤ S := Iff.rfl

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

theorem classOf_eq_of_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (h : Tensor.pullback ex ey ez S = T) : classOf T = classOf S :=
  (congrArg classOf h).symm.trans (classOf_reindex S ex ey ez)

@[simp] theorem classOf_coeff (T : (FiniteTensor K)) : classOf T.coeff = tensorClass T := by
  apply (tensorClass_eq_iff _ _).mpr
  exact ⟨IsRestriction.pullback T.coeff _ _ _, IsRestriction.of_reindex T.coeff _ _ _⟩

instance : Mul (TensorClass K) where
  mul := Quotient.map₂ FiniteTensor.product (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.product_mono hT.1 hS.1,
      FiniteTensor.product_mono hT.2 hS.2⟩)

instance : Add (TensorClass K) where
  add := Quotient.map₂ FiniteTensor.sum (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.sum_mono hT.1 hS.1, FiniteTensor.sum_mono hT.2 hS.2⟩)

@[simp] theorem tensorClass_product (T S : (FiniteTensor K)) :
    tensorClass T * tensorClass S = tensorClass (FiniteTensor.product T S) := rfl

@[simp] theorem tensorClass_sum (T S : (FiniteTensor K)) :
    tensorClass T + tensorClass S = tensorClass (FiniteTensor.sum T S) := rfl

theorem classOf_product {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S := by
  symm
  exact classOf_reindex (Tensor.product T S)
    (Equiv.prodCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.prodCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.prodCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)

theorem classOf_sum {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (sumTensor T S) = classOf T + classOf S := by
  symm
  have h := classOf_reindex (sumTensor T S)
    (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
  change classOf (sumTensor (FiniteTensor.ofTensor T).coeff
    (FiniteTensor.ofTensor S).coeff) = _
  have heq : sumTensor (FiniteTensor.ofTensor T).coeff (FiniteTensor.ofTensor S).coeff =
      Tensor.pullback
        (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
        (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
        (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
        (sumTensor T S) := by
    funext x y z
    cases x <;> cases y <;> cases z <;> rfl
  rw [heq]
  exact h

instance : Zero (TensorClass K) := ⟨classOf (0 : Tensor K Empty Empty Empty)⟩
instance : One (TensorClass K) := ⟨classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))⟩

theorem classOf_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    classOf (0 : Tensor K X Y Z) = 0 :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.zero _, IsRestriction.zero _⟩

private theorem class_add_assoc (a b c : (TensorClass K)) : (a + b) + c = a + (b + c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a + tensorClass b) + tensorClass c =
    tensorClass a + (tensorClass b + tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_assoc a.coeff b.coeff c.coeff)

private theorem class_add_comm (a b : (TensorClass K)) : a + b = b + a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a + tensorClass b = tensorClass b + tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_comm a.coeff b.coeff)

private theorem class_add_zero (a : (TensorClass K)) : a + 0 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a + 0 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff + classOf (0 : Tensor K Empty Empty Empty) = classOf a.coeff
  rw [← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (sumTensor_empty_right a.coeff
    (0 : Tensor K Empty Empty Empty))).symm

private theorem class_zero_add (a : (TensorClass K)) : 0 + a = a :=
  (class_add_comm 0 a).trans (class_add_zero a)

private theorem class_mul_assoc (a b c : (TensorClass K)) : (a * b) * c = a * (b * c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a * tensorClass b) * tensorClass c =
    tensorClass a * (tensorClass b * tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_assoc a.coeff b.coeff c.coeff)

private theorem class_mul_comm (a b : (TensorClass K)) : a * b = b * a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a * tensorClass b = tensorClass b * tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_comm a.coeff b.coeff)

private theorem class_mul_one (a : (TensorClass K)) : a * 1 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 1 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (fun (_ _ _ : PUnit.{1}) => (1 : K)) = classOf a.coeff
  rw [← classOf_product]
  exact (classOf_eq_of_reindex _ _ _ (tensorProduct_one_right a.coeff)).symm

private theorem class_one_mul (a : (TensorClass K)) : 1 * a = a :=
  (class_mul_comm 1 a).trans (class_mul_one a)

private theorem class_mul_zero (a : (TensorClass K)) : a * 0 = 0 := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 0 = 0
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (0 : Tensor K Empty Empty Empty) = 0
  rw [← classOf_product]
  have heq : Tensor.product a.coeff (0 : Tensor K Empty Empty Empty) = 0 := by
    funext x y z
    simp [Tensor.product]
  rw [heq, classOf_zero]

private theorem class_zero_mul (a : (TensorClass K)) : 0 * a = 0 :=
  (class_mul_comm 0 a).trans (class_mul_zero a)

private theorem class_left_distrib (a b c : (TensorClass K)) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change tensorClass a * (tensorClass b + tensorClass c) =
    tensorClass a * tensorClass b + tensorClass a * tensorClass c
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product, ← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (product_sumTensor a.coeff b.coeff c.coeff)).symm

private theorem class_right_distrib (a b c : (TensorClass K)) : (a + b) * c = a * c + b * c := by
  rw [class_mul_comm, class_left_distrib, class_mul_comm c a, class_mul_comm c b]

instance : CommSemiring (TensorClass K) where
  add_assoc := class_add_assoc
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero := class_add_zero
  nsmul := nsmulRec
  mul_assoc := class_mul_assoc
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one := class_mul_one
  zero_mul := class_zero_mul
  mul_zero := class_mul_zero
  left_distrib := class_left_distrib
  right_distrib := class_right_distrib

theorem mul_mono {T T' S S' : (TensorClass K)} (hT : T ≤ T') (hS : S ≤ S') :
    T * S ≤ T' * S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.product_mono hT hS

theorem add_mono {T T' S S' : (TensorClass K)} (hT : T ≤ T') (hS : S ≤ S') :
    T + S ≤ T' + S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.sum_mono hT hS

/-- Every tensor class is nonnegative in the restriction order. -/
theorem zero_le (T : (TensorClass K)) : 0 ≤ T := by
  induction T using Quotient.inductionOn with | h T =>
  change (0 : (TensorClass K)) ≤ tensorClass T
  rw [← classOf_coeff T]
  exact (classOf_le_iff _ _).mpr (IsRestriction.zero T.coeff)

instance : OrderBot (TensorClass K) where
  bot := 0
  bot_le := zero_le

instance : IsOrderedAddMonoid (TensorClass K) where
  add_le_add_left _ _ h _c := add_mono h le_rfl

instance : IsOrderedMonoid (TensorClass K) where
  mul_le_mul_left _ _ h _c := mul_mono h le_rfl

instance : IsOrderedRing (TensorClass K) where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    exact mul_mono le_rfl hbc
  mul_le_mul_of_nonneg_right := by
    intro a ha b c hbc
    exact mul_mono hbc le_rfl

/-- Exact rank descends to mutual-restriction classes. -/
def rank : (TensorClass K) → ℕ := Quotient.lift (fun T : (FiniteTensor K) => exactRank T.coeff)
  (by
    intro T S h
    exact le_antisymm (IsRestriction.rank_le h.1) (IsRestriction.rank_le h.2))

@[simp] theorem rank_tensorClass (T : (FiniteTensor K)) :
    rank (tensorClass T) = exactRank T.coeff := rfl

@[simp] theorem rank_classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : rank (classOf T) = exactRank T :=
  exactRank_reindex T _ _ _

theorem rank_mono {T S : (TensorClass K)} (h : T ≤ S) : rank T ≤ rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  exact IsRestriction.rank_le h

theorem rank_mul_le (T S : (TensorClass K)) : rank (T * S) ≤ rank T * rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change rank (tensorClass T * tensorClass S) ≤ rank (tensorClass T) * rank (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_product]
  simp only [rank_classOf]
  exact exactRank_product_le _ _

/-- Square matrix multiplication as an element of the tensor semiring. -/
def matrixClass (n : ℕ) : (TensorClass K) := classOf (Tensor.matrixMultiplication n n n)

@[simp] theorem rank_matrixClass (n : ℕ) : rank ((matrixClass (K := K)) n) = exactMatrixRank K n :=
  rank_classOf _

private theorem classOf_matrixCoefficients_equiv {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (e : A ≃ B) :
    classOf (Tensor.matrixCoefficients (K := K) A A A) =
      classOf (Tensor.matrixCoefficients (K := K) B B B) := by
  apply classOf_eq_of_reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e)
    (Equiv.prodCongr e e)
  funext x y z
  simp [Tensor.pullback, Tensor.matrixCoefficients, e.injective.eq_iff]

theorem matrixClass_mul (m n : ℕ) : (matrixClass (K := K)) (m * n) = (matrixClass (K := K)) m * (matrixClass (K := K)) n := by
  let e : Fin (m * n) ≃ Fin m × Fin n := Fintype.equivOfCardEq (by simp)
  have h := classOf_matrixCoefficients_equiv (K := K) e
  change (matrixClass (K := K)) (m * n) = classOf (Tensor.matrixCoefficients (K := K)
    (Fin m × Fin n) (Fin m × Fin n) (Fin m × Fin n)) at h
  rw [h]
  change _ = classOf (Tensor.matrixCoefficients (K := K) (Fin m) (Fin m) (Fin m)) *
    classOf (Tensor.matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))
  rw [← classOf_product]
  apply classOf_eq_of_reindex (Equiv.prodProdProdComm _ _ _ _)
    (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
  funext x y z
  exact Tensor.matrixCoefficients_product x y z

@[simp] theorem matrixClass_one : (matrixClass (K := K)) 1 = 1 := by
  let e : Fin 1 × Fin 1 ≃ PUnit.{1} := Fintype.equivOfCardEq (by simp)
  apply classOf_eq_of_reindex e e e
  funext x y z
  have hxy : x.2 = y.1 := Subsingleton.elim _ _
  have hyz : y.2 = z.1 := Subsingleton.elim _ _
  have hzx : z.2 = x.1 := Subsingleton.elim _ _
  simp [Tensor.pullback, Tensor.matrixMultiplication, hxy, hyz, hzx]

theorem matrixClass_pow (m j : ℕ) : (matrixClass (K := K)) (m ^ j) = (matrixClass (K := K)) m ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, matrixClass_mul, ih, pow_succ]

theorem classOf_eq_zero_iff {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : classOf T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hr : IsRestriction T (0 : Tensor K Empty Empty Empty) :=
      ((classOf_eq_iff _ _).mp h).1
    exact hr.eq_zero_of_zero
  · rintro rfl
    exact classOf_zero

instance : Nontrivial (TensorClass K) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have heq : (fun (_ _ _ : PUnit.{1}) => (1 : K)) = 0 :=
    (classOf_eq_zero_iff _).mp h
  have := congrFun (congrFun (congrFun heq PUnit.unit) PUnit.unit) PUnit.unit
  exact one_ne_zero this

/-- A nonzero tensor has a nonzero coefficient, which restricts to scalar multiplication. -/
theorem one_le_classOf_of_ne_zero {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] {T : Tensor K X Y Z} (hT : T ≠ 0) :
    1 ≤ classOf T := by
  classical
  have hex : ∃ x y z, T x y z ≠ 0 := by
    by_contra! h
    apply hT
    funext x y z
    exact h x y z
  obtain ⟨x, y, z, hxyz⟩ := hex
  apply (classOf_le_iff _ _).mpr
  refine ⟨(fun _ u => if u = x then (T x y z)⁻¹ else 0),
    (fun _ v => if v = y then 1 else 0),
    (fun _ w => if w = z then 1 else 0), ?_⟩
  funext a b c
  simp [Tensor.restrict, ite_mul, mul_ite, hxyz]

/-- Every nonzero class dominates the multiplicative unit. -/
theorem one_le_of_ne_zero {T : (TensorClass K)} (hT : T ≠ 0) : 1 ≤ T := by
  induction T using Quotient.inductionOn with | h T =>
  change tensorClass T ≠ 0 at hT
  change 1 ≤ tensorClass T
  rw [← classOf_coeff T] at hT ⊢
  exact one_le_classOf_of_ne_zero (fun h => hT ((classOf_eq_zero_iff _).mpr h))

end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end OAI



end AllFieldsModule2
/- END all-fields module GenericSemiring -/

/- BEGIN all-fields module GenericCharacterCore -/
section AllFieldsModule3



namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section DependentSum

variable {K S : Type*} [CommSemiring K] [DecidableEq S]
variable {X Y Z : S → Type*}

def dependentDirectSum (T : ∀ s, Tensor K (X s) (Y s) (Z s)) :
    Tensor K (Σ s, X s) (Σ s, Y s) (Σ s, Z s) :=
  fun x y z =>
    if hxy : y.1 = x.1 then
      if hxz : z.1 = x.1 then T x.1 x.2 (hxy ▸ y.2) (hxz ▸ z.2)
      else 0
    else 0

@[simp] theorem dependentDirectSum_matching
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (s : S) (x : X s) (y : Y s) (z : Z s) :
    dependentDirectSum T ⟨s, x⟩ ⟨s, y⟩ ⟨s, z⟩ = T s x y z := by
  simp [dependentDirectSum]

theorem dependentDirectSum_zero_of_left_ne
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (x : Σ s, X s) (y : Σ s, Y s) (z : Σ s, Z s)
    (h : x.1 ≠ y.1) : dependentDirectSum T x y z = 0 := by
  simp [dependentDirectSum, Ne.symm h]

def directSumCoordinateEquiv {A : Type*} (e : ∀ s, X s ≃ A) :
    (Σ s, X s) ≃ S × A where
  toFun x := (x.1, e x.1 x.2)
  invFun x := ⟨x.1, (e x.1).symm x.2⟩
  left_inv := by
    rintro ⟨s, x⟩
    simp
  right_inv := by
    rintro ⟨s, x⟩
    simp

theorem dependentDirectSum_reindex {A B C : Type*}
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (ex : ∀ s, X s ≃ A) (ey : ∀ s, Y s ≃ B) (ez : ∀ s, Z s ≃ C) :
    pullback (directSumCoordinateEquiv ex).symm
      (directSumCoordinateEquiv ey).symm (directSumCoordinateEquiv ez).symm
      (dependentDirectSum T) =
      directSum (fun s => pullback (ex s).symm (ey s).symm (ez s).symm (T s)) := by
  funext x y z
  rcases x with ⟨s, x⟩
  rcases y with ⟨t, y⟩
  rcases z with ⟨v, z⟩
  by_cases ht : t = s
  · subst t
    by_cases hv : v = s
    · subst v
      simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum]
    · simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum,
        hv, Ne.symm hv]
  · simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum,
      ht, Ne.symm ht]

end DependentSum
end Tensor


end MatrixMultiplication.Foundation
end OAI


/- Character/Basic -/
section CharacterModule0

namespace OAI

/-!
# Characters of finite complex tensors

The tensor operations in this file are the coefficient operations from
`MatrixMultiplication.Foundation.Tensor`. A character is an assumption on those
operations, not an assertion that a character exists. Restriction monotonicity
forces invariance under independent invertible changes of coordinates, so this
interface descends to the mutual-restriction classes of Section 3 of the paper.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]

/-- The scalar multiplication tensor, the multiplicative unit. -/
def unitTensor : Tensor K PUnit PUnit PUnit := fun _ _ _ => 1

/-- The direct sum of `r` scalar multiplication tensors, in diagonal coordinates. -/
def scalarTensor (r : ℕ) : Tensor K (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ i = k then 1 else 0

/-- A normalized, additive, multiplicative, restriction-monotone tensor valuation.

Index types vary over all finite types in `Type`. No character-existence result is
included among the fields or claimed by this definition.
-/
structure Character (K : Type*) [Field K] where
  value : {X Y Z : Type} → [Fintype X] → [Fintype Y] → [Fintype Z] →
    Tensor K X Y Z → ℝ
  nonneg : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z), 0 ≤ value T
  map_zero : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z],
    value (0 : Tensor K X Y Z) = 0
  map_one : value unitTensor = 1
  map_directSum : ∀ {ι X Y Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z] (T : ι → Tensor K X Y Z),
    value (Tensor.directSum T) = ∑ i, value (T i)
  map_product : ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W),
    value (Tensor.product T S) = value T * value S
  monotone : ∀ {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K)
    (B : Y' → Y → K) (C : Z' → Z → K),
    value (Tensor.restrict A B C T) ≤ value T

namespace Character

variable (χ : (Character K))
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Coordinate pullbacks are restrictions. -/
theorem value_pullback_le (T : Tensor K X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by
  classical
  rw [Tensor.pullback_eq_restrict]
  exact χ.monotone T _ _ _

/-- Independent coordinate bijections preserve a character. -/
theorem value_reindex (T : Tensor K X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  apply le_antisymm (χ.value_pullback_le T ex ey ez)
  have h := χ.value_pullback_le (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm
      (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- The character has the same value on mutually restricting tensors. -/
theorem value_eq_of_mutual_restriction (T : Tensor K X Y Z) (S : Tensor K X' Y' Z')
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (A' : X → X' → K) (B' : Y → Y' → K) (C' : Z → Z' → K)
    (hS : S = Tensor.restrict A B C T) (hT : T = Tensor.restrict A' B' C' S) :
    χ.value T = χ.value S := by
  apply le_antisymm
  · calc
      χ.value T = χ.value (Tensor.restrict A' B' C' S) := congrArg χ.value hT
      _ ≤ χ.value S := χ.monotone S A' B' C'
  · calc
      χ.value S = χ.value (Tensor.restrict A B C T) := congrArg χ.value hS
      _ ≤ χ.value T := χ.monotone T A B C

/-- An integer scalar tensor has its expected character value. -/
@[simp] theorem value_scalarTensor (r : ℕ) : χ.value (scalarTensor r) = r := by
  let T : Fin r → Tensor K PUnit PUnit PUnit := fun _ => unitTensor
  have heq : Tensor.pullback (Equiv.prodPUnit (Fin r)).symm
      (Equiv.prodPUnit (Fin r)).symm (Equiv.prodPUnit (Fin r)).symm
      (Tensor.directSum T) = scalarTensor r := by
    rfl
  rw [← heq, χ.value_reindex, χ.map_directSum]
  simp [T, χ.map_one]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Restricting a diagonal scalar tensor realizes a rank decomposition. -/
theorem restrict_scalarTensor (r : ℕ) (a : Fin r → X → K)
    (b : Fin r → Y → K) (c : Fin r → Z → K) :
    Tensor.restrict (fun x i => a i x) (fun y i => b i y) (fun z i => c i z)
      (scalarTensor r) =
      fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
  classical
  funext x y z
  simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]

/-- (Character K) values are bounded by every exact rank decomposition size. -/
theorem value_le_rank {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.value T ≤ r := by
  rcases h with ⟨a, b, c, rfl⟩
  rw [← restrict_scalarTensor r a b c]
  exact (χ.monotone (scalarTensor r) _ _ _).trans_eq (χ.value_scalarTensor r)

/-- Every nonzero tensor restricts to the scalar multiplication tensor. -/
theorem one_le_value {T : Tensor K X Y Z} (hT : T ≠ 0) : 1 ≤ χ.value T := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hT
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hy
  change T x y z ≠ 0 at hz
  let A : PUnit → X → K := fun _ x' => if x' = x then (T x y z)⁻¹ else 0
  let B : PUnit → Y → K := fun _ y' => if y' = y then 1 else 0
  let C : PUnit → Z → K := fun _ z' => if z' = z then 1 else 0
  have heq : Tensor.restrict A B C T = unitTensor := by
    funext i j k
    simp [Tensor.restrict, A, B, C, unitTensor, ite_mul, mul_ite, hz]
  simpa only [heq, χ.map_one] using χ.monotone T A B C

/-- Normalization and restriction monotonicity make the character faithful. -/
@[simp] theorem value_eq_zero_iff (T : Tensor K X Y Z) : χ.value T = 0 ↔ T = 0 := by
  constructor
  · intro h
    by_contra hT
    have hle := χ.one_le_value hT
    rw [h] at hle
    exact (not_le_of_gt zero_lt_one) hle
  · rintro rfl
    exact χ.map_zero

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end CharacterModule0


/- Tensor/CharacterBounds -/
section CharacterModule1

namespace OAI

/-!
# (Character K) values on powers and varying-dimension direct sums

These are consequences of the normalized restriction-monotone character
interface. Coordinate changes preserve values; permuting the three tensor
legs need not preserve an individual character.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {K : Type*} [Field K]

variable (χ : (Character K))

section Embeddings

variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']

/-- Extending finite coordinates by zero does not change a character value. -/
theorem value_extendByZero (T : Tensor K X Y Z)
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz) :
    χ.value (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) = χ.value T := by
  classical
  apply le_antisymm (χ.monotone T _ _ _)
  have h := χ.value_pullback_le (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) fx fy fz
  have heq : Tensor.pullback fx fy fz (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) = T := by
    funext x y z
    simp [Tensor.pullback, Tensor.restrict, hx.eq_iff, hy.eq_iff, hz.eq_iff,
      ite_mul, mul_ite]
  simpa only [heq] using h

end Embeddings

section Powers

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Tensor powers turn a character value into an ordinary natural power. -/
@[simp] theorem value_power (T : Tensor K X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n := by
  induction n with
  | zero =>
      have heq : Tensor.power T 0 = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) unitTensor := by
        funext x y z
        simp [Tensor.power, Tensor.pullback, unitTensor]
      rw [heq, χ.value_reindex, χ.map_one, pow_zero]
  | succ n ih =>
      have heq : Tensor.power T (n + 1) = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product T (Tensor.power T n)) := by
        funext x y z
        simp [Tensor.power, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, pow_succ, mul_comm]

/-- Full independent copies contribute their exact multiplicity. -/
theorem value_copies (T : Tensor K X Y Z) (r : ℕ) :
    χ.value (Tensor.directSum (fun _ : Fin r => T)) = r * χ.value T := by
  rw [χ.map_directSum]
  simp

/-- The character cost of an exact number of full copies of a tensor power. -/
theorem value_power_copies (T : Tensor K X Y Z) (r n : ℕ) :
    χ.value (Tensor.directSum (fun _ : Fin r => Tensor.power T n)) =
      r * χ.value T ^ n := by
  rw [χ.value_copies, χ.value_power]

end Powers

section DependentDirectSum

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X Y Z : ι → Type}
variable [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

/-- A branch extended to the common ambient sigma coordinate spaces. -/
def paddedBranch (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι) :
    Tensor K (Σ i, X i) (Σ i, Y i) (Σ i, Z i) :=
  Tensor.restrict
    (fun x a => if Sigma.mk i a = x then 1 else 0)
    (fun y b => if Sigma.mk i b = y then 1 else 0)
    (fun z c => if Sigma.mk i c = z then 1 else 0) (T i)

@[simp] theorem value_paddedBranch
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι) :
    χ.value (paddedBranch T i) = χ.value (T i) := by
  simpa only [paddedBranch] using
    χ.value_extendByZero (T i) (Sigma.mk i) (Sigma.mk i) (Sigma.mk i)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)

omit [Fintype ι] in
@[simp] theorem paddedBranch_matching
    (T : ∀ i, Tensor K (X i) (Y i) (Z i))
    (i : ι) (x : X i) (y : Y i) (z : Z i) :
    paddedBranch T i ⟨i, x⟩ ⟨i, y⟩ ⟨i, z⟩ = T i x y z := by
  simp [paddedBranch, Tensor.restrict, ite_mul, mul_ite]

omit [Fintype ι] in
theorem paddedBranch_zero_left
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hx : x.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ a : X i, Sigma.mk i a ≠ x :=
    fun a h => hx (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

omit [Fintype ι] in
theorem paddedBranch_zero_middle
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hy : y.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ b : Y i, Sigma.mk i b ≠ y :=
    fun b h => hy (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

omit [Fintype ι] in
theorem paddedBranch_zero_right
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hz : z.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ c : Z i, Sigma.mk i c ≠ z :=
    fun c h => hz (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

/-- Redundant outer labels give a zero extension of the varying-dimension sum. -/
theorem directSum_paddedBranch
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    Tensor.directSum (paddedBranch T) = Tensor.restrict
      (fun (x' : ι × (Σ i, X i)) x => if (x.1, x) = x' then 1 else 0)
      (fun (y' : ι × (Σ i, Y i)) y => if (y.1, y) = y' then 1 else 0)
      (fun (z' : ι × (Σ i, Z i)) z => if (z.1, z) = z' then 1 else 0)
      (Tensor.dependentDirectSum T) := by
  funext x' y' z'
  rcases x' with ⟨i, ⟨ix, x⟩⟩
  rcases y' with ⟨j, ⟨iy, y⟩⟩
  rcases z' with ⟨k, ⟨iz, z⟩⟩
  have hgraph {A : Type} (f : A → ι) (a x : A) (i : ι) :
      (f a, a) = (i, x) ↔ a = x ∧ f x = i := by
    constructor
    · intro h
      have ha : a = x := congrArg Prod.snd h
      refine ⟨ha, ?_⟩
      rw [← ha]
      exact congrArg Prod.fst h
    · rintro ⟨rfl, h⟩
      simp [h]
  simp only [Tensor.restrict, hgraph, ite_and]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : ix = i
  · subst ix
    by_cases hj : iy = i
    · subst iy
      by_cases hk : iz = i
      · subst iz
        by_cases hij : i = j
        · subst j
          by_cases hik : i = k
          · subst k
            simp [Tensor.directSum, Tensor.dependentDirectSum]
          · simp [Tensor.directSum, hik]
        · simp [Tensor.directSum, hij]
      · simp [Tensor.directSum, Tensor.dependentDirectSum,
          paddedBranch_zero_right T i ⟨i, x⟩ ⟨i, y⟩ ⟨iz, z⟩ hk,
          hk]
    · simp [Tensor.directSum, Tensor.dependentDirectSum,
        paddedBranch_zero_middle T i ⟨i, x⟩ ⟨iy, y⟩ ⟨iz, z⟩ hj,
        hj]
  · simp [Tensor.directSum,
      paddedBranch_zero_left T i ⟨ix, x⟩ ⟨iy, y⟩ ⟨iz, z⟩ hi, hi]


/-- Additivity holds even when each summand has different coordinate types. -/
theorem value_dependentDirectSum
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    χ.value (Tensor.dependentDirectSum T) = ∑ i, χ.value (T i) := by
  have h := χ.value_extendByZero (Tensor.dependentDirectSum T)
    (fun x => (x.1, x)) (fun y => (y.1, y)) (fun z => (z.1, z))
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)
    (fun _ _ h => congrArg Prod.snd h)
  rw [← directSum_paddedBranch] at h
  rw [← h, χ.map_directSum]
  simp

end DependentDirectSum

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end CharacterModule1




end AllFieldsModule3
/- END all-fields module GenericCharacterCore -/

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

/-- A character is additive on binary direct sums with arbitrary finite
coordinate types. -/
theorem value_sumTensor (χ : (Character K))
    {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    χ.value (sumTensor T S) = χ.value T + χ.value S := by
  classical
  let family : (b : Bool) →
      Tensor K (bif b then U else X) (bif b then V else Y) (bif b then W else Z)
    | false => T
    | true => S
  let : ∀ b : Bool, Fintype (bif b then U else X) :=
    fun | false => inferInstanceAs (Fintype X) | true => inferInstanceAs (Fintype U)
  let : ∀ b : Bool, Fintype (bif b then V else Y) :=
    fun | false => inferInstanceAs (Fintype Y) | true => inferInstanceAs (Fintype V)
  let : ∀ b : Bool, Fintype (bif b then W else Z) :=
    fun | false => inferInstanceAs (Fintype Z) | true => inferInstanceAs (Fintype W)
  have heq : Tensor.pullback (Equiv.sumEquivSigmaBool X U)
      (Equiv.sumEquivSigmaBool Y V) (Equiv.sumEquivSigmaBool Z W)
      (Tensor.dependentDirectSum family) = sumTensor T S := by
    funext x y z
    cases x <;> cases y <;> cases z <;>
      simp [Tensor.pullback, Tensor.dependentDirectSum, Equiv.sumEquivSigmaBool,
        family, sumTensor]
  rw [← heq, χ.value_reindex, χ.value_dependentDirectSum]
  simp [family, add_comm]

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

private theorem classOf_directSum_reindex {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (T : κ → Tensor K X Y Z) (e : ι ≃ κ) :
    classOf (Tensor.directSum (fun i => T (e i))) = classOf (Tensor.directSum T) := by
  apply classOf_eq_of_reindex (Equiv.prodCongr e (Equiv.refl X))
    (Equiv.prodCongr e (Equiv.refl Y)) (Equiv.prodCongr e (Equiv.refl Z))
  funext x y z
  simp [Tensor.pullback, Tensor.directSum, e.injective.eq_iff]

private theorem classOf_directSum_option {ι : Type*} [Fintype ι] [di : DecidableEq ι]
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

/-- A character has a well-defined value on mutual-restriction classes. -/
def valueOnTensorClass (χ : (Character K)) : (TensorClass K) → ℝ :=
  Quotient.lift (fun T : (FiniteTensor K) => χ.value T.coeff) (by
    intro T S h
    change χ.value T.coeff = χ.value S.coeff
    apply le_antisymm
    · rcases h.1 with ⟨A, B, C, heq⟩
      rw [heq]
      exact χ.monotone S.coeff A B C
    · rcases h.2 with ⟨A, B, C, heq⟩
      rw [heq]
      exact χ.monotone T.coeff A B C)

@[simp] theorem valueOnTensorClass_tensorClass (χ : (Character K)) (T : (FiniteTensor K)) :
    χ.valueOnTensorClass (tensorClass T) = χ.value T.coeff := rfl

/-- Passing to a finite natural-coordinate presentation preserves the value. -/
@[simp] theorem valueOnTensorClass_classOf (χ : (Character K))
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : χ.valueOnTensorClass (classOf T) = χ.value T :=
  χ.value_reindex T _ _ _

/-- Restriction monotonicity descends to the quotient order. -/
theorem valueOnTensorClass_monotone (χ : (Character K)) : Monotone χ.valueOnTensorClass := by
  intro T S h
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change IsRestriction T.coeff S.coeff at h
  rcases h with ⟨A, B, C, heq⟩
  change χ.value T.coeff ≤ χ.value S.coeff
  rw [heq]
  exact χ.monotone S.coeff A B C

@[simp] theorem valueOnTensorClass_zero (χ : (Character K)) :
    χ.valueOnTensorClass 0 = 0 := by
  change χ.valueOnTensorClass (classOf (0 : Tensor K Empty Empty Empty)) = 0
  rw [χ.valueOnTensorClass_classOf, χ.map_zero]

@[simp] theorem valueOnTensorClass_one (χ : (Character K)) :
    χ.valueOnTensorClass 1 = 1 := by
  change χ.valueOnTensorClass (classOf unitTensor) = 1
  rw [χ.valueOnTensorClass_classOf, χ.map_one]

/-- Multiplicativity is unchanged on passing to tensor classes. -/
theorem valueOnTensorClass_mul (χ : (Character K)) (T S : (TensorClass K)) :
    χ.valueOnTensorClass (T * S) = χ.valueOnTensorClass T * χ.valueOnTensorClass S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change χ.valueOnTensorClass (tensorClass T * tensorClass S) =
    χ.valueOnTensorClass (tensorClass T) * χ.valueOnTensorClass (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_product]
  simp only [χ.valueOnTensorClass_classOf]
  exact χ.map_product T.coeff S.coeff

/-- Additivity is unchanged on passing to tensor classes. -/
theorem valueOnTensorClass_add (χ : (Character K)) (T S : (TensorClass K)) :
    χ.valueOnTensorClass (T + S) = χ.valueOnTensorClass T + χ.valueOnTensorClass S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change χ.valueOnTensorClass (tensorClass T + tensorClass S) =
    χ.valueOnTensorClass (tensorClass T) + χ.valueOnTensorClass (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_sum]
  simp only [χ.valueOnTensorClass_classOf]
  exact χ.value_sumTensor T.coeff S.coeff

/-- A coefficient-level character descends to a normalized semiring homomorphism. -/
def toTensorClassHom (χ : (Character K)) : (TensorClass K) →+* ℝ where
  toFun := χ.valueOnTensorClass
  map_zero' := χ.valueOnTensorClass_zero
  map_one' := χ.valueOnTensorClass_one
  map_add' := χ.valueOnTensorClass_add
  map_mul' := χ.valueOnTensorClass_mul

theorem toTensorClassHom_monotone (χ : (Character K)) : Monotone χ.toTensorClassHom :=
  χ.valueOnTensorClass_monotone

@[simp] theorem toTensorClassHom_classOf (χ : (Character K))
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : χ.toTensorClassHom (classOf T) = χ.value T :=
  χ.valueOnTensorClass_classOf T

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

@[simp] theorem ofTensorClassHom_value (φ : (TensorClass K) →+* ℝ) (hφ : Monotone φ)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (ofTensorClassHom φ hφ).value T = φ (classOf T) := rfl

/-- Equality of all coefficient-level values determines a character. -/
@[ext] theorem ext {χ ψ : (Character K)}
    (h : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
      (T : Tensor K X Y Z), χ.value T = ψ.value T) : χ = ψ := by
  cases χ
  cases ψ
  congr
  funext X Y Z hX hY hZ T
  exact h T

/-- Descending and then lifting recovers the original coefficient-level character. -/
@[simp] theorem ofTensorClassHom_toTensorClassHom (χ : (Character K)) :
    ofTensorClassHom χ.toTensorClassHom χ.toTensorClassHom_monotone = χ := by
  apply ext
  intro X Y Z hX hY hZ T
  exact χ.toTensorClassHom_classOf T

/-- Lifting and then descending recovers the original semiring homomorphism. -/
@[simp] theorem toTensorClassHom_ofTensorClassHom
    (φ : (TensorClass K) →+* ℝ) (hφ : Monotone φ) :
    (ofTensorClassHom φ hφ).toTensorClassHom = φ := by
  apply RingHom.ext
  intro T
  induction T using Quotient.inductionOn with | h T =>
  change φ (classOf T.coeff) = φ (tensorClass T)
  rw [classOf_coeff]

/-- Concrete characters are exactly monotone real-valued tensor semiring homomorphisms. -/
def tensorClassHomEquiv : (Character K) ≃ {φ : (TensorClass K) →+* ℝ // Monotone φ} where
  toFun χ := ⟨χ.toTensorClassHom, χ.toTensorClassHom_monotone⟩
  invFun φ := ofTensorClassHom φ.1 φ.2
  left_inv := ofTensorClassHom_toTensorClassHom
  right_inv φ := Subtype.ext (toTensorClassHom_ofTensorClassHom φ.1 φ.2)

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

/-- Splitting the diagonal index set splits its scalar tensor into two blocks. -/
theorem scalarTensor_add_reindex (m n : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      finSumFinEquiv finSumFinEquiv ((scalarTensor (K := K)) (m + n)) =
      sumTensor ((scalarTensor (K := K)) m) ((scalarTensor (K := K)) n) := by
  funext x y z
  simp only [Tensor.pullback, scalarTensor,
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).injective.eq_iff]
  cases x <;> cases y <;> cases z <;> simp [sumTensor, scalarTensor]

/-- A diagonal scalar tensor has its evident decomposition into simple terms. -/
theorem scalarTensor_rankAtMost (r : ℕ) : Tensor.RankAtMost ((scalarTensor (K := K)) r) r := by
  classical
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0), (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- The diagonal flattening also gives the matching lower bound. -/
@[simp] theorem exactRank_scalarTensor (r : ℕ) : exactRank ((scalarTensor (K := K)) r) = r := by
  apply le_antisymm (exactRank_le (scalarTensor_rankAtMost r))
  have h := (exactRank_spec ((scalarTensor (K := K)) r)).card_le_of_identity id id id
    (by intro i j; simp [scalarTensor])
  simpa only [Fintype.card_fin] using h

namespace TensorSemiring

/-- Addition of the diagonal index sets is semiring addition. -/
theorem classOf_scalarTensor_add (m n : ℕ) :
    classOf ((scalarTensor (K := K)) (m + n)) =
      classOf ((scalarTensor (K := K)) m) + classOf ((scalarTensor (K := K)) n) := by
  have h := classOf_eq_of_reindex _ _ _ (scalarTensor_add_reindex (K := K) m n)
  exact h.symm.trans (classOf_sum _ _)

@[simp] theorem classOf_scalarTensor_zero :
    classOf ((scalarTensor (K := K)) 0) = (0 : (TensorClass K)) := by
  have h : (scalarTensor (K := K)) 0 = 0 := by
    funext x
    exact Fin.elim0 x
  rw [h, classOf_zero]

@[simp] theorem classOf_scalarTensor_one :
    classOf ((scalarTensor (K := K)) 1) = (1 : (TensorClass K)) := by
  change classOf ((scalarTensor (K := K)) 1) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))
  apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 1))
    (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
  funext x y z
  simp [Tensor.pullback, scalarTensor, Subsingleton.elim x y, Subsingleton.elim y z]

/-- Natural numbers in the quotient semiring have their intended tensor meaning. -/
@[simp] theorem classOf_scalarTensor (r : ℕ) :
    classOf ((scalarTensor (K := K)) r) = (r : (TensorClass K)) := by
  induction r with
  | zero => exact classOf_scalarTensor_zero
  | succ r ih =>
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ,
        classOf_scalarTensor_one, ih] using
        classOf_scalarTensor_add (K := K) r 1

/-- Exact rank decompositions are precisely restrictions of diagonal tensors. -/
theorem rankAtMost_iff_isRestriction_scalarTensor
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (r : ℕ) :
    Tensor.RankAtMost T r ↔ IsRestriction T ((scalarTensor (K := K)) r) := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨(fun x i => a i x), (fun y i => b i y), (fun z i => c i z), ?_⟩
    apply h.trans
    funext x y z
    simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  · rintro ⟨A, B, C, rfl⟩
    exact (scalarTensor_rankAtMost r).restrict A B C

/-- The restriction order below a natural number is exactly the usual rank bound. -/
theorem classOf_le_nat_iff_rankAtMost
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (r : ℕ) :
    classOf T ≤ (r : (TensorClass K)) ↔ Tensor.RankAtMost T r := by
  rw [← classOf_scalarTensor r, classOf_le_iff]
  exact (rankAtMost_iff_isRestriction_scalarTensor T r).symm

/-- Rank takes its usual value on natural numbers in the tensor semiring. -/
@[simp] theorem rank_natCast (r : ℕ) : rank (r : (TensorClass K)) = r := by
  rw [← classOf_scalarTensor r, rank_classOf, exactRank_scalarTensor]

/-- The rank is a natural-number upper bound in the restriction order. -/
theorem le_rank (T : (TensorClass K)) : T ≤ (rank T : (TensorClass K)) := by
  induction T using Quotient.inductionOn with
  | h T =>
    change tensorClass T ≤ (exactRank T.coeff : (TensorClass K))
    rw [← classOf_coeff T]
    exact (classOf_le_nat_iff_rankAtMost T.coeff (exactRank T.coeff)).mpr
      (exactRank_spec T.coeff)

/-- The tensor restriction order induces the usual order on natural numbers. -/
@[simp] theorem natCast_le_natCast_iff (m n : ℕ) :
    (m : (TensorClass K)) ≤ (n : (TensorClass K)) ↔ m ≤ n := by
  constructor
  · intro h
    simpa only [rank_natCast] using rank_mono h
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add]
    simpa only [add_zero] using add_mono (le_refl (m : (TensorClass K))) (zero_le (k : (TensorClass K)))

/-- A natural multiple of any nonzero tensor contains any prescribed tensor
by restriction. -/
theorem le_nat_mul_of_ne_zero (T S : (TensorClass K)) (hS : S ≠ 0) :
    T ≤ (rank T : (TensorClass K)) * S := by
  apply (le_rank T).trans
  simpa only [mul_one] using
    mul_mono (le_refl (rank T : (TensorClass K))) (one_le_of_ne_zero hS)

end TensorSemiring
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end CharacterModule5




end AllFieldsModule4
/- END all-fields module GenericCharacters -/

/- BEGIN all-fields module GenericSpectrum -/
section AllFieldsModule5



section SpectrumModule0

namespace OAI

/-!
# The rank obstruction behind the preliminary spectral state

The finite catalyst is kept fixed while first tensor powers, then exponent
slack, then the number of copies are varied.  The hypotheses below isolate the
rank inequalities supplied by the catalytic comparison; they do not assert
the existence of a tensor spectrum or the separation argument producing that
comparison.
-/

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜]

/-- Tensor powers of a fixed exact matrix algorithm retain their exact rank
bound after identifying the product coordinates with one matrix dimension. -/
theorem exactMatrixRank_pow_le (u j : ℕ) :
    (exactMatrixRank 𝕜) (u ^ j) ≤ (exactMatrixRank 𝕜) u ^ j := by
  classical
  let e : Fin (u ^ j) ≃ (Fin j → Fin u) := Fintype.equivOfCardEq (by simp)
  let f : Fin (u ^ j) × Fin (u ^ j) → Fin j → Fin u × Fin u :=
    fun x i => (e x.1 i, e x.2 i)
  have h := (((exactMatrixRank_spec (K := 𝕜)) u).power j).pullback f f f
  have heq : Tensor.pullback f f f (Tensor.power ((Tensor.matrixMultiplication (K := 𝕜)) u u u) j) =
      (Tensor.matrixMultiplication (K := 𝕜)) (u ^ j) (u ^ j) (u ^ j) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, Tensor.matrixMultiplication, f,
      Fintype.prod_boole, forall_and, ← funext_iff, e.injective.eq_iff]
  rw [heq] at h
  exact exactRank_le h

/-- A floor approximation uses at most `n^j` copies of a fixed matrix
algorithm and loses at most one factor of its fixed matrix dimension. -/
theorem floor_rank_power_bounds {u n R : ℕ} (hu : 2 ≤ u) (hn : 1 ≤ n)
    {τ : ℝ} (hτ : 0 < τ) (hR : (R : ℝ) ≤ (u : ℝ) ^ τ) (j : ℕ) :
    let l := ⌊(j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ⌋₊
    (R : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
      (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l := by
  have hu1 : (1 : ℝ) < u := by exact_mod_cast (show 1 < u by omega)
  have hu0 : (0 : ℝ) < u := zero_lt_one.trans hu1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  let x := (j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ
  let l := ⌊x⌋₊
  have hx : 0 ≤ x := div_nonneg
    (mul_nonneg (Nat.cast_nonneg j) (Real.logb_nonneg hu1 hn1)) hτ.le
  have hl : (l : ℝ) ≤ x := Nat.floor_le hx
  have hxl : x ≤ (l : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hlog : (u : ℝ) ^ Real.logb (u : ℝ) (n : ℝ) = n :=
    Real.rpow_logb hu0 (ne_of_gt hu1) hn0
  change (R : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
    (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l
  constructor
  · calc
      (R : ℝ) ^ l ≤ ((u : ℝ) ^ τ) ^ l :=
        pow_le_pow_left₀ (Nat.cast_nonneg R) hR l
      _ = (u : ℝ) ^ (τ * (l : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
      _ ≤ (u : ℝ) ^ (τ * x) :=
        Real.rpow_le_rpow_of_exponent_le hu1.le (mul_le_mul_of_nonneg_left hl hτ.le)
      _ = (n : ℝ) ^ j := by
        rw [show τ * x = Real.logb (u : ℝ) (n : ℝ) * (j : ℝ) by
          dsimp [x]; field_simp]
        rw [Real.rpow_mul hu0.le, hlog, Real.rpow_natCast]
  · calc
      (n : ℝ) ^ ((j : ℝ) / τ) = (u : ℝ) ^ x := by
        rw [← hlog, ← Real.rpow_mul hu0.le]
        congr 1
        dsimp [x]
        ring
      _ ≤ (u : ℝ) ^ ((l : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le hu1.le hxl
      _ = (u : ℝ) * (u : ℝ) ^ l := by
        rw [Real.rpow_add hu0, Real.rpow_natCast, Real.rpow_one, mul_comm]

/-- At fixed `n` and exponent slack, every admissible matrix rank budget
forces the exponential growth rate of the catalytic comparison.  The constant
`R` is fixed before the tensor-power parameter varies. -/
theorem catalytic_rank_bound_at_slack {d n K R : ℕ}
    (hd : 0 < d) (hn : 1 ≤ n)
    (hbound : ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ, (exactMatrixRank 𝕜) g ≤ n ^ j →
      (exactMatrixRank 𝕜) (d ^ j * g) ≤ R * K ^ j)
    {δ : ℝ} (hδ : 0 < δ) :
    (d : ℝ) ^ (exactRankExponent 𝕜) *
      (n : ℝ) ^ ((exactRankExponent 𝕜) / ((exactRankExponent 𝕜) + δ)) ≤ K := by
  let ν := (exactRankExponent 𝕜)
  let τ := ν + δ
  have hν : 0 ≤ ν := (by norm_num : (0 : ℝ) ≤ 2).trans (exactRankExponent_lower (K := 𝕜))
  have hτ : 0 < τ := add_pos_of_nonneg_of_pos hν hδ
  obtain ⟨u, hu, huR⟩ := (exists_exactMatrixRank_lt_rpow (K := 𝕜))
    (show (exactRankExponent 𝕜) < τ from lt_add_of_pos_right _ hδ)
  apply le_of_eventually_pow_le_const_mul_pow (C := (u : ℝ) ^ ν * R)
    (Nat.cast_nonneg K)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with j hj
  let l := ⌊(j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ⌋₊
  let g := u ^ l
  have hg : 0 < g := pow_pos (by omega) l
  have hf := floor_rank_power_bounds hu hn hτ huR.le j
  change ((exactMatrixRank 𝕜) u : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
    (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l at hf
  have hbudget : (exactMatrixRank 𝕜) g ≤ n ^ j := by
    have hpow : ((exactMatrixRank 𝕜) g : ℝ) ≤ ((exactMatrixRank 𝕜) u : ℝ) ^ l := by
      exact_mod_cast exactMatrixRank_pow_le u l
    have hb := hpow.trans hf.1
    exact_mod_cast hb
  have hrank := hbound j hj g hbudget
  have hsize : (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * g := by
    simpa only [g, Nat.cast_pow] using hf.2
  have hlow := (exactMatrixRank_rpow_lower_of_pos (K := 𝕜)) (mul_pos (pow_pos hd j) hg)
  have hpow_n : ((n : ℝ) ^ (ν / τ)) ^ j =
      ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  calc
    ((d : ℝ) ^ ν * (n : ℝ) ^ (ν / τ)) ^ j =
        (((d ^ j : ℕ) : ℝ) ^ ν) * ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
      rw [mul_pow, Real.rpow_pow_comm (Nat.cast_nonneg d), hpow_n, Nat.cast_pow]
    _ ≤ (((d ^ j : ℕ) : ℝ) ^ ν) * ((u : ℝ) * g) ^ ν := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsize hν)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (u : ℝ) ^ ν * (((d ^ j * g : ℕ) : ℝ) ^ ν) := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg u) (Nat.cast_nonneg g),
        Real.mul_rpow (Nat.cast_nonneg (d ^ j)) (Nat.cast_nonneg g)]
      ring
    _ ≤ (u : ℝ) ^ ν * ((exactMatrixRank 𝕜) (d ^ j * g) : ℝ) :=
      mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (Nat.cast_nonneg u) _)
    _ ≤ (u : ℝ) ^ ν * ((R : ℝ) * (K : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg u) _)
      exact_mod_cast hrank
    _ = ((u : ℝ) ^ ν * R) * (K : ℝ) ^ j := by ring

/-- The numerical rank consequence of a single fixed finite catalyst is
incompatible with `k < d^ν`.  The same `D` and `R` occur for every `n` and
every tensor power.  No uniform bound on the approximation block selected
after an exponent slack is assumed. -/
theorem catalytic_rank_obstruction {d k D R : ℕ} (hd : 0 < d)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ,
      (exactMatrixRank 𝕜) g ≤ n ^ j →
      (exactMatrixRank 𝕜) (d ^ j * g) ≤ R * (n * k + D) ^ j) :
    (d : ℝ) ^ (exactRankExponent 𝕜) ≤ k := by
  apply spectral_coefficient_le_of_all_nat
    (hν := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (exactRankExponent_lower (K := 𝕜)))
    (D := (D : ℝ))
  intro n hn δ hδ
  have h := catalytic_rank_bound_at_slack hd hn (hbound n hn) hδ
  simpa only [Nat.cast_add, Nat.cast_mul] using h

/-- Contradiction form for the finite-obstruction argument. -/
theorem not_catalytic_rank_bounds_of_lt {d k D R : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) < (d : ℝ) ^ (exactRankExponent 𝕜)) :
    ¬ (∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ,
      (exactMatrixRank 𝕜) g ≤ n ^ j →
      (exactMatrixRank 𝕜) (d ^ j * g) ≤ R * (n * k + D) ^ j) := by
  intro hbound
  exact (not_lt_of_ge (catalytic_rank_obstruction hd hbound)) hk

/-- Iteration and absorption of a fixed catalyst require no cancellation of
the tensor factor `s`.  Monotonicity is explicit so the lemma applies to the
restriction order on a tensor semiring, where additive cancellation fails. -/
theorem catalytic_power_comparison {S : Type*} [CommSemiring S] [Preorder S]
    (hadd : ∀ {a b c e : S}, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hmul : ∀ {a b c e : S}, a ≤ b → c ≤ e → a * c ≤ b * e)
    (hzero : ∀ a : S, 0 ≤ a)
    (D t s : S) (k C : ℕ)
    (hcat : D + t * s ≤ D + (k : S) * s)
    (hD : D ≤ (C : S) * s) (n j : ℕ) :
    (n : S) ^ j * t ^ j * s ≤ ((n * k + C : ℕ) : S) ^ j * s := by
  have hiter : ∀ m : ℕ,
      D + (m : S) * (t * s) ≤ D + (m : S) * ((k : S) * s) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        D + ((m + 1 : ℕ) : S) * (t * s) =
            (D + t * s) + (m : S) * (t * s) := by push_cast; ring
        _ ≤ (D + (k : S) * s) + (m : S) * (t * s) := hadd hcat le_rfl
        _ = (D + (m : S) * (t * s)) + (k : S) * s := by ring
        _ ≤ (D + (m : S) * ((k : S) * s)) + (k : S) * s := hadd ih le_rfl
        _ = D + ((m + 1 : ℕ) : S) * ((k : S) * s) := by push_cast; ring
  have habsorb : (n : S) * t * s ≤ ((n * k + C : ℕ) : S) * s := by
    calc
      (n : S) * t * s = 0 + (n : S) * (t * s) := by ring
      _ ≤ D + (n : S) * (t * s) := hadd (hzero D) le_rfl
      _ ≤ D + (n : S) * ((k : S) * s) := hiter n
      _ ≤ (C : S) * s + (n : S) * ((k : S) * s) := hadd hD le_rfl
      _ = ((n * k + C : ℕ) : S) * s := by push_cast; ring
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      (n : S) ^ (j + 1) * t ^ (j + 1) * s =
          ((n : S) ^ j * t ^ j) * ((n : S) * t * s) := by ring
      _ ≤ ((n : S) ^ j * t ^ j) * (((n * k + C : ℕ) : S) * s) :=
        hmul le_rfl habsorb
      _ = ((n * k + C : ℕ) : S) * ((n : S) ^ j * t ^ j * s) := by ring
      _ ≤ ((n * k + C : ℕ) : S) * (((n * k + C : ℕ) : S) ^ j * s) :=
        hmul le_rfl ih
      _ = ((n * k + C : ℕ) : S) ^ (j + 1) * s := by ring

/-- A rank-compatible ordered tensor semiring converts a single finite
catalytic inequality into the actual exact-rank obstruction.  The hypotheses
name the required tensor interpretation and scalar rank domination explicitly;
no additive rank formula or cancellation property is assumed. -/
theorem catalytic_semiring_obstruction {S : Type*} [CommSemiring S] [Preorder S]
    (hadd : ∀ {a b c e : S}, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hmul : ∀ {a b c e : S}, a ≤ b → c ≤ e → a * c ≤ b * e)
    (hzero : ∀ a : S, 0 ≤ a)
    (ρ : S → ℕ) (hρmono : Monotone ρ)
    (hρcopies : ∀ (m : ℕ) (s : S), ρ ((m : S) * s) ≤ m * ρ s)
    (M : ℕ → S)
    (hMmul : ∀ a b : ℕ, M (a * b) = M a * M b)
    (hMpow : ∀ a j : ℕ, M (a ^ j) = M a ^ j)
    (hρM : ∀ a : ℕ, ρ (M a) = (exactMatrixRank 𝕜) a)
    (hbudget : ∀ n j g : ℕ, (exactMatrixRank 𝕜) g ≤ n ^ j → M g ≤ (n : S) ^ j)
    (D s : S) (d k C : ℕ) (hd : 0 < d) (hs : 1 ≤ s)
    (hcat : D + M d * s ≤ D + (k : S) * s)
    (hD : D ≤ (C : S) * s) :
    (d : ℝ) ^ (exactRankExponent 𝕜) ≤ k := by
  apply catalytic_rank_obstruction (D := C) (R := ρ s) hd
  intro n _hn j _hj g hg
  have hcompare : M (d ^ j * g) ≤ ((n * k + C : ℕ) : S) ^ j * s := by
    calc
      M (d ^ j * g) = M d ^ j * M g := by rw [hMmul, hMpow]
      _ ≤ M d ^ j * (n : S) ^ j := hmul le_rfl (hbudget n j g hg)
      _ = ((n : S) ^ j * M d ^ j) * 1 := by ring
      _ ≤ ((n : S) ^ j * M d ^ j) * s := hmul le_rfl hs
      _ ≤ ((n * k + C : ℕ) : S) ^ j * s :=
        catalytic_power_comparison hadd hmul hzero D (M d) s k C hcat hD n j
  calc
    (exactMatrixRank 𝕜) (d ^ j * g) = ρ (M (d ^ j * g)) := (hρM _).symm
    _ ≤ ρ (((n * k + C : ℕ) : S) ^ j * s) := hρmono hcompare
    _ = ρ ((((n * k + C) ^ j : ℕ) : S) * s) := by rw [Nat.cast_pow]
    _ ≤ (n * k + C) ^ j * ρ s := hρcopies _ s
    _ = ρ s * (n * k + C) ^ j := Nat.mul_comm _ _

/-- In the semiring of actual finite complex tensors modulo mutual
restriction, a fixed catalyst cannot make `k` copies dominate multiplication
by `T_d` unless `k ≥ d^ν`.  The nonzero hypothesis is exactly what supplies
the scalar restriction `s ≥ 1`; the catalyst remains fixed throughout. -/
theorem tensor_catalytic_obstruction
    {D s : (TensorSemiring.TensorClass 𝕜)} {d k : ℕ}
    (hd : 0 < d) (hs : s ≠ 0)
    (hcat : D + (TensorSemiring.matrixClass (K := 𝕜)) d * s ≤ D + (k : (TensorSemiring.TensorClass 𝕜)) * s) :
    (d : ℝ) ^ (exactRankExponent 𝕜) ≤ k := by
  have hs1 : 1 ≤ s := TensorSemiring.one_le_of_ne_zero hs
  have hcopies : ∀ (m : ℕ) (x : (TensorSemiring.TensorClass 𝕜)),
      TensorSemiring.rank ((m : (TensorSemiring.TensorClass 𝕜)) * x) ≤
        m * TensorSemiring.rank x := by
    intro m x
    simpa only [TensorSemiring.rank_natCast] using
      TensorSemiring.rank_mul_le (m : (TensorSemiring.TensorClass 𝕜)) x
  have hbudget : ∀ n j g : ℕ, (exactMatrixRank 𝕜) g ≤ n ^ j →
      (TensorSemiring.matrixClass (K := 𝕜)) g ≤ (n : (TensorSemiring.TensorClass 𝕜)) ^ j := by
    intro n j g hg
    have hleft : (TensorSemiring.matrixClass (K := 𝕜)) g ≤
        ((exactMatrixRank 𝕜) g : (TensorSemiring.TensorClass 𝕜)) := by
      simpa only [TensorSemiring.rank_matrixClass] using
        TensorSemiring.le_rank ((TensorSemiring.matrixClass (K := 𝕜)) g)
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hg
    have hright : ((exactMatrixRank 𝕜) g : (TensorSemiring.TensorClass 𝕜)) ≤
        (n : (TensorSemiring.TensorClass 𝕜)) ^ j := by
      rw [← Nat.cast_pow, hq, Nat.cast_add]
      simpa only [add_zero] using TensorSemiring.add_mono
        (le_refl ((exactMatrixRank 𝕜) g : (TensorSemiring.TensorClass 𝕜)))
        (TensorSemiring.zero_le (q : (TensorSemiring.TensorClass 𝕜)))
    exact hleft.trans hright
  have hD : D ≤ (TensorSemiring.rank D : (TensorSemiring.TensorClass 𝕜)) * s := by
    calc
      D ≤ (TensorSemiring.rank D : (TensorSemiring.TensorClass 𝕜)) := TensorSemiring.le_rank D
      _ = (TensorSemiring.rank D : (TensorSemiring.TensorClass 𝕜)) * 1 := (mul_one _).symm
      _ ≤ (TensorSemiring.rank D : (TensorSemiring.TensorClass 𝕜)) * s :=
        TensorSemiring.mul_mono le_rfl hs1
  exact catalytic_semiring_obstruction
    TensorSemiring.add_mono TensorSemiring.mul_mono TensorSemiring.zero_le
    TensorSemiring.rank (fun _ _ h => TensorSemiring.rank_mono h) hcopies
    (TensorSemiring.matrixClass (K := 𝕜)) (TensorSemiring.matrixClass_mul (K := 𝕜)) (TensorSemiring.matrixClass_pow (K := 𝕜))
    TensorSemiring.rank_matrixClass hbudget D s d k (TensorSemiring.rank D) hd hs1 hcat hD

/-- The stronger comparison produced by a finite separation certificate
has the same consequence.  Its positive scalar summand is only needed
earlier to rule out `s = 0`; that nonzero fact is explicit here. -/
theorem tensor_catalytic_obstruction_of_scalar_gain
    {D s : (TensorSemiring.TensorClass 𝕜)} {d k m : ℕ}
    (hd : 0 < d) (hs : s ≠ 0)
    (hcat : D + (m : (TensorSemiring.TensorClass 𝕜)) + (TensorSemiring.matrixClass (K := 𝕜)) d * s ≤
      D + (k : (TensorSemiring.TensorClass 𝕜)) * s) :
    (d : ℝ) ^ (exactRankExponent 𝕜) ≤ k := by
  apply tensor_catalytic_obstruction hd hs
  refine le_trans ?_ hcat
  simpa only [add_zero] using TensorSemiring.add_mono
    (TensorSemiring.add_mono (le_refl D)
      (TensorSemiring.zero_le (m : (TensorSemiring.TensorClass 𝕜))))
    (le_refl ((TensorSemiring.matrixClass (K := 𝕜)) d * s))

/-- A finite tensor cannot absorb a positive scalar direct summand.  Iterating
such an absorption would place arbitrarily large scalar tensors below one
fixed finite-rank tensor.  This uses rank monotonicity, not rank additivity. -/
theorem not_tensor_add_positive_nat_le_self (D : (TensorSemiring.TensorClass 𝕜))
    {m : ℕ} (hm : 0 < m) : ¬ D + (m : (TensorSemiring.TensorClass 𝕜)) ≤ D := by
  intro h
  have hiter : ∀ n : ℕ, D + ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) ≤ D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        D + (((n + 1) * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) =
            (D + ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜))) + m := by push_cast; ring
        _ ≤ D + (m : (TensorSemiring.TensorClass 𝕜)) := TensorSemiring.add_mono ih le_rfl
        _ ≤ D := h
  let n := TensorSemiring.rank D + 1
  have hscalar : ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) ≤ D := by
    have hleft := TensorSemiring.add_mono (TensorSemiring.zero_le D)
      (le_refl ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)))
    have hsmall : ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) ≤
        D + ((n * m : ℕ) : (TensorSemiring.TensorClass 𝕜)) := by
      simpa only [zero_add] using hleft
    exact hsmall.trans (hiter n)
  have hrank : n * m ≤ TensorSemiring.rank D := by
    simpa only [TensorSemiring.rank_natCast] using TensorSemiring.rank_mono hscalar
  have hnm : n ≤ n * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (Nat.succ_le_of_lt hm)
  have hlarge : TensorSemiring.rank D + 1 ≤ TensorSemiring.rank D := hnm.trans hrank
  omega

/-- The exact finite-obstruction comparison from Appendix A.1 forces
`k ≥ d^ν`.  Both tensors are fixed, `m` is a positive scalar gain, and the
ordinary tensor rank and restriction order are the actual ones. -/
theorem tensor_catalytic_obstruction_of_positive_scalar_gain
    {D s : (TensorSemiring.TensorClass 𝕜)} {d k m : ℕ}
    (hd : 0 < d) (hm : 0 < m)
    (hcat : D + (m : (TensorSemiring.TensorClass 𝕜)) + (TensorSemiring.matrixClass (K := 𝕜)) d * s ≤
      D + (k : (TensorSemiring.TensorClass 𝕜)) * s) :
    (d : ℝ) ^ (exactRankExponent 𝕜) ≤ k := by
  apply tensor_catalytic_obstruction_of_scalar_gain hd (m := m) ?_ hcat
  intro hs
  subst s
  have hbad : D + (m : (TensorSemiring.TensorClass 𝕜)) ≤ D := by
    simpa only [mul_zero, add_zero] using hcat
  exact not_tensor_add_positive_nat_le_self D hm hbad

/-- Contradiction interface for the finite inconsistency certificate in
the construction of an additive monotone state. -/
theorem no_tensor_catalytic_gain {d k : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) < (d : ℝ) ^ (exactRankExponent 𝕜)) :
    ¬ ∃ (D s : (TensorSemiring.TensorClass 𝕜)) (m : ℕ), 0 < m ∧
      D + (m : (TensorSemiring.TensorClass 𝕜)) + (TensorSemiring.matrixClass (K := 𝕜)) d * s ≤
        D + (k : (TensorSemiring.TensorClass 𝕜)) * s := by
  rintro ⟨D, s, m, hm, hcat⟩
  exact (not_lt_of_ge (tensor_catalytic_obstruction_of_positive_scalar_gain hd hm hcat)) hk

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end SpectrumModule0


section SpectrumModule1

namespace OAI

/-!
# Detecting characters for complex matrix multiplication

This proves Lemma 3.1, including Appendix A. Finite inconsistency would
produce a positive scalar-gain catalyst, ruled out by the exact-rank exponent.
A compact normalized state space then yields a multiplicative state, which
transfers to the concrete coefficient-level character interface.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜]

open MatrixMultiplication.Foundation

/-- Lemma 3.1: normalized, additive, multiplicative, restriction-monotone
characters detect every integer strictly below the exact-rank growth value. -/
theorem exists_detecting_character {d k : ℕ} (hd : 2 ≤ d)
    (hk : (k : ℝ) < (d : ℝ) ^ (exactRankExponent 𝕜)) :
    ∃ χ : (Character 𝕜), (k : ℝ) ≤ χ.value ((Tensor.matrixMultiplication (K := 𝕜)) d d d) := by
  have hnonempty := normalizedStates_nonempty_of_no_catalyst
    TensorSemiring.rank ((TensorSemiring.matrixClass (K := 𝕜)) d) k
    TensorSemiring.zero_le TensorSemiring.le_rank
    (fun _ _ _ _ h₁ h₂ => TensorSemiring.add_mono h₁ h₂)
    (fun D s m hm hcat => no_tensor_catalytic_gain (by omega) hk ⟨D, s, m, hm, hcat⟩)
  have hdom (z x : (TensorSemiring.TensorClass 𝕜)) :
      z * x ≤ (TensorSemiring.rank x : (TensorSemiring.TensorClass 𝕜)) * z := by
    calc
      z * x ≤ z * (TensorSemiring.rank x : (TensorSemiring.TensorClass 𝕜)) :=
        TensorSemiring.mul_mono le_rfl (TensorSemiring.le_rank x)
      _ = (TensorSemiring.rank x : (TensorSemiring.TensorClass 𝕜)) * z := mul_comm _ _
  obtain ⟨φ, hφ, _, hdetect⟩ := exists_monotone_semiringHom_of_normalizedStates
    TensorSemiring.rank ((TensorSemiring.matrixClass (K := 𝕜)) d) (k : ℝ)
    (fun z hz => TensorSemiring.one_le_of_ne_zero hz)
    (fun _ _ _ h => TensorSemiring.mul_mono le_rfl h) hdom hnonempty
  exact ⟨Character.ofTensorClassHom φ hφ, hdetect⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end SpectrumModule1




end AllFieldsModule5
/- END all-fields module GenericSpectrum -/

/- BEGIN all-fields module GenericPairing -/
section AllFieldsModule6
/-! The generic algebraic pairing and symmetrization layers from OAI.
Complex topological border-rank theorems are excluded. All retained algebraic
statements use the original namespaces and are valid over CommSemiring K.
-/
set_option autoImplicit false
section PairingModule0
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Pairing

variable {K U : Type*} [CommSemiring K] [DecidableEq U]

def dotPairing (U : Type*) [DecidableEq U] : Tensor K U U Unit :=
  fun i j _ => if i = j then 1 else 0

@[simp] theorem dotPairing_matching (i : U) :
    dotPairing (K := K) U i i () = 1 := by
  simp [dotPairing]

theorem contract_dotPairing [Fintype U] (a b : U → K) :
    contract (dotPairing (K := K) U) a b () = ∑ i, a i * b i := by
  classical
  simp [contract, dotPairing, ite_mul]

end Pairing

end Tensor
end MatrixMultiplication.Foundation

end OAI

end PairingModule0

section PairingModule1
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

theorem RankAtMost.cyclic {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) : RankAtMost (Tensor.cyclic T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, c, a, ?_⟩
  funext y z x
  simp only [Tensor.cyclic, rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def directSumProductEquiv (ι κ X U : Type*) :
    ((ι × κ) × (X × U)) ≃ ((ι × X) × (κ × U)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (T : ι → Tensor K X Y Z) (S : κ → Tensor K U V W) :
    pullback (directSumProductEquiv ι κ X U)
      (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
      (product (directSum T) (directSum S)) =
      directSum (fun i : ι × κ => product (T i.1) (S i.2)) := by
  funext x y z
  change
    (if x.1.1 = y.1.1 ∧ x.1.1 = z.1.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 else 0) *
    (if x.1.2 = y.1.2 ∧ x.1.2 = z.1.2 then
      S x.1.2 x.2.2 y.2.2 z.2.2 else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 * S x.1.2 x.2.2 y.2.2 z.2.2 else 0
  have hguard : (x.1 = y.1 ∧ x.1 = z.1) ↔
      (x.1.1 = y.1.1 ∧ x.1.1 = z.1.1) ∧
      (x.1.2 = y.1.2 ∧ x.1.2 = z.1.2) := by
    constructor
    · intro h
      exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
        ⟨congrArg Prod.snd h.1, congrArg Prod.snd h.2⟩⟩
    · intro h
      exact ⟨Prod.ext h.1.1 h.2.1, Prod.ext h.1.2 h.2.2⟩
  by_cases hi : x.1.1 = y.1.1 ∧ x.1.1 = z.1.1
  · by_cases hk : x.1.2 = y.1.2 ∧ x.1.2 = z.1.2
    · simp only [if_pos hi, if_pos hk, if_pos (hguard.mpr ⟨hi, hk⟩)]
    · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hk (hguard.mp h).2
      simp only [if_pos hi, if_neg hk, if_neg hfull, mul_zero]
  · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hi (hguard.mp h).1
    simp only [if_neg hi, if_neg hfull, zero_mul]

theorem RankAtMost.directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : ι → Tensor K X Y Z} {S : κ → Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost (directSum T) r) (hS : RankAtMost (directSum S) s) :
    RankAtMost (directSum (fun i : ι × κ => Tensor.product (T i.1) (S i.2))) (r * s) := by
  have h := (hT.product hS).pullback (directSumProductEquiv ι κ X U)
    (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
  rw [Tensor.directSum_product] at h
  exact h

theorem directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    pullback (fun x : ι × X' => (x.1, fx x.2))
      (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))
      (directSum T) = directSum (fun i => pullback fx fy fz (T i)) := rfl

theorem RankAtMost.directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (directSum (fun i => Tensor.pullback fx fy fz (T i))) r :=
  h.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

theorem cyclic_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    cyclic (directSum T) = directSum (fun i => cyclic (T i)) := by
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [cyclic, directSum]
    · simp [cyclic, directSum, hik, Ne.symm hik]
  · by_cases hki : k = i
    · subst k
      simp [cyclic, directSum, hij]
    · simp [cyclic, directSum, hij, hki]

theorem RankAtMost.directSum_cyclic {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r) :
    RankAtMost (directSum (fun i => Tensor.cyclic (T i))) r := by
  rw [← Tensor.cyclic_directSum]
  exact h.cyclic

def directSumPowerEquiv (ι X : Type*) (n : ℕ) :
    ((Fin n → ι) × (Fin n → X)) ≃ (Fin n → ι × X) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem directSum_power {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum T) n) =
      directSum (fun f : Fin n → ι =>
        fun x y z => ∏ i, T (f i) (x i) (y i) (z i)) := by
  funext x y z
  change (∏ i, if x.1 i = y.1 i ∧ x.1 i = z.1 i then
      T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      ∏ i, T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0
  simp only [Fintype.prod_ite_zero, forall_and, ← funext_iff]

theorem directSum_const_power {ι : Type*} [DecidableEq ι]
    (T : Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum (fun _ : ι => T)) n) =
      directSum (fun _ : Fin n → ι => power T n) :=
  directSum_power (fun _ : ι => T) n

theorem RankAtMost.directSum_const_of_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {n R : ℕ}
    (h : RankAtMost (Tensor.power (directSum (fun _ : ι => T)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) R := by
  have h' := h.pullback (directSumPowerEquiv ι X n)
    (directSumPowerEquiv ι Y n) (directSumPowerEquiv ι Z n)
  rw [Tensor.directSum_const_power] at h'
  exact h'

theorem RankAtMost.directSum_const_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum (fun _ : ι => T)) r)
    (n : ℕ) : RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) (r ^ n) :=
  (h.power n).directSum_const_of_power

section Rectangular

variable {A B C : Type*}

def rectangularSquareX (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((A × B) × (B × C)) × (C × A)) where
  toFun x := (((x.1.1, x.2.2.1), (x.1.2.1, x.2.2.2)), (x.1.2.2, x.2.1))
  invFun x := ((x.1.1.1, x.1.2.1, x.2.1), (x.2.2, x.1.1.2, x.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareY (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((B × C) × (C × A)) × (A × B)) where
  toFun y := (((y.1.2.1, y.2.2.2), (y.1.2.2, y.2.1)), (y.1.1, y.2.2.1))
  invFun y := ((y.2.1, y.1.1.1, y.1.2.1), (y.1.2.2, y.2.2, y.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareZ (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((C × A) × (A × B)) × (B × C)) where
  toFun z := (((z.1.2.2, z.2.1), (z.1.1, z.2.2.1)), (z.1.2.1, z.2.2.2))
  invFun z := ((z.1.2.1, z.2.1, z.1.1.1), (z.1.1.2, z.1.2.2, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrixCoefficients_directSum_rank_of_power
    {ι : Type*} [DecidableEq ι] {n R : ℕ}
    (h : RankAtMost
      (power (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι =>
      matrixCoefficients (K := K) (Fin n → A) (Fin n → B) (Fin n → C))) R := by
  have h' := h.directSum_const_of_power.directSum_pullback
    (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
  have heq : pullback
      (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
      (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
      (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
      (power (matrixCoefficients (K := K) A B C) n) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) := by
    funext x y z
    exact matrixCoefficients_power n x y z
  simpa only [heq] using h'

theorem matrixCoefficients_cyclic_product_square :
    pullback (rectangularSquareX A B C) (rectangularSquareY A B C)
      (rectangularSquareZ A B C)
      (product (product (matrixCoefficients (K := K) A B C)
        (matrixCoefficients B C A)) (matrixCoefficients C A B)) =
      matrixCoefficients (A × B × C) (A × B × C) (A × B × C) := by
  funext x y z
  change
    ((if x.2.2.1 = y.1.2.1 ∧ y.2.2.2 = z.1.2.2 ∧ z.2.1 = x.1.1 then
        (1 : K) else 0) *
      (if x.2.2.2 = y.1.2.2 ∧ y.2.1 = z.1.1 ∧ z.2.2.1 = x.1.2.1 then
        1 else 0)) *
      (if x.2.1 = y.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ z.2.2.2 = x.1.2.2 then
        1 else 0) =
      if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [Prod.ext_iff]
  have hguard :
      (((x.2.2.1 = y.1.2.1 ∧ y.2.2.2 = z.1.2.2 ∧ z.2.1 = x.1.1) ∧
        (x.2.2.2 = y.1.2.2 ∧ y.2.1 = z.1.1 ∧ z.2.2.1 = x.1.2.1)) ∧
        (x.2.1 = y.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ z.2.2.2 = x.1.2.2)) ↔
      ((x.2.1 = y.1.1 ∧ x.2.2.1 = y.1.2.1 ∧ x.2.2.2 = y.1.2.2) ∧
        (y.2.1 = z.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ y.2.2.2 = z.1.2.2) ∧
        z.2.1 = x.1.1 ∧ z.2.2.1 = x.1.2.1 ∧ z.2.2.2 = x.1.2.2) := by
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨⟨h₃.1, h₁.1, h₂.1⟩, ⟨h₂.2.1, h₃.2.1, h₁.2.1⟩,
        h₁.2.2, h₂.2.2, h₃.2.2⟩
    · intro h
      exact ⟨⟨⟨h.1.2.1, h.2.1.2.2, h.2.2.1⟩,
        ⟨h.1.2.2, h.2.1.1, h.2.2.2.1⟩⟩, ⟨h.1.1, h.2.1.2.1, h.2.2.2.2⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

theorem cyclic_matrixCoefficients :
    cyclic (matrixCoefficients (K := K) A B C) = matrixCoefficients B C A := by
  funext x y z
  exact matrixCoefficients_cyclic x y z

theorem matrixCoefficients_symmetrized_rank {r : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K)
      (A × B × C) (A × B × C) (A × B × C)) (r ^ 3) := by
  have h' := ((h.product (matrixCoefficients_cyclic_rank h)).product
    (matrixCoefficients_cyclic_rank (matrixCoefficients_cyclic_rank h))).pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  rw [matrixCoefficients_cyclic_product_square] at h'
  simpa only [pow_succ, pow_zero, one_mul] using h'

theorem matrixCoefficients_directSum_symmetrized_rank
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : (ι × ι) × ι =>
      matrixCoefficients (K := K) (A × B × C) (A × B × C) (A × B × C))) (r ^ 3) := by
  have h₁ : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) B C A)) r := by
    simpa only [cyclic_matrixCoefficients] using h.directSum_cyclic
  have h₂ : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) C A B)) r := by
    simpa only [cyclic_matrixCoefficients] using h₁.directSum_cyclic
  have h₃ := ((h.directSum_product h₁).directSum_product h₂).directSum_pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  simpa only [matrixCoefficients_cyclic_product_square, pow_succ, pow_zero, one_mul] using h₃

theorem symmetrized_tag_card (ι : Type*) [Fintype ι] :
    Fintype.card ((ι × ι) × ι) = Fintype.card ι ^ 3 := by
  simp [Fintype.card_prod, pow_succ]

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
theorem symmetrized_index_card [Fintype A] [Fintype B] [Fintype C] :
    Fintype.card (A × B × C) = Fintype.card A * Fintype.card B * Fintype.card C := by
  simp [Fintype.card_prod, mul_assoc]

end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end OAI

end PairingModule1

section PairingModule2
namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K : Type*} [CommSemiring K]

def dotPairingMatrixX (U : Type*) : (Unit × U) ≃ U where
  toFun x := x.2
  invFun x := ((), x)
  left_inv := by rintro ⟨⟨⟩, x⟩; rfl
  right_inv x := rfl

def dotPairingMatrixY (U : Type*) : (U × Unit) ≃ U where
  toFun y := y.1
  invFun y := (y, ())
  left_inv := by rintro ⟨y, ⟨⟩⟩; rfl
  right_inv y := rfl

def dotPairingMatrixZ : (Unit × Unit) ≃ Unit where
  toFun _ := ()
  invFun _ := ((), ())
  left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
  right_inv := by rintro ⟨⟩; rfl

theorem dotPairing_matrixCoefficients (U : Type*) [DecidableEq U] :
    pullback (dotPairingMatrixX U) (dotPairingMatrixY U) dotPairingMatrixZ
      (dotPairing (K := K) U) = matrixCoefficients Unit U Unit := by
  funext x y z
  change (if x.2 = y.1 then (1 : K) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) ↔ x.2 = y.1 :=
    ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  by_cases hxy : x.2 = y.1
  · calc
      (if x.2 = y.1 then (1 : K) else 0) = 1 := if_pos hxy
      _ = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) :=
        (if_pos (hguard.mpr hxy)).symm
  · have hfull : ¬ (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
      fun h => hxy (hguard.mp h)
    calc
      (if x.2 = y.1 then (1 : K) else 0) = 0 := if_neg hxy
      _ = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) :=
        (if_neg hfull).symm

theorem matrixCoefficients_rank_of_dotPairing {U : Type*} [DecidableEq U] {r : ℕ}
    (h : RankAtMost (dotPairing (K := K) U) r) :
    RankAtMost (matrixCoefficients (K := K) Unit U Unit) r := by
  have h' := h.pullback (dotPairingMatrixX U) (dotPairingMatrixY U) dotPairingMatrixZ
  rw [dotPairing_matrixCoefficients] at h'
  exact h'

def pairingTriple (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K ((B × A) × Unit) ((B × Unit) × C) ((Unit × A) × C) :=
  product (product (dotPairing B) (cyclic (dotPairing A)))
    (cyclic (cyclic (dotPairing C)))

def pairingTripleMatrixX (A B : Type*) : (A × B) ≃ ((B × A) × Unit) where
  toFun x := ((x.2, x.1), ())
  invFun x := (x.1.2, x.1.1)
  left_inv x := rfl
  right_inv := by rintro ⟨⟨b, a⟩, ⟨⟩⟩; rfl

def pairingTripleMatrixY (B C : Type*) : (B × C) ≃ ((B × Unit) × C) where
  toFun y := ((y.1, ()), y.2)
  invFun y := (y.1.1, y.2)
  left_inv y := rfl
  right_inv := by rintro ⟨⟨b, ⟨⟩⟩, c⟩; rfl

def pairingTripleMatrixZ (C A : Type*) : (C × A) ≃ ((Unit × A) × C) where
  toFun z := (((), z.2), z.1)
  invFun z := (z.2, z.1.2)
  left_inv z := rfl
  right_inv := by rintro ⟨⟨⟨⟩, a⟩, c⟩; rfl

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem pairingTriple_matrixCoefficients :
    pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
      (pairingTripleMatrixZ C A) (pairingTriple (K := K) A B C) =
      matrixCoefficients A B C := by
  funext x y z
  change ((if x.2 = y.1 then (1 : K) else 0) *
    (if z.2 = x.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : ((x.2 = y.1 ∧ z.2 = x.1) ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

theorem matrixCoefficients_rank_of_pairingTriple {r : ℕ}
    (h : RankAtMost (pairingTriple (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) A B C) r := by
  have h' := h.pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
    (pairingTripleMatrixZ C A)
  rw [pairingTriple_matrixCoefficients] at h'
  exact h'

theorem matrixCoefficients_directSum_rank_of_pairingTriple
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => pairingTriple (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r := by
  have h' := h.directSum_pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
    (pairingTripleMatrixZ C A)
  simpa only [pairingTriple_matrixCoefficients] using h'

end Tensor
end MatrixMultiplication.Foundation

end OAI

end PairingModule2



end AllFieldsModule6
/- END all-fields module GenericPairing -/

/- BEGIN all-fields module Interpolation -/
section AllFieldsModule7

set_option autoImplicit false

section GenericInterpolation
namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {F X Y Z : Type*} [Field F]

theorem coeff_eq_sum_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → F) (hnodes : Function.Injective nodes)
    (p : Polynomial F) (d : ℕ) (hdegree : p.degree < Fintype.card ι) :
    p.coeff d = ∑ i, p.eval (nodes i) *
      (Lagrange.basis Finset.univ nodes i).coeff d := by
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset ι)) := hnodes.injOn
  have hinterp := Lagrange.eq_interpolate hinj (by simpa using hdegree)
    (f := p)
  calc
    p.coeff d = (Lagrange.interpolate Finset.univ nodes
        (fun i => p.eval (nodes i))).coeff d := congrArg (fun q => q.coeff d) hinterp
    _ = _ := by
      simp only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff,
        Polynomial.coeff_C_mul]

theorem RankAtMost.coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → F) (hnodes : Function.Injective nodes)
    {P : Tensor (Polynomial F) X Y Z} {r : ℕ} (hP : RankAtMost P r)
    (d : ℕ) (hdegree : ∀ x y z, (P x y z).degree < Fintype.card ι) :
    RankAtMost (fun x y z => (P x y z).coeff d) (Fintype.card ι * r) := by
  rcases hP with ⟨a, b, c, rfl⟩
  let w : ι → F := fun i => (Lagrange.basis Finset.univ nodes i).coeff d
  let aa : (ι × Fin r) → X → F := fun i x => w i.1 * (a i.2 x).eval (nodes i.1)
  let bb : (ι × Fin r) → Y → F := fun i y => (b i.2 y).eval (nodes i.1)
  let cc : (ι × Fin r) → Z → F := fun i z => (c i.2 z).eval (nodes i.1)
  have heq : (fun x y z => (∑ j, rankOne (a j) (b j) (c j) x y z).coeff d) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    rw [coeff_eq_sum_eval nodes hnodes _ d (hdegree x y z)]
    simp only [Fintype.sum_prod_type, rankOne, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [aa, bb, cc, w]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

structure PolynomialApproximation (T : Tensor F X Y Z) (r d D : ℕ) where
  polynomial : Tensor (Polynomial F) X Y Z
  rank_bound : RankAtMost polynomial r
  vanishes : ∀ x y z k, k < d → (polynomial x y z).coeff k = 0
  leading : ∀ x y z, (polynomial x y z).coeff d = T x y z
  degree_bound : ∀ x y z, (polynomial x y z).degree ≤ D

namespace PolynomialApproximation

variable {T : Tensor F X Y Z} {r d D : ℕ}

def normalized (A : PolynomialApproximation T r d D) :
    Tensor (Polynomial F) X Y Z :=
  fun x y z => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem polynomial_eq (A : PolynomialApproximation T r d D) (x : X) (y : Y) (z : Z) :
    A.polynomial x y z = Polynomial.X ^ d * A.normalized x y z :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem normalized_constant (A : PolynomialApproximation T r d D)
    (x : X) (y : Y) (z : Z) : (A.normalized x y z).coeff 0 = T x y z := by
  have h := A.leading x y z
  rw [A.polynomial_eq] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using h

theorem power_polynomial_eq (A : PolynomialApproximation T r d D) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
    Tensor.power A.polynomial n x y z =
      Polynomial.X ^ (d * n) * Tensor.power A.normalized n x y z := by
  simp [Tensor.power, A.polynomial_eq, Finset.prod_mul_distrib, ← pow_mul]

def power (A : PolynomialApproximation T r d D) (n : ℕ) :
    PolynomialApproximation (Tensor.power T n) (r ^ n) (d * n) (D * n) where
  polynomial := Tensor.power A.polynomial n
  rank_bound := A.rank_bound.power n
  vanishes := by
    intro x y z k hk
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false]
  leading := by
    intro x y z
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      Tensor.power, Polynomial.coeff_zero_prod, A.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    calc
      (Tensor.power A.polynomial n x y z).natDegree ≤
          ∑ i, (A.polynomial (x i) (y i) (z i)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin n, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact Polynomial.natDegree_le_of_degree_le (A.degree_bound (x i) (y i) (z i))
      _ = D * n := by simp [Nat.mul_comm]

theorem rank_power [Infinite F] (A : PolynomialApproximation T r d D) (n : ℕ) :
    RankAtMost (Tensor.power T n) ((D * n + 1) * r ^ n) := by
  let nodes : Fin (D * n + 1) → F := fun i => Infinite.natEmbedding F i.val
  have hinj : Function.Injective nodes := by
    intro i j h
    apply Fin.ext
    exact (Infinite.natEmbedding F).injective h
  have hdegree (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
      ((A.power n).polynomial x y z).degree < Fintype.card (Fin (D * n + 1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt ((A.power n).degree_bound x y z)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (D * n)))
  have h := (A.power n).rank_bound.coeff nodes hinj (d * n) hdegree
  have heq : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power T n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [heq, Fintype.card_fin] at h
  exact h

end PolynomialApproximation
end Tensor
end MatrixMultiplication.Foundation
end
end OAI

end GenericInterpolation



end AllFieldsModule7
/- END all-fields module Interpolation -/

/- BEGIN all-fields module GenericPolynomialMaps -/
section AllFieldsModule8

set_option autoImplicit false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section ScalarRestriction

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]
variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_scalar_mul (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (P : Tensor K X Y Z) (s : K) :
    restrict A B C (fun x y z => s * P x y z) =
      fun x' y' z' => s * restrict A B C P x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem cyclic_restrict (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (P : Tensor K X Y Z) :
    cyclic (restrict A B C P) = restrict B C A (cyclic P) := by
  funext y' z' x'
  simp only [cyclic, restrict]
  calc
    (∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * P x y z) =
        ∑ y, ∑ x, ∑ z, A x' x * B y' y * C z' z * P x y z :=
      Finset.sum_comm
    _ = ∑ y, ∑ z, ∑ x, A x' x * B y' y * C z' z * P x y z := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro x hx
      ring

end ScalarRestriction

section PolynomialCoefficients

variable {F : Type*} [Field F]

theorem coeff_mul_expand_eq_constant (M p : Polynomial F) (a : F)
    (hp : p.coeff 0 = a) (k j : ℕ) (hj : j ≤ k) :
    (M * Polynomial.expand F (k + 1) p).coeff j =
      (M * Polynomial.C a).coeff j := by
  have hdiv : Polynomial.X ∣ p - Polynomial.C a :=
    Polynomial.X_dvd_iff.mpr (by simp only [Polynomial.coeff_sub,
      Polynomial.coeff_C_zero, hp, sub_self])
  rcases hdiv with ⟨q, hq⟩
  have hpq : p = Polynomial.C a + Polynomial.X * q := by
    rw [← hq]
    ring
  have hexpand : Polynomial.expand F (k + 1) p =
      Polynomial.C a + Polynomial.X ^ (k + 1) *
        Polynomial.expand F (k + 1) q := by
    rw [hpq, map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X]
  have hmul : M * Polynomial.expand F (k + 1) p =
      M * Polynomial.C a + Polynomial.X ^ (k + 1) *
        (M * Polynomial.expand F (k + 1) q) := by
    rw [hexpand]
    ring
  rw [hmul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_neg (by omega), add_zero]

end PolynomialCoefficients

section PolynomialLocalMaps

variable {F X Y Z X' Y' Z' : Type*} [Field F]
variable [Fintype X] [Fintype Y] [Fintype Z]

structure PolynomialRestrictionDegeneration
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k Lx Ly Lz : ℕ) where
  leftMap : X' → X → Polynomial F
  middleMap : Y' → Y → Polynomial F
  rightMap : Z' → Z → Polynomial F
  left_degree : ∀ x' x, (leftMap x' x).degree ≤ Lx
  middle_degree : ∀ y' y, (middleMap y' y).degree ≤ Ly
  right_degree : ∀ z' z, (rightMap z' z).degree ≤ Lz
  vanishes : ∀ x' y' z' j, j < k →
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff j = 0
  leading : ∀ x' y' z',
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff k = U x' y' z'

namespace PolynomialRestrictionDegeneration

variable {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'}
variable {k Lx Ly Lz r d D : ℕ}

def cyclic (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    PolynomialRestrictionDegeneration (Tensor.cyclic T) (Tensor.cyclic U) k Ly Lz Lx where
  leftMap := L.middleMap
  middleMap := L.rightMap
  rightMap := L.leftMap
  left_degree := L.middle_degree
  middle_degree := L.right_degree
  right_degree := L.left_degree
  vanishes := by
    intro y' z' x' j hj
    change (restrict L.middleMap L.rightMap L.leftMap
      (Tensor.cyclic (fun x y z => Polynomial.C (T x y z))) y' z' x').coeff j = 0
    rw [← cyclic_restrict]
    exact L.vanishes x' y' z' j hj
  leading := by
    intro y' z' x'
    change (restrict L.middleMap L.rightMap L.leftMap
      (Tensor.cyclic (fun x y z => Polynomial.C (T x y z))) y' z' x').coeff k =
        Tensor.cyclic U y' z' x'
    rw [← cyclic_restrict]
    exact L.leading x' y' z'

def basePolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap (fun x y z => Polynomial.C (T x y z))

def compositionPolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) : Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap
    (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z))

def normalizedComposition (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) : Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap
    (fun x y z => Polynomial.expand F (k + 1) (W.normalized x y z))

theorem compositionPolynomial_eq
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (x' : X') (y' : Y') (z' : Z') :
    L.compositionPolynomial W x' y' z' =
      Polynomial.X ^ (d * (k + 1)) * L.normalizedComposition W x' y' z' := by
  have hpoint : (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z)) =
      fun x y z => Polynomial.X ^ (d * (k + 1)) *
        Polynomial.expand F (k + 1) (W.normalized x y z) := by
    funext x y z
    rw [W.polynomial_eq, map_mul, map_pow, Polynomial.expand_X]
    simp only [← pow_mul, Nat.mul_comm]
  unfold compositionPolynomial normalizedComposition
  rw [hpoint, restrict_scalar_mul]

theorem normalizedComposition_coeff
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (j : ℕ) (hj : j ≤ k)
    (x' : X') (y' : Y') (z' : Z') :
    (L.normalizedComposition W x' y' z').coeff j =
      (L.basePolynomial x' y' z').coeff j := by
  simp only [normalizedComposition, basePolynomial, restrict, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  exact coeff_mul_expand_eq_constant
    (L.leftMap x' x * L.middleMap y' y * L.rightMap z' z)
    (W.normalized x y z) (T x y z) (W.normalized_constant x y z) k j hj

theorem compositionPolynomial_rank
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    RankAtMost (L.compositionPolynomial W) r :=
  (W.rank_bound.map (Polynomial.expand F (k + 1)).toRingHom).restrict
    L.leftMap L.middleMap L.rightMap

theorem compositionPolynomial_degree
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (x' : X') (y' : Y') (z' : Z') :
    (L.compositionPolynomial W x' y' z').degree ≤ D * (k + 1) + Lx + Ly + Lz := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold compositionPolynomial restrict
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y hy
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z hz
  have hA := Polynomial.natDegree_le_of_degree_le (L.left_degree x' x)
  have hB := Polynomial.natDegree_le_of_degree_le (L.middle_degree y' y)
  have hC := Polynomial.natDegree_le_of_degree_le (L.right_degree z' z)
  have hP : (Polynomial.expand F (k + 1) (W.polynomial x y z)).natDegree ≤
      D * (k + 1) := by
    rw [Polynomial.natDegree_expand]
    exact Nat.mul_le_mul_right (k + 1)
      (Polynomial.natDegree_le_of_degree_le (W.degree_bound x y z))
  have hprod := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le hA hB) hC) hP
  change (L.leftMap x' x * L.middleMap y' y * L.rightMap z' z *
    Polynomial.expand F (k + 1) (W.polynomial x y z)).natDegree ≤
      D * (k + 1) + Lx + Ly + Lz
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprod

def compose (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    PolynomialApproximation U r (d * (k + 1) + k) (D * (k + 1) + Lx + Ly + Lz) where
  polynomial := L.compositionPolynomial W
  rank_bound := L.compositionPolynomial_rank W
  vanishes := by
    intro x' y' z' j hj
    rw [L.compositionPolynomial_eq W, Polynomial.coeff_X_pow_mul']
    split_ifs with hdj
    · have hjk : j - d * (k + 1) < k := by omega
      rw [L.normalizedComposition_coeff W _ (Nat.le_of_lt hjk)]
      exact L.vanishes x' y' z' _ hjk
    · rfl
  leading := by
    intro x' y' z'
    rw [L.compositionPolynomial_eq W, Polynomial.coeff_X_pow_mul']
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
    rw [L.normalizedComposition_coeff W k le_rfl]
    exact L.leading x' y' z'
  degree_bound := L.compositionPolynomial_degree W

@[simp] theorem compose_polynomial
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    (L.compose W).polynomial = restrict L.leftMap L.middleMap L.rightMap
      (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z)) := rfl

end PolynomialRestrictionDegeneration

end PolynomialLocalMaps

end Tensor
end MatrixMultiplication.Foundation

end

end OAI



end AllFieldsModule8
/- END all-fields module GenericPolynomialMaps -/

/- BEGIN all-fields module GenericNonzeroInterpolation -/
section AllFieldsModule9

set_option autoImplicit false

namespace OAI

/-!
# Exact interpolation away from zero

The coefficient-extraction theorem already proved for matrix multiplication is
used here with distinct nonzero nodes in an arbitrary infinite field.  In particular a polynomial
degeneration can be recovered by a finite sum of its ordinary restrictions at
nonzero parameters, with the leading power divided out at each parameter.
-/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

variable {K : Type*} [Field K] [Infinite K]

/-- Choose infinitely many distinct nonzero elements without a characteristic assumption. -/
private def nonzeroInterpolationEmbedding (K : Type*) [Zero K] [Infinite K] :
    ℕ ↪ {x : K // x ≠ 0} := by
  have hs : ({x : K | x ≠ 0} : Set K).Infinite := by
    have hset : {x : K | x ≠ 0} = ({0} : Set K)ᶜ := by
      ext x
      simp
    rw [hset]
    exact (Set.finite_singleton (0 : K)).infinite_compl
  letI : Infinite {x : K // x ≠ 0} := Set.infinite_coe_iff.mpr hs
  exact Infinite.natEmbedding _

/-- An injective family of nonzero interpolation parameters in an infinite field. -/
def interpolationNode (D : ℕ) (i : Fin (D + 1)) : K :=
  (nonzeroInterpolationEmbedding K i.val).val

theorem interpolationNode_injective (D : ℕ) :
    Function.Injective (interpolationNode (K := K) D) := by
  intro i j hij
  apply Fin.ext
  apply (nonzeroInterpolationEmbedding K).injective
  exact Subtype.ext hij

theorem interpolationNode_ne_zero (D : ℕ) (i : Fin (D + 1)) :
    interpolationNode (K := K) D i ≠ 0 :=
  (nonzeroInterpolationEmbedding K i.val).property

/-- The constant-coefficient functional expressed in the Lagrange basis. -/
def constantInterpolationWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → K) (i : ι) : K :=
  (Lagrange.basis Finset.univ nodes i).coeff 0

omit [Infinite K] in
/-- Exact constant recovery; this specializes the existing coefficient theorem. -/
theorem constant_eq_sum_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → K) (hinj : Function.Injective nodes) (p : Polynomial K)
    (hdegree : p.degree < Fintype.card ι) :
    p.coeff 0 = ∑ i, constantInterpolationWeight nodes i * p.eval (nodes i) := by
  simpa only [constantInterpolationWeight, mul_comm] using
    Tensor.coeff_eq_sum_eval nodes hinj p 0 hdegree

/-- A degree-`D` polynomial is recovered at zero using only nonzero parameters. -/
theorem constant_eq_sum_nonzero_eval (D : ℕ) (p : Polynomial K)
    (hdegree : p.degree ≤ D) :
    p.coeff 0 = ∑ i, constantInterpolationWeight (interpolationNode D) i *
      p.eval (interpolationNode D i) := by
  apply constant_eq_sum_eval _ (interpolationNode_injective D)
  simp only [Fintype.card_fin]
  exact lt_of_le_of_lt hdegree (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))

omit [Infinite K] in
/-- Removing a leading power before interpolation only requires evaluations at
nonzero nodes.  The degree bound is on the normalized polynomial. -/
theorem leading_eq_sum_normalized_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → K) (hinj : Function.Injective nodes)
    (hnonzero : ∀ i, nodes i ≠ 0) (p q : Polynomial K) (d : ℕ)
    (hp : p = Polynomial.X ^ d * q) (hdegree : q.degree < Fintype.card ι) :
    p.coeff d = ∑ i, constantInterpolationWeight nodes i *
      (nodes i ^ d)⁻¹ * p.eval (nodes i) := by
  have hcoeff : p.coeff d = q.coeff 0 := by
    rw [hp, Polynomial.coeff_X_pow_mul']
    simp
  rw [hcoeff, constant_eq_sum_eval nodes hinj q hdegree]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hp, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  have hpow : nodes i ^ d ≠ 0 := pow_ne_zero d (hnonzero i)
  calc
    constantInterpolationWeight nodes i * q.eval (nodes i) =
        constantInterpolationWeight nodes i *
          ((nodes i ^ d)⁻¹ * (nodes i ^ d)) * q.eval (nodes i) := by
            rw [inv_mul_cancel₀ hpow, mul_one]
    _ = _ := by ring

/-- A leading coefficient is a finite linear combination of normalized
evaluations, assuming all lower coefficients vanish. -/
theorem leading_eq_sum_nonzero_eval (D d : ℕ) (p : Polynomial K)
    (hvanish : ∀ j < d, p.coeff j = 0) (hdegree : p.degree ≤ D) :
    p.coeff d = ∑ i, constantInterpolationWeight (interpolationNode D) i *
      (interpolationNode D i ^ d)⁻¹ * p.eval (interpolationNode D i) := by
  obtain ⟨q, hp⟩ := Polynomial.X_pow_dvd_iff.mpr hvanish
  apply leading_eq_sum_normalized_eval _ (interpolationNode_injective D)
    (interpolationNode_ne_zero D) p q d hp
  have hqdegree : q.degree ≤ p.degree := by
    rw [hp, mul_comm]
    exact Polynomial.degree_le_mul_left q (pow_ne_zero d Polynomial.X_ne_zero)
  simp only [Fintype.card_fin]
  exact lt_of_le_of_lt (le_trans hqdegree hdegree)
    (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))

section PolynomialRestriction

variable {X Y Z X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor K X Y Z} {U : Tensor K X' Y' Z'}
variable {k Lx Ly Lz : ℕ}

omit [Infinite K] in
/-- Evaluating the polynomial restriction evaluates its three local maps. -/
theorem restrictionDegeneration_eval
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (t : K) (x' : X') (y' : Y') (z' : Z') :
    (L.basePolynomial x' y' z').eval t =
      Tensor.restrict (fun a x => (L.leftMap a x).eval t)
        (fun b y => (L.middleMap b y).eval t)
        (fun c z => (L.rightMap c z).eval t) T x' y' z' := by
  simp only [Tensor.PolynomialRestrictionDegeneration.basePolynomial, Tensor.restrict,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]

omit [Infinite K] in
/-- The degree of a polynomial restriction is bounded by the sum of the
degrees of its three local maps. -/
theorem restrictionDegeneration_degree
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (x' : X') (y' : Y') (z' : Z') :
    (L.basePolynomial x' y' z').degree ≤ (Lx + Ly + Lz : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold Tensor.PolynomialRestrictionDegeneration.basePolynomial Tensor.restrict
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y hy
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z hz
  have hA := Polynomial.natDegree_le_of_degree_le (L.left_degree x' x)
  have hB := Polynomial.natDegree_le_of_degree_le (L.middle_degree y' y)
  have hC := Polynomial.natDegree_le_of_degree_le (L.right_degree z' z)
  have hconstant : (Polynomial.C (T x y z)).natDegree ≤ 0 := by simp
  simpa using Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le hA hB) hC) hconstant

/-- The existing polynomial-approximation API applies to a polynomial
restriction as soon as the source tensor has a rank bound. -/
def restrictionDegeneration_approximation
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    {r : ℕ} (hT : Tensor.RankAtMost T r) :
    Tensor.PolynomialApproximation U r k (Lx + Ly + Lz) where
  polynomial := L.basePolynomial
  rank_bound := (hT.map Polynomial.C).restrict L.leftMap L.middleMap L.rightMap
  vanishes := L.vanishes
  leading := L.leading
  degree_bound := restrictionDegeneration_degree L

/-- Interpolation after tensor powering has a linear degree overhead, rather
than raising the single-copy interpolation overhead to the tensor power. -/
theorem restrictionDegeneration_power_rankAtMost
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    {r : ℕ} (hT : Tensor.RankAtMost T r) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power U n) (((Lx + Ly + Lz) * n + 1) * r ^ n) :=
  (restrictionDegeneration_approximation L hT).rank_power n

/-- A polynomial degeneration yields an exact finite sum of ordinary
restrictions at nonzero parameters.  There are `Lx + Ly + Lz + 1` terms. -/
theorem restrictionDegeneration_recovery
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (x' : X') (y' : Y') (z' : Z') :
    U x' y' z' = ∑ i,
      constantInterpolationWeight (interpolationNode (Lx + Ly + Lz)) i *
      (interpolationNode (Lx + Ly + Lz) i ^ k)⁻¹ *
      Tensor.restrict
        (fun a x => (L.leftMap a x).eval (interpolationNode (Lx + Ly + Lz) i))
        (fun b y => (L.middleMap b y).eval (interpolationNode (Lx + Ly + Lz) i))
        (fun c z => (L.rightMap c z).eval (interpolationNode (Lx + Ly + Lz) i))
        T x' y' z' := by
  rw [← L.leading x' y' z']
  change (L.basePolynomial x' y' z').coeff k = _
  rw [leading_eq_sum_nonzero_eval (Lx + Ly + Lz) k
    (L.basePolynomial x' y' z') (L.vanishes x' y' z')
    (restrictionDegeneration_degree L x' y' z')]
  simp_rw [restrictionDegeneration_eval]

/-- Finite interpolation converts a polynomial degeneration into an exact
rank bound with its explicit number of evaluation parameters. -/
theorem restrictionDegeneration_rankAtMost
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    {r : ℕ} (hT : Tensor.RankAtMost T r) :
    Tensor.RankAtMost U ((Lx + Ly + Lz + 1) * r) := by
  have hbase := (hT.map Polynomial.C).restrict L.leftMap L.middleMap L.rightMap
  change Tensor.RankAtMost L.basePolynomial r at hbase
  have hdegree (x' : X') (y' : Y') (z' : Z') :
      (L.basePolynomial x' y' z').degree <
        Fintype.card (Fin (Lx + Ly + Lz + 1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (restrictionDegeneration_degree L x' y' z')
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (Lx + Ly + Lz)))
  have h := hbase.coeff (interpolationNode (Lx + Ly + Lz))
    (interpolationNode_injective _) k hdegree
  have hleading : (fun x' y' z' => (L.basePolynomial x' y' z').coeff k) = U := by
    funext x' y' z'
    exact L.leading x' y' z'
  simpa only [hleading, Fintype.card_fin] using h

end PolynomialRestriction

end MatrixMultiplication.AuxiliarySeparation

end

end OAI



end AllFieldsModule9
/- END all-fields module GenericNonzeroInterpolation -/

/- BEGIN all-fields module GenericCharacterLaws -/
section AllFieldsModule10

set_option autoImplicit false

section DotCharacter
namespace OAI

/-!
# Dot-product exponents of tensor characters

The power laws here follow from restriction monotonicity and tensor products.
They are not additional assumptions on a character. The three exponents refer
to the leg on which the corresponding dot product has dimension one.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {K : Type*} [Field K]
variable (χ : Character K)

theorem value_pos {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} (hT : T ≠ 0) : 0 < χ.value T :=
  lt_of_lt_of_le zero_lt_one (χ.one_le_value hT)

/-- Precomposing a character with a cyclic permutation gives a character. -/
def cyclicCharacter : Character K where
  value T := χ.value (Tensor.cyclic T)
  nonneg T := χ.nonneg (Tensor.cyclic T)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    rw [Tensor.cyclic_directSum, χ.map_directSum]
  map_product T S := χ.map_product (Tensor.cyclic T) (Tensor.cyclic S)
  monotone T A B C := by
    have heq : Tensor.cyclic (Tensor.restrict A B C T) =
        Tensor.restrict B C A (Tensor.cyclic T) := by
      funext y z x
      simp only [Tensor.cyclic, Tensor.restrict]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq]
    exact χ.monotone (Tensor.cyclic T) B C A

@[simp] theorem cyclicCharacter_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    χ.cyclicCharacter.value T = χ.value (Tensor.cyclic T) := rfl

private theorem dotPairing_ne_zero {m : ℕ} (hm : 0 < m) :
    Tensor.dotPairing (K := K) (Fin m) ≠ 0 := by
  intro h
  have hv := congrFun (congrFun (congrFun h ⟨0, hm⟩) ⟨0, hm⟩) ()
  simp [Tensor.dotPairing] at hv

private theorem dotPairing_rank (m : ℕ) :
    Tensor.RankAtMost (Tensor.dotPairing (K := K) (Fin m)) m := by
  let a : Fin m → Fin m → K := fun i j => if i = j then 1 else 0
  have heq : Tensor.dotPairing (K := K) (Fin m) =
      fun x y z => ∑ i, Tensor.rankOne (a i) (a i) (fun _ : Unit => 1) x y z := by
    funext x y z
    simp [Tensor.dotPairing, Tensor.rankOne, a, mul_ite, eq_comm]
  rw [heq]
  simpa using Tensor.rankAtMost_sum_rankOne a a (fun (_ : Fin m) (_ : Unit) => (1 : K))

theorem value_dotPairing_pos {m : ℕ} (hm : 0 < m) :
    0 < χ.value (Tensor.dotPairing (K := K) (Fin m)) :=
  χ.value_pos (dotPairing_ne_zero hm)

theorem value_dotPairing_le (m : ℕ) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) ≤ m :=
  χ.value_le_rank (dotPairing_rank m)

theorem value_dotPairing_mono {m n : ℕ} (hmn : m ≤ n) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) ≤
      χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback (Fin.castLE hmn) (Fin.castLE hmn) id
      (Tensor.dotPairing (K := K) (Fin n)) = Tensor.dotPairing (K := K) (Fin m) := by
    funext x y z
    simp [Tensor.pullback, Tensor.dotPairing]
  rw [← heq]
  exact χ.value_pullback_le _ _ _ _

theorem value_dotPairing_mul (m n : ℕ) :
    χ.value (Tensor.dotPairing (K := K) (Fin (m * n))) =
      χ.value (Tensor.dotPairing (K := K) (Fin m)) *
        χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback finProdFinEquiv.symm finProdFinEquiv.symm
      (Equiv.prodUnique Unit Unit).symm
      (Tensor.product (Tensor.dotPairing (K := K) (Fin m))
        (Tensor.dotPairing (K := K) (Fin n))) =
      Tensor.dotPairing (K := K) (Fin (m * n)) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing,
      ite_zero_mul_ite_zero, one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  rw [← heq, χ.value_reindex, χ.map_product]

/-- The exponent on dot products whose third leg has dimension one. -/
def pZ : ℝ :=
  Real.log (χ.value (Tensor.dotPairing (K := K) (Fin 2))) / Real.log 2

/-- The exponent on dot products whose second leg has dimension one. -/
def pY : ℝ := χ.cyclicCharacter.pZ

/-- The exponent on dot products whose first leg has dimension one. -/
def pX : ℝ := χ.cyclicCharacter.cyclicCharacter.pZ

theorem pZ_nonneg : 0 ≤ χ.pZ := by
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  exact Real.log_nonneg (χ.one_le_value (dotPairing_ne_zero (by norm_num)))

theorem pZ_le_one : χ.pZ ≤ 1 := by
  apply (div_le_one (Real.log_pos (by norm_num))).2
  exact Real.log_le_log (χ.value_dotPairing_pos (by norm_num)) (χ.value_dotPairing_le 2)

theorem pY_nonneg : 0 ≤ χ.pY := χ.cyclicCharacter.pZ_nonneg
theorem pY_le_one : χ.pY ≤ 1 := χ.cyclicCharacter.pZ_le_one
theorem pX_nonneg : 0 ≤ χ.pX := χ.cyclicCharacter.cyclicCharacter.pZ_nonneg
theorem pX_le_one : χ.pX ≤ 1 := χ.cyclicCharacter.cyclicCharacter.pZ_le_one

theorem value_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) = (m : ℝ) ^ χ.pZ := by
  apply positiveMultiplicative_eq_rpow
    (f := fun m => χ.value (Tensor.dotPairing (K := K) (Fin m)))
    (fun n hn => χ.value_dotPairing_pos hn)
    (fun m n _ _ => χ.value_dotPairing_mul m n)
    (fun _ _ _ _ hmn => χ.value_dotPairing_mono hmn) hm

theorem value_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m))) =
      (m : ℝ) ^ χ.pY :=
  χ.cyclicCharacter.value_dotPairing hm

theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m)))) =
      (m : ℝ) ^ χ.pX :=
  χ.cyclicCharacter.cyclicCharacter.value_dotPairing hm

/-- Exact factorization through the three oriented dot products. -/
theorem value_matrixCoefficients {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    χ.value (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) =
      (b : ℝ) ^ χ.pZ * (a : ℝ) ^ χ.pY * (c : ℝ) ^ χ.pX := by
  rw [← Tensor.pairingTriple_matrixCoefficients, χ.value_reindex]
  simp only [Tensor.pairingTriple, χ.map_product, χ.value_dotPairing hb,
    χ.value_cyclic_dotPairing ha, χ.value_cyclic_cyclic_dotPairing hc]

/-- The character of square matrix multiplication has exponent `pX + pY + pZ`. -/
theorem value_matrixCoefficients_square {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.matrixCoefficients (K := K) (Fin m) (Fin m) (Fin m)) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  rw [χ.value_matrixCoefficients hm hm hm]
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [Real.rpow_add hm', Real.rpow_add hm']
  ring

/-- The same power law in the matrix-tensor notation used for exact rank. -/
theorem value_matrixMultiplication {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.matrixMultiplication m m m) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  simpa only [Tensor.matrixMultiplication_eq_matrixCoefficients] using
    χ.value_matrixCoefficients_square hm

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end DotCharacter

section DegenerationCharacter
namespace OAI

/-!
# Characters decrease under polynomial degeneration

Finite interpolation expresses a polynomial's leading coefficient as a sum
of evaluations.  Applying it after tensor powering gives only a linear
overhead, which disappears in the exponential growth rate.  No continuity
assumption on the character is used.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

variable {K : Type*} [Field K] [Infinite K]
variable (χ : Character K)
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Scalar multiplication is a restriction, including when the scalar is zero. -/
theorem value_scale_le (c : K) (T : Tensor K X Y Z) :
    χ.value (fun x y z => c * T x y z) ≤ χ.value T := by
  classical
  have heq : Tensor.restrict
      (fun x' x => if x = x' then c else 0)
      (fun y' y => if y = y' then 1 else 0)
      (fun z' z => if z = z' then 1 else 0) T =
      fun x y z => c * T x y z := by
    funext x y z
    simp [Tensor.restrict, ite_mul, mul_ite]
  simpa only [heq] using χ.monotone T
    (fun x' x => if x = x' then c else 0)
    (fun y' y => if y = y' then 1 else 0)
    (fun z' z => if z = z' then 1 else 0)

/-- Nonzero scalar multiplication preserves a character. -/
theorem value_scale (c : K) (hc : c ≠ 0) (T : Tensor K X Y Z) :
    χ.value (fun x y z => c * T x y z) = χ.value T := by
  apply le_antisymm (χ.value_scale_le c T)
  have h := χ.value_scale_le c⁻¹ (fun x y z => c * T x y z)
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h

/-- Adding tensors is a restriction of their independent direct sum. -/
theorem value_sum_le {ι : Type} [Fintype ι] (T : ι → Tensor K X Y Z) :
    χ.value (fun x y z => ∑ i, T i x y z) ≤ ∑ i, χ.value (T i) := by
  classical
  have heq : Tensor.restrict
      (fun x (p : ι × X) => if p.2 = x then 1 else 0)
      (fun y (p : ι × Y) => if p.2 = y then 1 else 0)
      (fun z (p : ι × Z) => if p.2 = z then 1 else 0)
      (Tensor.directSum T) = fun x y z => ∑ i, T i x y z := by
    funext x y z
    simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
      ite_mul, mul_ite, ite_and]
  rw [← χ.map_directSum T, ← heq]
  exact χ.monotone (Tensor.directSum T) _ _ _

/-- Exact interpolation bounds any polynomial coefficient by the sum of the
character values of finitely many evaluation tensors. -/
theorem value_coefficient_le (P : Tensor (Polynomial K) X Y Z) (d D : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree ≤ D) :
    χ.value (fun x y z => (P x y z).coeff d) ≤
      ∑ i : Fin (D + 1), χ.value (fun x y z => (P x y z).eval (interpolationNode D i)) := by
  classical
  let w : Fin (D + 1) → K := fun i =>
    (Lagrange.basis Finset.univ (interpolationNode D) i).coeff d
  have heq : (fun x y z => (P x y z).coeff d) =
      fun x y z => ∑ i : Fin (D + 1), w i * (P x y z).eval (interpolationNode D i) := by
    funext x y z
    have hlt : (P x y z).degree < Fintype.card (Fin (D + 1)) := by
      simp only [Fintype.card_fin]
      exact lt_of_le_of_lt (hdegree x y z)
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))
    simpa only [w, mul_comm] using Tensor.coeff_eq_sum_eval
      (interpolationNode D) (interpolationNode_injective D) (P x y z) d hlt
  rw [heq]
  apply (χ.value_sum_le _).trans
  exact Finset.sum_le_sum fun i _ => χ.value_scale_le (w i) _

/-- A uniform bound on nonzero evaluations bounds the leading tensor.  The
proof uses tensor powers and removes their linear interpolation overhead. -/
theorem value_le_of_polynomialApproximation
    {U : Tensor K X Y Z} {r d D : ℕ}
    (A : Tensor.PolynomialApproximation U r d D) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ t : K, t ≠ 0 →
      χ.value (fun x y z => (A.polynomial x y z).eval t) ≤ b) :
    χ.value U ≤ b := by
  apply le_of_pow_le_linear_mul_pow (K := (D : ℝ)) hb
  intro n
  have hcoefficient := χ.value_coefficient_le (A.power n).polynomial
    (d * n) (D * n) (A.power n).degree_bound
  have hleading : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power U n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [hleading, χ.value_power] at hcoefficient
  apply hcoefficient.trans
  calc
    (∑ i : Fin (D * n + 1), χ.value
        (fun x y z => ((A.power n).polynomial x y z).eval
          (interpolationNode (D * n) i))) ≤
        ∑ _i : Fin (D * n + 1), b ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      have heval : (fun x y z => ((A.power n).polynomial x y z).eval
          (interpolationNode (D * n) i)) =
          Tensor.power (fun x y z => (A.polynomial x y z).eval
            (interpolationNode (D * n) i)) n := by
        funext x y z
        simp only [Tensor.PolynomialApproximation.power, Tensor.power,
          Polynomial.eval_prod]
      rw [heval, χ.value_power]
      exact pow_le_pow_left₀ (χ.nonneg _)
        (hbound _ (interpolationNode_ne_zero _ _)) n
    _ = ((n : ℝ) * (D : ℝ) + 1) * b ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring

omit [Fintype Z] in
private theorem exists_rankAtMost (T : Tensor K X Y Z) :
    ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y → X → K := fun p x => if p.1 = x then 1 else 0
  let b : X × Y → Y → K := fun p y => if p.2 = y then 1 else 0
  let c : X × Y → Z → K := fun p z => T p.1 p.2 z
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [Tensor.rankOne, a, b, c, Fintype.sum_prod_type, ite_mul, mul_ite]
  exact ⟨Fintype.card (X × Y), heq ▸ Tensor.rankAtMost_sum_rankOne a b c⟩

/-- The character axioms imply monotonicity under polynomial degeneration.
Continuity of the character is neither assumed nor used. -/
theorem value_polynomialRestrictionDegeneration_le
    {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor K X Y Z} {U : Tensor K X' Y' Z'} {k Lx Ly Lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    χ.value U ≤ χ.value T := by
  obtain ⟨r, hr⟩ := exists_rankAtMost T
  apply χ.value_le_of_polynomialApproximation
    (restrictionDegeneration_approximation L hr) (χ.nonneg T)
  intro t ht
  have heval : (fun x y z =>
      ((restrictionDegeneration_approximation L hr).polynomial x y z).eval t) =
      Tensor.restrict (fun x' x => (L.leftMap x' x).eval t)
        (fun y' y => (L.middleMap y' y).eval t)
        (fun z' z => (L.rightMap z' z).eval t) T := by
    funext x y z
    exact restrictionDegeneration_eval L t x y z
  rw [heval]
  exact χ.monotone T _ _ _

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end DegenerationCharacter



end AllFieldsModule10
/- END all-fields module GenericCharacterLaws -/

/- BEGIN all-fields module GenericConvolution -/
section AllFieldsModule11
set_option autoImplicit false

section Module0
namespace OAI
variable {K : Type*} [Field K]

/-!
# The polynomial multiplication tensor

The coefficient tensor `convolution (K := K) a b` represents multiplication of binary forms
of degrees `a - 1` and `b - 1`, or equivalently ordinary coefficient convolution.
The output leg has `a + b - 1` coordinates.  The definitions also make sense when
an input dimension is zero, while the nonzero and full-output-support statements
use the positive dimensions assumed in Section 5 of the paper.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- The tensor `C(a,b)` of Section 5, in monomial coefficient coordinates. -/
def convolution (a b : ℕ) : Tensor K (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

@[simp] theorem convolution_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl

@[simp] theorem convolution_ne_zero_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k ≠ 0 ↔ i.val + j.val = k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

@[simp] theorem convolution_eq_one_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k = 1 ↔ i.val + j.val = k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

@[simp] theorem convolution_eq_zero_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k = 0 ↔ i.val + j.val ≠ k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

/-- Every pair of input monomials has a valid output coordinate. -/
def convolutionOutput {a b : ℕ} (i : Fin a) (j : Fin b) : Fin (a + b - 1) :=
  ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩

@[simp] theorem convolution_at_output {a b : ℕ} (i : Fin a) (j : Fin b) :
    convolution (K := K) a b i j (convolutionOutput i j) = 1 := by
  simp [convolutionOutput]

/-- Every output monomial of the expected degree occurs in the product. -/
theorem convolution_output_supported {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (k : Fin (a + b - 1)) :
    ∃ (i : Fin a) (j : Fin b), convolution (K := K) a b i j k = 1 := by
  by_cases hk : k.val < a
  · exact ⟨⟨k.val, hk⟩, ⟨0, hb⟩, by simp⟩
  · have hk' := k.isLt
    refine ⟨⟨a - 1, by omega⟩, ⟨k.val - (a - 1), by omega⟩, ?_⟩
    apply (convolution_eq_one_iff _ _ _).mpr
    dsimp
    omega

theorem convolution_nonzero {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    convolution (K := K) a b ≠ 0 := by
  intro hz
  have hc := congrFun (congrFun (congrFun hz ⟨0, ha⟩) ⟨0, hb⟩)
    (convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩)
  change convolution (K := K) a b ⟨0, ha⟩ ⟨0, hb⟩
    (convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩) = 0 at hc
  rw [convolution_at_output] at hc
  exact one_ne_zero hc

theorem convolution_nonzero_iff (a b : ℕ) :
    convolution (K := K) a b ≠ 0 ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    constructor
    · by_contra ha
      have ha' : a = 0 := by omega
      subst a
      apply h
      funext i
      exact Fin.elim0 i
    · by_contra hb
      have hb' : b = 0 := by omega
      subst b
      apply h
      funext i j
      exact Fin.elim0 j
  · rintro ⟨ha, hb⟩
    exact convolution_nonzero ha hb

/-- Commuting the two inputs only casts the equal output dimensions. -/
theorem convolution_comm (a b : ℕ) (i : Fin a) (j : Fin b)
    (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k =
      convolution (K := K) b a j i (Fin.cast (by omega) k) := by
  simp only [convolution, Fin.val_cast, Nat.add_comm]

/-- The boundary tensor `C(1,b)` has the coefficient matrix of a dot product. -/
theorem convolution_one_left (b : ℕ) (i : Fin 1) (j : Fin b)
    (k : Fin (1 + b - 1)) :
    convolution (K := K) 1 b i j k = if j.val = k.val then 1 else 0 := by
  simp [convolution]

/-- The other boundary tensor has the same coordinate identity. -/
theorem convolution_one_right (a : ℕ) (i : Fin a) (j : Fin 1)
    (k : Fin (a + 1 - 1)) :
    convolution (K := K) a 1 i j k = if i.val = k.val then 1 else 0 := by
  simp [convolution]

/-- Relabel the output of `C(1,b)` by its actual dimension `b`. -/
def convolutionOneOutputEquiv (b : ℕ) : Fin b ≃ Fin (1 + b - 1) :=
  finCongr (by omega)

/-- Relabel the single input coordinate of `C(1,b)` by `Unit`. -/
def convolutionOneInputEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _i := Subsingleton.elim _ _

/-- `C(1,b)` is the dot-product tensor with the singleton on the first leg. -/
theorem convolution_one_left_dotPairing (b : ℕ) :
    Tensor.pullback convolutionOneInputEquiv (Equiv.refl (Fin b))
      (convolutionOneOutputEquiv b) (convolution (K := K) 1 b) =
      Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin b))) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff]

/-- Relabel the output of `C(a,1)` by its actual dimension `a`. -/
def convolutionRightOneOutputEquiv (a : ℕ) : Fin a ≃ Fin (a + 1 - 1) :=
  finCongr (by omega)

/-- `C(a,1)` is the dot-product tensor with the singleton on the second leg. -/
theorem convolution_one_right_dotPairing (a : ℕ) :
    Tensor.pullback (Equiv.refl (Fin a)) convolutionOneInputEquiv
      (convolutionRightOneOutputEquiv a) (convolution (K := K) a 1) =
      Tensor.cyclic (Tensor.dotPairing (K := K) (Fin a)) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionRightOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff, eq_comm]
  rfl

/-- Contracting the coefficient tensor computes ordinary finite convolution. -/
theorem contract_convolution {a b : ℕ} (x : Fin a → K) (y : Fin b → K)
    (k : Fin (a + b - 1)) :
    Tensor.contract (convolution (K := K) a b) x y k =
      ∑ i : Fin a, ∑ j : Fin b,
        if i.val + j.val = k.val then x i * y j else 0 := by
  simp [Tensor.contract, convolution, ite_mul]

end MatrixMultiplication.AuxiliarySeparation

end OAI

end Module0


section Module1
namespace OAI
variable {K : Type*} [Field K]

/-!
# Polynomial convolution (K := K) by evaluation and interpolation

Evaluating the two input polynomials at `a + b - 1` distinct complex points,
then interpolating their product, expresses the convolution (K := K) tensor as a sum
of `a + b - 1` rank-one tensors. This is the polynomial multiplication rank
upper bound used in Section 5.
-/

open scoped BigOperators
open Polynomial

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Recover each monomial coefficient from evaluations at distinct nodes. -/
lemma monomial_coeff_eq_sum_interpolation {n m : ℕ} (hm : m < n)
    (v : Fin n → K) (hv : Function.Injective v) (k : ℕ) :
    (if m = k then (1 : K) else 0) =
      ∑ r : Fin n, v r ^ m * (Lagrange.basis Finset.univ v r).coeff k := by
  have hdeg : (X ^ m : K[X]).degree < (Finset.univ : Finset (Fin n)).card := by
    simpa using hm
  have hpoly := Lagrange.eq_interpolate (f := (X ^ m : K[X])) hv.injOn hdeg
  have hcoeff := congrArg (fun p : K[X] => p.coeff k) hpoly
  simpa only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow, eq_comm] using hcoeff

/-- Evaluation at distinct nodes and Lagrange interpolation give an explicit
rank-one decomposition of polynomial convolution. -/
theorem convolution_eq_sum_rankOne {a b : ℕ}
    (v : Fin (a + b - 1) → K) (hv : Function.Injective v) :
    convolution (K := K) a b = fun i j k => ∑ r : Fin (a + b - 1),
      Tensor.rankOne (fun i : Fin a => v r ^ i.val)
        (fun j : Fin b => v r ^ j.val)
        (fun k : Fin (a + b - 1) => (Lagrange.basis Finset.univ v r).coeff k.val)
        i j k := by
  funext i j k
  have hij : i.val + j.val < a + b - 1 := (convolutionOutput i j).isLt
  simpa only [convolution_apply, Tensor.rankOne, pow_add] using
    monomial_coeff_eq_sum_interpolation hij v hv k.val

/-- The convolution (K := K) tensor `C(a,b)` has rank at most `a + b - 1` over `K`. -/
theorem convolution_rankAtMost [Infinite K] (a b : ℕ) :
    Tensor.RankAtMost (convolution (K := K) a b) (a + b - 1) := by
  let v : Fin (a + b - 1) → K := fun i => Infinite.natEmbedding K i.val
  have hv : Function.Injective v := by
    intro i j h
    exact Fin.ext ((Infinite.natEmbedding K).injective h)
  rw [convolution_eq_sum_rankOne v hv]
  simpa using Tensor.rankAtMost_sum_rankOne
    (fun r (i : Fin a) => v r ^ i.val)
    (fun r (j : Fin b) => v r ^ j.val)
    (fun r (k : Fin (a + b - 1)) => (Lagrange.basis Finset.univ v r).coeff k.val)

end MatrixMultiplication.AuxiliarySeparation

end OAI

end Module1


section Module2
namespace OAI
variable {K : Type*} [Field K]

/-!
# Exact rank of polynomial convolution

Each output coefficient of polynomial multiplication occurs in some product
of two input monomials. Choosing one such pair for each output gives an
identity minor in the output flattening. Together with evaluation and
interpolation, this proves the exact rank of `C(a,b)` for positive dimensions.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Choosing one product for every output monomial gives an identity minor
of the output flattening. -/
theorem convolution_identity_minor {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (x : Fin (a + b - 1) → Fin a) (y : Fin (a + b - 1) → Fin b),
      ∀ k l, convolution (K := K) a b (x k) (y k) l = if k = l then 1 else 0 := by
  choose x y hxy using fun k : Fin (a + b - 1) => convolution_output_supported (K := K) ha hb k
  have hsum (k : Fin (a + b - 1)) : (x k).val + (y k).val = k.val :=
    (convolution_eq_one_iff _ _ _).mp (hxy k)
  refine ⟨x, y, ?_⟩
  intro k l
  simp only [convolution_apply, hsum, Fin.val_inj]

/-- Every rank decomposition of convolution (K := K) has at least one term per output
coefficient. -/
theorem convolution_rank_lower {a b r : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hRank : Tensor.RankAtMost (convolution (K := K) a b) r) : a + b - 1 ≤ r := by
  obtain ⟨x, y, hxy⟩ := convolution_identity_minor (K := K) ha hb
  simpa using hRank.card_le_of_identity x y id hxy

/-- Polynomial multiplication has exact rank `a+b-1` when both inputs have
positive dimension. -/
theorem exactRank_convolution [Infinite K] {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    exactRank (convolution (K := K) a b) = a + b - 1 := by
  apply le_antisymm (exactRank_le (convolution_rankAtMost a b))
  exact convolution_rank_lower ha hb (exactRank_spec _)

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end Module2



end AllFieldsModule11
/- END all-fields module GenericConvolution -/

/- BEGIN all-fields module GenericNumerics -/
section AllFieldsModule12

set_option autoImplicit false

section CompatibilityAliases

universe u

/- Compatibility aliases: Lean 4.34.1 Init/Core.lean names, proved by their
   Lean 4.33.1 predecessors without changing the source statements. -/
private theorem GenericNumerics_ite_eq_left {c : Prop} {h : Decidable c} (hc : c)
    {α : Sort u} {t e : α} : ite c t e = t := if_pos hc
private theorem GenericNumerics_ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c)
    {α : Sort u} {t e : α} : ite c t e = e := if_neg hnc
private theorem GenericNumerics_dite_eq_left {c : Prop} {h : Decidable c} (hc : c)
    {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = t hc := dif_pos hc
private theorem GenericNumerics_dite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c)
    {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = e hnc := dif_neg hnc
/- From Mathlib 4.34.1 Order/Antisymmetrization.lean, unchanged proof. -/
private theorem GenericNumerics_toAntisymmetrization_eq {α : Type u} (r : α → α → Prop)
    [IsPreorder α r] (a b : α) :
    toAntisymmetrization r a = toAntisymmetrization r b ↔ AntisymmRel r a b :=
  Quotient.eq

end CompatibilityAliases



/- OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy -/
section NumericModule0

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

def entropyTerm (p : ℝ) : ℝ := -p * Real.log p

def finiteEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, entropyTerm (p a)

theorem finiteEntropy_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) : finiteEntropy (fun a => p (e a)) = finiteEntropy p :=
  e.sum_comp (fun b => entropyTerm (p b))

@[simp] theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

theorem finiteEntropy_chain {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : A → B → ℝ) (hq : ∀ a, ∑ b, q a b = 1) :
    finiteEntropy (fun ab : A × B => p ab.1 * q ab.1 ab.2) =
      finiteEntropy p + ∑ a, p a * finiteEntropy (q a) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, entropyTerm_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]

structure FiniteLaw (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B := by
  classical
  exact
    { mass := fun b => ∑ a, if f a = b then p.mass a else 0
      nonneg := fun b => Finset.sum_nonneg fun a _ => by
        split_ifs
        · exact p.nonneg a
        · exact le_rfl
      total := by
        rw [Finset.sum_comm]
        simpa using p.total }

@[simp] theorem map_mass [DecidableEq B] (p : FiniteLaw A) (f : A → B) (b : B) :
    (p.map f).mass b = ∑ a, if f a = b then p.mass a else 0 := by
  classical
  dsimp only [map]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp only [h, ite_true, ite_false]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

theorem map_entropy_of_injective (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) : finiteEntropy (p.map f).mass = finiteEntropy p.mass := by
  classical
  have hterm (b : B) : entropyTerm ((p.map f).mass b) =
      ∑ a, if f a = b then entropyTerm (p.mass a) else 0 := by
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [map_mass_apply p f hf]
      simp [hf.eq_iff]
    · simp [map_mass, not_exists.mp hb]
  unfold finiteEntropy
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

def joint (p : FiniteLaw A) (q : A → FiniteLaw B) : FiniteLaw (A × B) where
  mass ab := p.mass ab.1 * (q ab.1).mass ab.2
  nonneg ab := mul_nonneg (p.nonneg ab.1) ((q ab.1).nonneg ab.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, (q _).total, p.total]

theorem joint_entropy (p : FiniteLaw A) (q : A → FiniteLaw B) :
    finiteEntropy (p.joint q).mass =
      finiteEntropy p.mass + ∑ a, p.mass a * finiteEntropy (q a).mass :=
  finiteEntropy_chain p.mass (fun a => (q a).mass) (fun a => (q a).total)

theorem mass_le_map_mass (p : FiniteLaw A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  rw [map_mass]
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun a' => if f a' = f a then p.mass a' else 0)
    (fun a' _ => by
      change 0 ≤ if f a' = f a then p.mass a' else 0
      split_ifs
      · exact p.nonneg a'
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa using h

def conditional (p : FiniteLaw A) (f : A → B) (b : B) : FiniteLaw A := by
  classical
  exact if hzero : (p.map f).mass b = 0 then p else
    { mass := fun a => (if f a = b then p.mass a else 0) / (p.map f).mass b
      nonneg := fun a => div_nonneg
        (by split_ifs; exact p.nonneg a; exact le_rfl) ((p.map f).nonneg b)
      total := by
        rw [← Finset.sum_div, ← map_mass p f b, div_self hzero] }

theorem map_mass_mul_conditional [DecidableEq B]
    (p : FiniteLaw A) (f : A → B) (b : B) (a : A) :
    (p.map f).mass b * (p.conditional f b).mass a =
      if f a = b then p.mass a else 0 := by
  classical
  by_cases hzero : (p.map f).mass b = 0
  · have ha : f a = b → p.mass a = 0 := by
      intro hab
      have hle := p.mass_le_map_mass f a
      rw [hab, hzero] at hle
      exact le_antisymm hle (p.nonneg a)
    rw [hzero, zero_mul]
    by_cases hab : f a = b
    · rw [GenericNumerics_ite_eq_left hab, ha hab]
    · rw [GenericNumerics_ite_eq_right hab]
  · simp only [conditional, hzero, ↓reduceDIte]
    by_cases hab : f a = b
    · simpa only [hab, ite_true] using (mul_div_cancel₀ (p.mass a) hzero)
    · simp only [hab, ite_false, zero_div, mul_zero]

theorem entropy_eq_map_add_conditional (p : FiniteLaw A) (f : A → B) :
    finiteEntropy p.mass = finiteEntropy (p.map f).mass +
      ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass := by
  classical
  let graph : A → B × A := fun a => (f a, a)
  have hinj : Function.Injective graph := fun _ _ h => congrArg Prod.snd h
  have hmass : ((p.map f).joint (p.conditional f)).mass = (p.map graph).mass := by
    funext ba
    rcases ba with ⟨b, a⟩
    change (p.map f).mass b * (p.conditional f b).mass a = (p.map graph).mass (b, a)
    rw [map_mass_mul_conditional, map_mass, Finset.sum_eq_single a]
    · simp only [graph, Prod.mk.injEq, and_true]
    · intro x _ hxa
      simp only [graph, Prod.mk.injEq, hxa, and_false, ite_false]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  calc
    finiteEntropy p.mass = finiteEntropy (p.map graph).mass :=
      (p.map_entropy_of_injective graph hinj).symm
    _ = finiteEntropy ((p.map f).joint (p.conditional f)).mass := by rw [hmass]
    _ = _ := (p.map f).joint_entropy (p.conditional f)

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

theorem entropyTerm_eq_negMulLog (p : ℝ) : entropyTerm p = Real.negMulLog p := rfl

@[simp] theorem entropyTerm_one : entropyTerm 1 = 0 := by simp [entropyTerm]

theorem mul_entropyTerm_inv (x : ℝ) : x * entropyTerm x⁻¹ = Real.log x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [entropyTerm, Real.log_inv]
    calc
      _ = (x * x⁻¹) * Real.log x := by ring
      _ = Real.log x := by rw [mul_inv_cancel₀ hx, one_mul]

theorem finiteEntropy_uniform {A : Type*} [Fintype A] :
    finiteEntropy (fun _a : A => (Fintype.card A : ℝ)⁻¹) =
      Real.log (Fintype.card A) := by
  simp only [finiteEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_entropyTerm_inv (Fintype.card A)

theorem finiteEntropy_deterministic {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) : finiteEntropy (fun b => if b = a then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  change entropyTerm (if b = a then 1 else 0) = 0
  split_ifs <;> simp

@[fun_prop] theorem continuous_entropyTerm : Continuous entropyTerm :=
  Real.continuous_negMulLog

theorem entropyTerm_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ entropyTerm p :=
  Real.negMulLog_nonneg hp₀ hp₁

theorem concaveOn_entropyTerm : ConcaveOn ℝ (Set.Ici 0) entropyTerm :=
  Real.concaveOn_negMulLog

@[fun_prop] theorem continuous_finiteEntropy {A : Type*} [Fintype A] :
    Continuous (finiteEntropy : (A → ℝ) → ℝ) := by
  unfold finiteEntropy
  exact continuous_finset_sum _ fun value _ =>
    continuous_entropyTerm.comp (continuous_apply value)

theorem tendsto_entropyTerm {I : Type*} {l : Filter I} {p : I → ℝ} {q : ℝ}
    (h : Tendsto p l (𝓝 q)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 (entropyTerm q)) :=
  continuous_entropyTerm.continuousAt.tendsto.comp h

theorem tendsto_entropyTerm_zero {I : Type*} {l : Filter I} {p : I → ℝ}
    (h : Tendsto p l (𝓝 0)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 0) := by
  simpa only [entropyTerm_zero] using tendsto_entropyTerm h

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

theorem finiteEntropy_nonneg {A : Type*} [Fintype A] (p : A → ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hp₁ : ∀ a, p a ≤ 1) : 0 ≤ finiteEntropy p := by
  exact Finset.sum_nonneg fun a _ => entropyTerm_nonneg (hp₀ a) (hp₁ a)

theorem finiteEntropy_mix_le {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * finiteEntropy p + b * finiteEntropy q ≤
      finiteEntropy (fun i => a * p i + b * q i) := by
  calc
    a * finiteEntropy p + b * finiteEntropy q =
        ∑ i, (a * entropyTerm (p i) + b * entropyTerm (q i)) := by
      simp only [finiteEntropy, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ finiteEntropy (fun i => a * p i + b * q i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact concaveOn_entropyTerm.2 (hp i) (hq i) ha hb hab

theorem finiteEntropy_le_log_card {A : Type*} [Fintype A] (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (htotal : ∑ a, p a = 1) :
    finiteEntropy p ≤ Real.log (Fintype.card A) := by
  classical
  have hcard : 0 < Fintype.card A := by
    by_contra h
    have : IsEmpty A := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    simp at htotal
  have hn : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr hcard
  have hw : ∑ _a : A, (Fintype.card A : ℝ)⁻¹ = 1 := by
    simp [Finset.sum_const, nsmul_eq_mul, hn.ne']
  have hJ := concaveOn_entropyTerm.le_map_sum
    (t := (Finset.univ : Finset A))
    (w := fun _a : A => (Fintype.card A : ℝ)⁻¹) (p := p)
    (fun _a _ha => (inv_pos.mpr hn).le) hw (fun a _ha => hp a)
  have hJ' : (Fintype.card A : ℝ)⁻¹ * finiteEntropy p ≤
      entropyTerm (Fintype.card A : ℝ)⁻¹ := by
    simpa only [smul_eq_mul, ← Finset.mul_sum, htotal, mul_one, finiteEntropy] using hJ
  calc
    finiteEntropy p = (Fintype.card A : ℝ) *
        ((Fintype.card A : ℝ)⁻¹ * finiteEntropy p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    _ ≤ (Fintype.card A : ℝ) * entropyTerm (Fintype.card A : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hJ' hn.le
    _ = Real.log (Fintype.card A) := mul_entropyTerm_inv (Fintype.card A)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteLaw A where
  mass _a := (Fintype.card A : ℝ)⁻¹
  nonneg _a := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card A : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card A)).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn]

@[simp] theorem uniform_mass [Nonempty A] (a : A) :
    (uniform A).mass a = (Fintype.card A : ℝ)⁻¹ := rfl

@[simp] theorem uniform_entropy [Nonempty A] :
    finiteEntropy (uniform A).mass = Real.log (Fintype.card A) :=
  finiteEntropy_uniform

def pure (a : A) : FiniteLaw A := by
  classical
  exact
    { mass := fun b => if b = a then 1 else 0
      nonneg := fun b => by split_ifs <;> norm_num
      total := by simp }

@[simp] theorem pure_entropy (a : A) : finiteEntropy (pure a).mass = 0 := by
  classical
  exact finiteEntropy_deterministic a

theorem mass_le_one (p : FiniteLaw A) (a : A) : p.mass a ≤ 1 := by
  calc
    p.mass a ≤ ∑ b, p.mass b :=
      Finset.single_le_sum (fun b _hb => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := p.total

theorem entropy_nonneg (p : FiniteLaw A) : 0 ≤ finiteEntropy p.mass :=
  finiteEntropy_nonneg p.mass p.nonneg p.mass_le_one

theorem entropy_le_log_card (p : FiniteLaw A) :
    finiteEntropy p.mass ≤ Real.log (Fintype.card A) :=
  finiteEntropy_le_log_card p.mass p.nonneg p.total

theorem map_entropy_le {B : Type*} [Fintype B] (p : FiniteLaw A) (f : A → B) :
    finiteEntropy (p.map f).mass ≤ finiteEntropy p.mass := by
  calc
    finiteEntropy (p.map f).mass ≤ finiteEntropy (p.map f).mass +
        ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun b _ =>
        mul_nonneg ((p.map f).nonneg b) ((p.conditional f b).entropy_nonneg))
    _ = finiteEntropy p.mass := (p.entropy_eq_map_add_conditional f).symm

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

/-- The common binary probability law used for every permuted character. -/
def binaryLaw (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) : FiniteLaw (Fin 2) where
  mass i := if i = 0 then q else 1 - q
  nonneg i := by
    fin_cases i
    · simpa using hq₀
    · simpa using sub_nonneg.mpr hq₁
  total := by simp [Fin.sum_univ_two]

@[simp] theorem binaryLaw_zero (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (binaryLaw q hq₀ hq₁).mass 0 = q := by simp [binaryLaw]

@[simp] theorem binaryLaw_one (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (binaryLaw q hq₀ hq₁).mass 1 = 1 - q := by simp [binaryLaw]

/-- The finite-law entropy agrees exactly with the binary entropy convention. -/
theorem binaryLaw_entropy (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    finiteEntropy (binaryLaw q hq₀ hq₁).mass = Real.binEntropy q := by
  simp [finiteEntropy, Fin.sum_univ_two, entropyTerm, Real.binEntropy, Real.log_inv]
  ring

theorem binaryLaw_product (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (f : Fin 2 → ℝ) :
    (∏ i, f i ^ (binaryLaw q hq₀ hq₁).mass i) = f 0 ^ q * f 1 ^ (1 - q) := by
  simp [Fin.prod_univ_two]

/-- The three-sector entropy factor is `3 ^ p`. -/
theorem uniformThree_entropy_factor (p : ℝ) :
    Real.exp (p * finiteEntropy (FiniteLaw.uniform (Fin 3)).mass) = (3 : ℝ) ^ p := by
  rw [FiniteLaw.uniform_entropy]
  norm_num only [Fintype.card_fin]
  rw [Real.rpow_def_of_pos (by norm_num)]
  congr 1
  ring

theorem uniformThree_product (f : Fin 3 → ℝ) :
    (∏ i, f i ^ (FiniteLaw.uniform (Fin 3)).mass i) =
      f 0 ^ (1 / 3 : ℝ) * f 1 ^ (1 / 3 : ℝ) * f 2 ^ (1 / 3 : ℝ) := by
  simp [Fin.prod_univ_three, FiniteLaw.uniform_mass, mul_assoc]

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

/-- The logarithmic form of the entropy identity at the normalized weights. -/
theorem binary_entropy_log_partition {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.binEntropy (A / (A + B)) +
        Real.log A * (A / (A + B)) +
        Real.log B * (1 - A / (A + B)) = Real.log (A + B) := by
  have hsum : A + B ≠ 0 := ne_of_gt (add_pos hA hB)
  have hcomplement : 1 - A / (A + B) = B / (A + B) := by
    field_simp
    ring
  rw [Real.binEntropy, hcomplement, Real.log_inv, Real.log_inv,
    Real.log_div hA.ne' hsum, Real.log_div hB.ne' hsum]
  field_simp
  ring

/-- Entropy compensates the weighted geometric mean at the normalized weights. -/
theorem binary_entropy_variational_identity {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.exp (Real.binEntropy (A / (A + B))) *
        A ^ (A / (A + B)) * B ^ (1 - A / (A + B)) = A + B := by
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB,
    ← Real.exp_add, ← Real.exp_add, binary_entropy_log_partition hA hB,
    Real.exp_log (add_pos hA hB)]

/-- The identity with an explicitly named optimizing proportion. -/
theorem binary_entropy_variational_identity_of_ratio {A B q : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hq : q = A / (A + B)) :
    Real.exp (-q * Real.log q - (1 - q) * Real.log (1 - q)) *
        A ^ q * B ^ (1 - q) = A + B := by
  subst q
  have hentropy :
      -(A / (A + B)) * Real.log (A / (A + B)) -
          (1 - A / (A + B)) * Real.log (1 - A / (A + B)) =
        Real.binEntropy (A / (A + B)) := by
    simp only [Real.binEntropy, Real.log_inv]
    ring
  rw [hentropy]
  exact binary_entropy_variational_identity hA hB

/-- The logarithmic entropy identity for positive weights on a finite set. -/
theorem finite_entropy_log_partition {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hs : s.Nonempty) (hA : ∀ i ∈ s, 0 < A i) :
    -(∑ i ∈ s, (A i / (∑ j ∈ s, A j)) * Real.log (A i / (∑ j ∈ s, A j))) +
        (∑ i ∈ s, Real.log (A i) * (A i / (∑ j ∈ s, A j))) =
      Real.log (∑ j ∈ s, A j) := by
  have hsum : 0 < ∑ j ∈ s, A j := Finset.sum_pos hA hs
  calc
    _ = ∑ i ∈ s, (A i / (∑ j ∈ s, A j)) * Real.log (∑ j ∈ s, A j) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.log_div (hA i hi).ne' hsum.ne']
      ring
    _ = (∑ i ∈ s, A i / (∑ j ∈ s, A j)) * Real.log (∑ j ∈ s, A j) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [← Finset.sum_div, div_self hsum.ne', one_mul]

/-- Normalizing any positive finite family attains its sum in the entropy formula. -/
theorem finite_entropy_variational_identity {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hs : s.Nonempty) (hA : ∀ i ∈ s, 0 < A i) :
    Real.exp (-(∑ i ∈ s, (A i / (∑ j ∈ s, A j)) *
        Real.log (A i / (∑ j ∈ s, A j)))) *
        (∏ i ∈ s, (A i) ^ (A i / (∑ j ∈ s, A j))) = ∑ j ∈ s, A j := by
  have hsum : 0 < ∑ j ∈ s, A j := Finset.sum_pos hA hs
  have hprod : (∏ i ∈ s, (A i) ^ (A i / (∑ j ∈ s, A j))) =
      Real.exp (∑ i ∈ s, Real.log (A i) * (A i / (∑ j ∈ s, A j))) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.rpow_def_of_pos (hA i hi) _
  rw [hprod, ← Real.exp_add, finite_entropy_log_partition s A hs hA,
    Real.exp_log hsum]

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

/-- Multiplying the entropy bounds and taking the positive normalization root
gives the midpoint-concavity inequality. -/
theorem finite_product_concavity {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i q, 0 ≤ q → q ≤ 1 →
      Real.exp (p i * Real.binEntropy q) * (B i) ^ q * (C i) ^ (1 - q) ≤
        (2 : ℝ) ^ (p i) * A i) :
    (∏ i, B i) ^ (1 / s) + (∏ i, C i) ^ (1 / s) ≤
      2 * (∏ i, A i) ^ (1 / s) := by
  have hprodA : 0 < ∏ i, A i := Finset.prod_pos (fun i _ => hA i)
  have hprodB : 0 < ∏ i, B i := Finset.prod_pos (fun i _ => hB i)
  have hprodC : 0 < ∏ i, C i := Finset.prod_pos (fun i _ => hC i)
  let a : ℝ := (∏ i, A i) ^ (1 / s)
  let b : ℝ := (∏ i, B i) ^ (1 / s)
  let c : ℝ := (∏ i, C i) ^ (1 / s)
  have ha : 0 < a := Real.rpow_pos_of_pos hprodA _
  have hb : 0 < b := Real.rpow_pos_of_pos hprodB _
  have hc : 0 < c := Real.rpow_pos_of_pos hprodC _
  let q : ℝ := b / (b + c)
  have hq0 : 0 ≤ q := le_of_lt (div_pos hb (add_pos hb hc))
  have hq1 : q ≤ 1 := (div_le_one (add_pos hb hc)).mpr (le_of_lt (lt_add_of_pos_right b hc))
  have hlog : ∀ i, p i * Real.binEntropy q + q * Real.log (B i) +
      (1 - q) * Real.log (C i) ≤ p i * Real.log 2 + Real.log (A i) := by
    intro i
    have hleft1 : 0 < Real.exp (p i * Real.binEntropy q) * (B i) ^ q :=
      mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (hB i) _)
    have h := Real.log_le_log
      (mul_pos hleft1 (Real.rpow_pos_of_pos (hC i) _)) (hbound i q hq0 hq1)
    rw [Real.log_mul hleft1.ne' (Real.rpow_pos_of_pos (hC i) _).ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos (hB i) _).ne',
      Real.log_exp, Real.log_rpow (hB i), Real.log_rpow (hC i),
      Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
        (hA i).ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h
    simpa only [mul_comm (Real.log 2) (p i)] using h
  have hlogs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlog i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hsum, ← Real.log_prod (fun i _ => (hA i).ne'),
    ← Real.log_prod (fun i _ => (hB i).ne'),
    ← Real.log_prod (fun i _ => (hC i).ne')] at hlogs
  have hnormalized : Real.binEntropy q + Real.log b * q + Real.log c * (1 - q) ≤
      Real.log 2 + Real.log a := by
    dsimp only [a, b, c]
    rw [Real.log_rpow hprodA, Real.log_rpow hprodB, Real.log_rpow hprodC]
    convert div_le_div_of_nonneg_right hlogs hs.le using 1 <;> (first | rfl | field_simp [hs.ne'])
  change Real.binEntropy (b / (b + c)) + Real.log b * (b / (b + c)) +
      Real.log c * (1 - b / (b + c)) ≤ Real.log 2 + Real.log a at hnormalized
  rw [binary_entropy_log_partition hb hc,
    ← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne'] at hnormalized
  exact (Real.log_le_log_iff (add_pos hb hc) (mul_pos (by norm_num) ha)).mp hnormalized

/-- Multiplying the cyclic bounds and taking the positive normalization root
gives the factor of three in the tripling inequality. -/
theorem finite_product_tripling {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (_hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i, (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ) ≤ A i)
    (hprod_eq : ∏ i, C i = ∏ i, B i) :
    3 * (∏ i, B i) ^ (1 / s) ≤ (∏ i, A i) ^ (1 / s) := by
  have hBprod : 0 < ∏ i, B i := Finset.prod_pos fun i _ => hB i
  have hprod : (3 : ℝ) ^ s * (∏ i, B i) ≤ ∏ i, A i := by
    have hmul := Finset.prod_le_prod (s := Finset.univ)
      (f := fun i => (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ))
      (g := A)
      (fun i _ => mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (hB i).le _))
        (Real.rpow_nonneg (hC i).le _))
      (fun i _ => hbound i)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 3) p Finset.univ, hsum,
      Real.finset_prod_rpow Finset.univ B (fun i _ => (hB i).le),
      Real.finset_prod_rpow Finset.univ C (fun i _ => (hC i).le), hprod_eq,
      mul_assoc, ← Real.rpow_add hBprod] at hmul
    norm_num at hmul
    exact (Real.rpow_one (∏ i, B i)) ▸ hmul
  have hmean := Real.rpow_le_rpow (by positivity) hprod (by positivity : (0 : ℝ) ≤ 1 / s)
  rw [Real.mul_rpow (by positivity) hBprod.le,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_one_div_cancel hs.ne',
    Real.rpow_one] at hmean
  exact hmean

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

/-- The usual second-difference inequality makes the increments decreasing. -/
theorem antitone_increments_of_discrete_concavity {u : ℕ → ℝ}
    (hu : ∀ n, u (n + 2) + u n ≤ 2 * u (n + 1)) :
    Antitone (fun n => u (n + 1) - u n) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hu n
  simp only [Nat.add_assoc] at *
  linarith

/-- A tangent-line upper bound for a sequence with decreasing increments. -/
theorem concave_sequence_le_affine {u : ℕ → ℝ}
    (hd : Antitone (fun n => u (n + 1) - u n)) (n k : ℕ) :
    u (n + k) ≤ u n + (k : ℝ) * (u (n + 1) - u n) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hd (show n ≤ n + k by omega)
      simp only at hstep
      rw [Nat.cast_add, Nat.cast_one]
      have hindex : n + (k + 1) = n + k + 1 := by omega
      rw [hindex]
      nlinarith

/-- Every increment of a nonnegative discretely concave sequence is nonnegative. -/
theorem increment_nonneg_of_antitone {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n))
    (n : ℕ) : 0 ≤ u (n + 1) - u n := by
  by_contra hn
  have hneg : u (n + 1) - u n < 0 := lt_of_not_ge hn
  obtain ⟨k, hk⟩ := exists_lt_nsmul (neg_pos.mpr hneg) (u n)
  have hk' : u n < (k : ℝ) * -(u (n + 1) - u n) := by
    simpa only [nsmul_eq_mul] using hk
  have hbound := concave_sequence_le_affine hd n k
  have hnonneg := hu (n + k)
  nlinarith

/-- A nonnegative discretely concave sequence is increasing. -/
theorem monotone_of_nonneg_of_antitone_increments {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n)) :
    Monotone u := by
  apply monotone_nat_of_le_succ
  intro n
  have := increment_nonneg_of_antitone hu hd n
  linarith

/-- Telescoping and Cesàro convergence identify the linear growth rate. -/
theorem tendsto_div_nat_of_tendsto_increments {u : ℕ → ℝ} {g : ℝ}
    (hd : Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 g)) :
    Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 g) := by
  have hmean := hd.cesaro
  simp only [Finset.sum_range_sub] at hmean
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (u 0)
  have hsum := hmean.add hconst
  simpa only [add_zero, div_eq_mul_inv, mul_sub, sub_add_cancel, mul_comm] using hsum

/-- The limiting increment of a nonnegative discretely concave sequence is
nonnegative, and it is also its linear growth rate. -/
theorem exists_nonneg_limit_of_antitone_increments {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n)) :
    ∃ g : ℝ, 0 ≤ g ∧
      Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 g) ∧
      Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 g) := by
  have hnonneg := increment_nonneg_of_antitone hu hd
  have hbdd : BddBelow (Set.range (fun n => u (n + 1) - u n)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hnonneg n
  have hlim := tendsto_atTop_ciInf hd hbdd
  refine ⟨⨅ n, u (n + 1) - u n, ?_, hlim,
    tendsto_div_nat_of_tendsto_increments hlim⟩
  exact ge_of_tendsto hlim (Eventually.of_forall hnonneg)

/-- Positive-index version, suitable for the rows in Section 6. The value at
index zero is irrelevant. -/
theorem exists_concave_slope_limit {P : ℕ → ℝ}
    (hP : ∀ n, 0 < P (n + 1))
    (hd : Antitone (fun n => P (n + 2) - P (n + 1))) :
    ∃ g : ℝ, 0 ≤ g ∧
      (∀ n, g ≤ P (n + 2) - P (n + 1)) ∧
      Tendsto (fun n => P (n + 2) - P (n + 1)) atTop (𝓝 g) ∧
      Tendsto (fun n => P n / (n : ℝ)) atTop (𝓝 g) := by
  have hd' : Antitone (fun n => P ((n + 1) + 1) - P (n + 1)) := by
    simpa only [Nat.add_assoc] using hd
  obtain ⟨g, hg, hlim, hratio⟩ := exists_nonneg_limit_of_antitone_increments
    (u := fun n => P (n + 1)) (fun n => (hP n).le) hd'
  have hmul := hratio.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hshift : Tendsto (fun n => P (n + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 g) := by
    rw [mul_one] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  refine ⟨g, hg, ?_, ?_, (tendsto_add_atTop_iff_nat 1).mp hshift⟩
  · intro n
    exact hd.le_of_tendsto (by simpa only [Nat.add_assoc] using hlim) n
  · simpa only [Nat.add_assoc] using hlim

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

/-- The indices obtained by repeatedly applying the affine tripling map. -/
def shiftedTriplingIndex (c h : ℕ) : ℕ → ℕ
  | 0 => h
  | j + 1 => 3 * shiftedTriplingIndex c h j + c

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

/-- The row estimate in the positive-index notation of the paper. -/
theorem profile_row_le_slope {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (htrip : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hlim : ∀ a : ℕ, 1 ≤ a →
      Tendsto (fun h : ℕ => P a h / (h : ℝ)) atTop (𝓝 (g a)))
    (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    P a h ≤ ((h : ℝ) + ((a : ℝ) - 1) / 2) * g a := by
  have ht : ∀ n : ℕ, 1 ≤ n → 3 * P a n ≤ P a (3 * n + (a - 1)) := by
    intro n hn
    have hi : 3 * n + (a - 1) = 3 * n + a - 1 := by omega
    rw [hi]
    exact htrip a ha n hn
  have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha, Nat.cast_one]
  simpa only [hcast] using profile_le_affine_slope hh ht (hlim a ha)

/-- The diagonal is bounded above by the limiting row slope with the precise
coefficient `(3a-1)/2`. -/
theorem profile_diagonal_le_slope {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (htrip : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hlim : ∀ a : ℕ, 1 ≤ a →
      Tendsto (fun h : ℕ => P a h / (h : ℝ)) atTop (𝓝 (g a)))
    (a : ℕ) (ha : 1 ≤ a) :
    P a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
  have hc : (a : ℝ) + ((a : ℝ) - 1) / 2 = (3 * (a : ℝ) - 1) / 2 := by ring
  simpa only [hc] using profile_row_le_slope htrip hlim a a ha ha

/-- Symmetry identifies a diagonal step with one increment in each adjacent
row. Only positive-index symmetry and slope bounds are used. -/
theorem diagonal_increment_of_slope_lower {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (hsymm : ∀ a : ℕ, 1 ≤ a → ∀ b : ℕ, 1 ≤ b → P a b = P b a)
    (hinc : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      g a ≤ P a (h + 1) - P a h)
    (n : ℕ) (hn : 1 ≤ n) :
    P n n + g n + g (n + 1) ≤ P (n + 1) (n + 1) := by
  have hfirst := hinc n hn n hn
  have hsecond := hinc (n + 1) (by omega) n hn
  have hsym := hsymm n hn (n + 1) (by omega)
  linarith

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

/-- A uniform bound on all positive natural inputs forces the exponent on
the left to be no larger than the exponent on the right. -/
theorem rpow_exponent_le_of_nat_bound {a b C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b) :
    a ≤ b := by
  have hC : 0 < C := by
    have h := hbound 1 (by omega)
    norm_num at h
    linarith
  by_contra hab
  have hab' : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (a - b) * Real.log 2 := mul_pos hab' hlog2
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.log C / ((a - b) * Real.log 2))
  have hk' : Real.log C < (k : ℝ) * ((a - b) * Real.log 2) :=
    (div_lt_iff₀ hp).mp hk
  have hn : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
  have h := Real.log_le_log (Real.rpow_pos_of_pos hn a)
    (hbound (2 ^ k) (Nat.one_le_iff_ne_zero.mpr (by positivity)))
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hn b).ne',
    Real.log_rpow hn a, Real.log_rpow hn b] at h
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  nlinarith

/-- The diagonal lower bound and the dimension upper bound force the scalar
exponent to be at most `3/4`. -/
theorem diagonal_exponent_le_three_quarters {D : ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ D n)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 4 ≤ D n ^ 3)
    (hupper : ∀ n : ℕ, 1 ≤ n → D n ≤ (2 * (n : ℝ) - 1) ^ (1 / t)) :
    t ≤ 3 / 4 := by
  have hexp : 0 ≤ 1 / t := le_of_lt (one_div_pos.mpr ht)
  have hpower : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (4 : ℝ) ≤
        (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbase : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
    have hu : D n ≤ (2 * (n : ℝ)) ^ (1 / t) :=
      (hupper n hn).trans (Real.rpow_le_rpow hbase (by linarith) hexp)
    calc
      (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by norm_num
      _ ≤ D n ^ 3 := hlower n hn
      _ ≤ ((2 * (n : ℝ)) ^ (1 / t)) ^ 3 :=
        pow_le_pow_left₀ (hnonneg n hn) hu 3
      _ = (2 * (n : ℝ)) ^ ((1 / t) * 3) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_mul_natCast (show 0 ≤ 2 * (n : ℝ) by positivity) (1 / t) 3).symm
      _ = (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) :=
        Real.mul_rpow (by norm_num) (by positivity)
  have hcompare : (4 : ℝ) ≤ (1 / t) * 3 :=
    rpow_exponent_le_of_nat_bound hpower
  have hmul := mul_le_mul_of_nonneg_right hcompare (le_of_lt ht)
  have hcancel : ((1 / t) * 3) * t = (3 : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  linarith

/-- The scalar comparison in the normalization used for the matrix
multiplication exponent. -/
theorem three_mul_diagonal_exponent_le_nine_quarters {D : ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ D n)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 4 ≤ D n ^ 3)
    (hupper : ∀ n : ℕ, 1 ≤ n → D n ≤ (2 * (n : ℝ) - 1) ^ (1 / t)) :
    3 * t ≤ 9 / 4 := by
  have h := diagonal_exponent_le_three_quarters ht hnonneg hlower hupper
  linarith

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

/-- The scalar profile hypotheses used in Section 6. Only positive indices
carry mathematical content; the values on either coordinate axis are unused. -/
structure ScalarProfile (t : ℝ) where
  value : ℕ → ℕ → ℝ
  positive : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 0 < value a b
  symmetric : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → value a b = value b a
  boundary : ∀ b : ℕ, 1 ≤ b → value 1 b = (b : ℝ)
  concave : ∀ a h : ℕ, 1 ≤ a → 2 ≤ h →
    value a (h - 1) + value a (h + 1) ≤ 2 * value a h
  tripling : ∀ a h : ℕ, 1 ≤ a → 1 ≤ h →
    3 * value a h ≤ value a (3 * h + a - 1)
  rank_bound : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    value a b ≤ ((a : ℝ) + (b : ℝ) - 1) ^ (1 / t)

namespace ScalarProfile

/-- Each row has a nonnegative limiting slope that bounds every increment
from below and equals the limit of the row divided by its index. -/
theorem exists_row_slope {t : ℝ} (P : ScalarProfile t) (a : ℕ) (ha : 1 ≤ a) :
    ∃ g : ℝ, 0 ≤ g ∧
      (∀ h : ℕ, 1 ≤ h → g ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 g) := by
  have hd : Antitone (fun n : ℕ => P.value a (n + 2) - P.value a (n + 1)) := by
    apply antitone_nat_of_succ_le
    intro n
    have hc := P.concave a (n + 2) ha (by omega)
    have hpred : n + 2 - 1 = n + 1 := by omega
    rw [hpred] at hc
    simp only [Nat.add_assoc] at *
    linarith
  obtain ⟨g, hg, hinc, _, hratio⟩ := exists_concave_slope_limit
    (P := P.value a) (fun n => P.positive a (n + 1) ha (by omega)) hd
  refine ⟨g, hg, ?_, hratio⟩
  intro h hh
  cases h with
  | zero => omega
  | succ n => simpa only [Nat.add_assoc] using hinc n

/-- Choose the row slopes together, retaining their bounds and limits on all
positive rows. -/
theorem exists_row_slopes {t : ℝ} (P : ScalarProfile t) :
    ∃ g : ℕ → ℝ, ∀ a : ℕ, 1 ≤ a → 0 ≤ g a ∧
      (∀ h : ℕ, 1 ≤ h → g a ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 (g a)) := by
  classical
  have hex (a : ℕ) : ∃ g : ℝ, 1 ≤ a → 0 ≤ g ∧
      (∀ h : ℕ, 1 ≤ h → g ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 g) := by
    by_cases ha : 1 ≤ a
    · obtain ⟨g, hg⟩ := P.exists_row_slope a ha
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun ha' => False.elim (ha ha')⟩
  choose g hg using hex
  exact ⟨g, hg⟩

/-- The exact polynomial lower bound on the diagonal, obtained from row
concavity, shifted tripling, and the simultaneous scalar induction. -/
theorem diagonal_fourth_power_lower {t : ℝ} (P : ScalarProfile t)
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ 4 ≤ P.value n n ^ 3 := by
  obtain ⟨g, hg⟩ := P.exists_row_slopes
  have hupper : ∀ a : ℕ, 1 ≤ a →
      P.value a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
    apply profile_diagonal_le_slope
    · intro a ha h hh
      exact P.tripling a h ha hh
    · intro a ha
      exact (hg a ha).2.2
  have hincrement : ∀ a : ℕ, 1 ≤ a →
      P.value a a + g a + g (a + 1) ≤ P.value (a + 1) (a + 1) := by
    apply diagonal_increment_of_slope_lower
    · intro a ha b hb
      exact P.symmetric a b ha hb
    · intro a ha h hh
      exact (hg a ha).2.1 h hh
  have hDbase : 1 ≤ P.value 1 1 := by
    rw [P.boundary 1 (by omega)]
    norm_num
  have hgbase : 1 ≤ g 1 := by
    have hu := hupper 1 (by omega)
    rw [P.boundary 1 (by omega)] at hu
    norm_num at hu
    exact (one_mul (g 1)) ▸ hu
  exact MatrixMultiplication.AuxiliarySeparation.diagonal_fourth_power_lower_of_one_le
    (fun a => P.value a a) g hgbase hDbase hupper hincrement n hn

/-- Lemma 6.1: a positive symmetric profile satisfying the stated concavity,
tripling, boundary, and rank bounds has exponent at most `3/4`. -/
theorem exponent_le_three_quarters {t : ℝ} (P : ScalarProfile t) (ht : 0 < t) :
    t ≤ 3 / 4 := by
  apply diagonal_exponent_le_three_quarters (D := fun a => P.value a a) ht
  · intro n hn
    exact (P.positive n n hn hn).le
  · exact P.diagonal_fourth_power_lower
  · intro n hn
    have hu := P.rank_bound n n hn hn
    simpa only [two_mul] using hu

end ScalarProfile

/-- The scalar profile implication, with every profile assumption displayed
explicitly rather than bundled in `ScalarProfile`. -/
theorem profile_exponent_le_three_quarters {P : ℕ → ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hpositive : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 0 < P a b)
    (hsymmetric : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → P a b = P b a)
    (hboundary : ∀ b : ℕ, 1 ≤ b → P 1 b = (b : ℝ))
    (hconcave : ∀ a h : ℕ, 1 ≤ a → 2 ≤ h →
      P a (h - 1) + P a (h + 1) ≤ 2 * P a h)
    (htripling : ∀ a h : ℕ, 1 ≤ a → 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hrank : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      P a b ≤ ((a : ℝ) + (b : ℝ) - 1) ^ (1 / t)) :
    t ≤ 3 / 4 := by
  exact ScalarProfile.exponent_le_three_quarters
    ⟨P, hpositive, hsymmetric, hboundary, hconcave, htripling, hrank⟩ ht

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

/-- A permutation of the three tensor legs. -/
abbrev LegPermutation := Equiv.Perm (Fin 3)

namespace LegPermutation

/-- There are six orders of the three legs. -/
theorem card : Fintype.card LegPermutation = 6 := by
  norm_num [Fintype.card_perm, Nat.factorial]

/-- Right composition just reindexes a product over all six permutations. -/
theorem prod_mul_right {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π, f (π * σ)) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.mulRight σ) f

/-- Left composition also just reindexes the six factors. -/
theorem prod_mul_left {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π, f (σ * π)) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.mulLeft σ) f

/-- The same reindexing statement in explicit equivalence-composition notation. -/
theorem prod_trans_right {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π : LegPermutation, f (π.trans σ)) = ∏ π, f π := by
  exact prod_mul_left f σ

/-- A permutation-independent sum may likewise be reindexed on the right. -/
theorem sum_mul_right {A : Type*} [AddCommMonoid A]
    (f : LegPermutation → A) (σ : LegPermutation) :
    (∑ π, f (π * σ)) = ∑ π, f π := by
  exact Equiv.sum_comp (Equiv.mulRight σ) f

/-- Each original leg occurs twice in each fixed position. -/
theorem card_apply_fiber (i j : Fin 3) :
    Fintype.card {π : LegPermutation // π i = j} = 2 := by
  let _ : Fintype LegPermutation := fintypePerm
  fin_cases i <;> fin_cases j <;> decide

/-- The product of values attached to one slot contains each leg twice. -/
theorem prod_apply {M : Type*} [CommMonoid M] (f : Fin 3 → M) (i : Fin 3) :
    (∏ π : LegPermutation, f (π i)) = (∏ j, f j) ^ 2 := by
  rw [← Fintype.prod_fiberwise' (fun π : LegPermutation => π i) f]
  simp only [Finset.prod_const, Finset.card_univ, card_apply_fiber, Finset.prod_pow]

/-- The exponent attached to one slot contains each leg exponent twice. -/
theorem sum_apply {A : Type*} [AddCommMonoid A] (p : Fin 3 → A) (i : Fin 3) :
    (∑ π : LegPermutation, p (π i)) = 2 • ∑ j, p j := by
  rw [← Fintype.sum_fiberwise' (fun π : LegPermutation => π i) p]
  simp only [Finset.sum_const, Finset.card_univ, card_apply_fiber, Finset.sum_nsmul]

/-- Inverting the permutation preserves the symmetrized product. -/
theorem prod_symm {M : Type*} [CommMonoid M] (f : LegPermutation → M) :
    (∏ π : LegPermutation, f π.symm) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.inv LegPermutation) f

/-- Inverting the permutation preserves a sum over all six orders. -/
theorem sum_symm {A : Type*} [AddCommMonoid A] (f : LegPermutation → A) :
    (∑ π : LegPermutation, f π.symm) = ∑ π, f π := by
  exact Equiv.sum_comp (Equiv.inv LegPermutation) f

/-- The twice-per-leg count is independent of the permutation convention. -/
theorem sum_symm_apply {A : Type*} [AddCommMonoid A]
    (p : Fin 3 → A) (i : Fin 3) :
    (∑ π : LegPermutation, p (π.symm i)) = 2 • ∑ j, p j := by
  rw [sum_symm (fun π => p (π i)), sum_apply]

/-- The sum of the six singleton-leg exponents is six times their mean. -/
theorem sum_exponents (p : Fin 3 → ℝ) (i : Fin 3) (t : ℝ)
    (h : (∑ j, p j) = 3 * t) :
    (∑ π : LegPermutation, p (π i)) = 6 * t := by
  rw [sum_apply, h]
  simp only [nsmul_eq_mul]
  ring

/-- The product of the valuations of all six transforms of an object. -/
def orbitProduct {X M : Type*} [CommMonoid M]
    (transform : LegPermutation → X → X) (value : X → M) (x : X) : M :=
  ∏ π : LegPermutation, value (transform π x)

/-- A further leg transformation preserves the product whenever transforms compose. -/
theorem orbitProduct_transform {X M : Type*} [CommMonoid M]
    (transform : LegPermutation → X → X) (value : X → M)
    (compose : ∀ π σ x, transform π (transform σ x) = transform (π * σ) x)
    (σ : LegPermutation) (x : X) :
    orbitProduct transform value (transform σ x) = orbitProduct transform value x := by
  simp only [orbitProduct, compose]
  exact prod_mul_right (fun π => value (transform π x)) σ

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

noncomputable def factorialLogRemainder (n : ℕ) : ℝ :=
  Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n)

theorem factorialLogRemainder_eq (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n) := rfl

@[simp] theorem factorialLogRemainder_zero : factorialLogRemainder 0 = 0 := by
  simp [factorialLogRemainder]

theorem factorialLogRemainder_stirling (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * n) := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Stirling.log_stirlingSeq_formula (n + 1)
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
    unfold factorialLogRemainder
    linarith

theorem tendsto_factorialLogRemainder_div :
    Tendsto (fun n : ℕ => factorialLogRemainder n / (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hstirling :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
        atTop (𝓝 0) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hconstant : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using hstirling.add ((hconstant.add hlog).const_mul (1 / 2 : ℝ))
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  rw [factorialLogRemainder_stirling,
    Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem tendsto_factorialLogRemainder_mul_div (c : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * c) / (t : ℝ))
      atTop (𝓝 0) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hmul : Tendsto (fun t : ℕ => t * c) atTop atTop :=
    tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hc)
  have hscaled : Tendsto
      (fun t : ℕ => factorialLogRemainder (t * c) / (t * c : ℕ) * (c : ℝ))
      atTop (𝓝 0) := by
    simpa using (tendsto_factorialLogRemainder_div.comp hmul).mul_const (c : ℝ)
  apply hscaled.congr
  intro t
  by_cases ht : t = 0
  · simp [ht]
  rw [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr ht]

theorem factorialLogRemainder_succ (n : ℕ) :
    factorialLogRemainder (n + 1) = factorialLogRemainder n + 1 -
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  unfold factorialLogRemainder
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

private theorem nat_mul_log_increment_le_one (n : ℕ) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have heq : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp [hpos.ne']
    ring
  rwa [heq] at hmul

private theorem one_le_succ_mul_log_increment (n : ℕ) (hn : 0 < n) :
    1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hsucc.le
  have heq : ((n : ℝ) + 1) * (1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹) = 1 := by
    rw [inv_div]
    field_simp [hsucc.ne']
    ring
  rwa [heq] at hmul

theorem factorialLogRemainder_nonneg (n : ℕ) : 0 ≤ factorialLogRemainder n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlog := nat_mul_log_increment_le_one n
    rw [factorialLogRemainder_succ]
    linarith

theorem factorialLogRemainder_le_one_add_log_pos (n : ℕ) :
    factorialLogRemainder (n + 1) ≤ 1 + Real.log (n + 1 : ℕ) := by
  induction n with
  | zero => norm_num [factorialLogRemainder]
  | succ n ih =>
    have hlog := one_le_succ_mul_log_increment (n + 1) (Nat.succ_pos n)
    have hstep := factorialLogRemainder_succ (n + 1)
    push_cast at ih hlog hstep ⊢
    nlinarith

theorem factorialLogRemainder_le_one_add_log (n : ℕ) :
    factorialLogRemainder n ≤ 1 + Real.log (n + 1 : ℕ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    refine (factorialLogRemainder_le_one_add_log_pos n).trans ?_
    apply add_le_add_right
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.le_succ (n + 1)

theorem abs_factorialLogRemainder_le (n : ℕ) :
    |factorialLogRemainder n| ≤ 1 + Real.log (n + 1 : ℕ) := by
  rw [abs_of_nonneg (factorialLogRemainder_nonneg n)]
  exact factorialLogRemainder_le_one_add_log n

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

theorem every_path_safe {State : Type*} (Safe : ℕ → State → Prop)
    (Allows : ℕ → State → State → Prop) (n : ℕ) (path : ℕ → State)
    (initial : Safe 0 (path 0))
    (closed : ∀ t < n, ∀ s s', Safe t s → Allows t s s' → Safe (t + 1) s')
    (steps : ∀ t < n, Allows t (path t) (path (t + 1))) :
    ∀ t ≤ n, Safe t (path t) := by
  intro t
  induction t with
  | zero => intro _; exact initial
  | succ t ih =>
      intro ht
      have htn : t < n := Nat.lt_of_succ_le ht
      exact closed t htn (path t) (path (t + 1))
        (ih (Nat.le_of_lt htn)) (steps t htn)

theorem exists_population_preserving_equiv {I J Node : Type*}
    [Fintype I] [Fintype J] [DecidableEq Node]
    (f : I → Node) (g : J → Node)
    (counts : ∀ node, Fintype.card {i // f i = node} =
      Fintype.card {j // g j = node}) :
    ∃ e : I ≃ J, ∀ i, g (e i) = f i := by
  classical
  let ef : ∀ node, {i // f i = node} ≃ {j // g j = node} :=
    fun node => Fintype.equivOfCardEq (counts node)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  exact (ef (f i) ⟨i, rfl⟩).property

theorem population_product_eq {I J Node M : Type*}
    [Fintype I] [Fintype J] [DecidableEq Node] [CommMonoid M]
    (f : I → Node) (g : J → Node)
    (counts : ∀ node, Fintype.card {i // f i = node} =
      Fintype.card {j // g j = node}) (cost : Node → M) :
    (∏ i, cost (f i)) = ∏ j, cost (g j) := by
  obtain ⟨e, he⟩ := exists_population_preserving_equiv f g counts
  calc
    (∏ i, cost (f i)) = ∏ i, cost (g (e i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [he i]
    _ = ∏ j, cost (g j) := e.prod_comp (fun j => cost (g j))

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

theorem target_relation_of_windows (a b c : ℤ) (x y z d : ℝ)
    (hd : 0 < d) (tight : x + y + z = 0)
    (hx : |x - (a : ℝ) * d| ≤ d / 10)
    (hy : |y - (b : ℝ) * d| ≤ d / 10)
    (hz : |z + 2 * (c : ℝ) * d| ≤ d / 10) :
    a + b = c + c := by
  obtain ⟨hx₀, hx₁⟩ := abs_le.mp hx
  obtain ⟨hy₀, hy₁⟩ := abs_le.mp hy
  obtain ⟨hz₀, hz₁⟩ := abs_le.mp hz
  let k : ℤ := a + b - 2 * c
  have hkcast : (k : ℝ) = (a : ℝ) + (b : ℝ) - 2 * (c : ℝ) := by
    simp [k]
  have hlow : -(1 : ℝ) < (k : ℝ) := by
    by_contra hn
    have hn' : (k : ℝ) ≤ -1 := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt hd)
    rw [hkcast] at hm
    nlinarith
  have hhigh : (k : ℝ) < 1 := by
    by_contra hn
    have hn' : 1 ≤ (k : ℝ) := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt hd)
    rw [hkcast] at hm
    nlinarith
  have hsmall : |(k : ℝ)| < 1 := abs_lt.mpr ⟨hlow, hhigh⟩
  have hsmallInt : |k| < 1 := by exact_mod_cast hsmall
  have hk : k = 0 := Int.abs_lt_one_iff.mp hsmallInt
  dsimp [k] at hk
  linarith

theorem synchronized_targets_of_windows (targets : Set ℤ)
    (free : ThreeAPFree targets) (a b c : ℤ)
    (ha : a ∈ targets) (hb : b ∈ targets) (hc : c ∈ targets)
    (x y z d : ℝ) (hd : 0 < d) (tight : x + y + z = 0)
    (hx : |x - (a : ℝ) * d| ≤ d / 10)
    (hy : |y - (b : ℝ) * d| ≤ d / 10)
    (hz : |z + 2 * (c : ℝ) * d| ≤ d / 10) :
    a = b ∧ a = c := by
  have hrelation := target_relation_of_windows a b c x y z d hd tight hx hy hz
  have hac : a = c := free ha hc hb hrelation
  exact ⟨by linarith, hac⟩

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

structure RationalLaw (A : Type*) [Fintype A] where
  mass : A → ℚ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace RationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def toFiniteLaw (p : RationalLaw A) : FiniteLaw A where
  mass a := p.mass a
  nonneg a := by exact_mod_cast p.nonneg a
  total := by exact_mod_cast p.total

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

theorem scale_exact_counts (p : RationalLaw A) (D : ℕ) (counts : A → ℕ)
    (hsum : (∑ a, counts a) = D)
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (k : ℕ) :
    (∑ a, k * counts a) = k * D ∧
      ∀ a, ((k * counts a : ℕ) : ℚ) = ((k * D : ℕ) : ℚ) * p.mass a := by
  constructor
  · rw [← Finset.mul_sum, hsum]
  · intro a
    simp only [Nat.cast_mul]
    rw [hcounts a]
    ring

theorem exact_counts_zero_iff (p : RationalLaw A) {D : ℕ} (hD : 0 < D)
    {counts : A → ℕ}
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (a : A) :
    counts a = 0 ↔ p.mass a = 0 := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  constructor
  · intro hzero
    have hz : (D : ℚ) * p.mass a = 0 := by
      rw [← hcounts a, hzero, Nat.cast_zero]
    exact (mul_eq_zero.mp hz).resolve_left hDq
  · intro hzero
    have hz : (counts a : ℚ) = 0 := by rw [hcounts a, hzero, mul_zero]
    exact_mod_cast hz

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
  obtain ⟨D, hD, counts, hsum, hcounts⟩ := p.exists_exact_counts
  refine ⟨counts, by simpa only [hsum] using hD, ?_⟩
  intro a
  rw [hsum]
  exact p.exact_counts_real_mass hD hcounts a

end RationalLaw

private theorem exists_nonnegative_rat_below (x : ℝ) (hx : 0 ≤ x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℚ, 0 ≤ r ∧ (r : ℝ) ≤ x ∧ (r = 0 ↔ x = 0) ∧
      |(r : ℝ) - x| < δ := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0, le_rfl, by simp, by simp, by simpa using hδ⟩
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hlo : max 0 (x - δ) < x := max_lt hxpos (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hlo
  have hrpos : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hrlo
  have hrposq : (0 : ℚ) < r := by exact_mod_cast hrpos
  refine ⟨r, hrposq.le, hrhi.le,
    iff_of_false (ne_of_gt hrposq) hx0, ?_⟩
  have hrlo' : x - δ < r := lt_of_le_of_lt (le_max_right _ _) hrlo
  rw [abs_of_nonpos (sub_nonpos.mpr hrhi.le)]
  linarith

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem exists_rational_approximation (p : FiniteLaw A) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : RationalLaw A,
      (∀ a, q.mass a = 0 ↔ p.mass a = 0) ∧
      ∀ a, |(q.mass a : ℝ) - p.mass a| < ε := by
  classical
  have hpivot : ∃ a, 0 < p.mass a := by
    by_contra h
    have hnonpos : ∀ a, p.mass a ≤ 0 :=
      fun a => le_of_not_gt (fun ha => h ⟨a, ha⟩)
    have hsum : (∑ a, p.mass a) ≤ 0 :=
      Finset.sum_nonpos (fun a _ => hnonpos a)
    rw [p.total] at hsum
    norm_num at hsum
  obtain ⟨a₀, ha₀⟩ := hpivot
  let δ : ℝ := ε / ((Fintype.card A : ℝ) + 1)
  have hcard : 0 ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (Fintype.card A : ℝ) + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * ((Fintype.card A : ℝ) + 1) = ε :=
    div_mul_cancel₀ ε (ne_of_gt hden)
  have hcardδ : 0 ≤ (Fintype.card A : ℝ) * δ := mul_nonneg hcard hδ.le
  have hδle : δ ≤ ε := by nlinarith
  choose r hrnonneg hrle hrzero hrclose using
    fun a => exists_nonnegative_rat_below (p.mass a) (p.nonneg a) δ hδ
  have hsum : (∑ a, (r a : ℝ)) ≤ 1 := by
    calc
      (∑ a, (r a : ℝ)) ≤ ∑ a, p.mass a :=
        Finset.sum_le_sum (fun a _ => hrle a)
      _ = 1 := p.total
  have hrest : 0 ≤ 1 - ∑ a, (r a : ℝ) := sub_nonneg.mpr hsum
  have hrestq : (0 : ℚ) ≤ 1 - ∑ a, r a := by exact_mod_cast hrest
  have hrest_le : 1 - ∑ a, (r a : ℝ) ≤ (Fintype.card A : ℝ) * δ := by
    calc
      1 - ∑ a, (r a : ℝ) = ∑ a, (p.mass a - (r a : ℝ)) := by
        rw [Finset.sum_sub_distrib, p.total]
      _ ≤ ∑ _a : A, δ := by
        apply Finset.sum_le_sum
        intro a _
        have h := (abs_lt.mp (hrclose a)).1
        linarith
      _ = (Fintype.card A : ℝ) * δ := by simp
  let q : RationalLaw A :=
    { mass := fun a => r a + if a = a₀ then 1 - ∑ b, r b else 0
      nonneg := by
        intro a
        apply add_nonneg (hrnonneg a)
        split_ifs
        · exact hrestq
        · exact le_rfl
      total := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring }
  refine ⟨q, ?_, ?_⟩
  · intro a
    by_cases ha : a = a₀
    · subst a
      have hrpos : 0 < r a₀ :=
        lt_of_le_of_ne (hrnonneg a₀) (Ne.symm (fun hz => (ne_of_gt ha₀) ((hrzero a₀).mp hz)))
      have hqpos : 0 < q.mass a₀ := by
        dsimp [q]
        simp only [ite_true]
        linarith
      exact iff_of_false (ne_of_gt hqpos) (ne_of_gt ha₀)
    · simpa only [q, GenericNumerics_ite_eq_right ha, add_zero] using hrzero a
  · intro a
    by_cases ha : a = a₀
    · have hqcast : (q.mass a : ℝ) =
          (r a : ℝ) + (1 - ∑ b, (r b : ℝ)) := by
        simp [q, ha]
      rw [hqcast]
      have habs : |(r a : ℝ) + (1 - ∑ b, (r b : ℝ)) - p.mass a| ≤
          |(r a : ℝ) - p.mass a| + (1 - ∑ b, (r b : ℝ)) := by
        calc
          _ = |((r a : ℝ) - p.mass a) + (1 - ∑ b, (r b : ℝ))| := by
            congr 1
            ring
          _ ≤ |(r a : ℝ) - p.mass a| + |1 - ∑ b, (r b : ℝ)| := abs_add_le _ _
          _ = _ := by rw [abs_of_nonneg hrest]
      have hclose := hrclose a
      nlinarith
    · simpa only [q, GenericNumerics_ite_eq_right ha, add_zero] using
        lt_of_lt_of_le (hrclose a) hδle

theorem exists_exact_type_approximation (p : FiniteLaw A) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∃ counts : A → ℕ,
      (∑ a, counts a) = D ∧
      (∀ a, counts a = 0 ↔ p.mass a = 0) ∧
      ∀ a, |(counts a : ℝ) / (D : ℝ) - p.mass a| < ε := by
  obtain ⟨q, hsupport, hclose⟩ := p.exists_rational_approximation ε hε
  obtain ⟨D, hD, counts, hsum, hcounts⟩ := q.exists_exact_counts
  refine ⟨D, hD, counts, hsum, ?_, ?_⟩
  · intro a
    exact (q.exact_counts_zero_iff hD hcounts a).trans (hsupport a)
  · intro a
    rw [q.exact_counts_real_mass hD hcounts a, RationalLaw.toFiniteLaw_mass]
    exact hclose a

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

def wordPopulation (w : I → A) (a : A) : ℕ := Fintype.card {i // w i = a}

omit [DecidableEq I] in
theorem wordPopulation_sum (w : I → A) :
    ∑ a, wordPopulation w a = Fintype.card I := by
  simpa [wordPopulation] using Fintype.card_congr (Equiv.sigmaFiberEquiv w)

omit [Fintype A] [DecidableEq I] in
theorem wordPopulation_reindex (w : I → A) (e : J ≃ I) (a : A) :
    wordPopulation (w ∘ e) a = wordPopulation w a :=
  Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

abbrev ExactWords (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → A // ∀ a, wordPopulation w a = counts a}

theorem wordPopulation_sigma_fst (counts : A → ℕ) (a : A) :
    wordPopulation (fun i : Σ b, Fin (counts b) => i.1) a = counts a := by
  let e : {i : Σ b, Fin (counts b) // i.1 = a} ≃ Fin (counts a) :=
    { toFun := fun i => i.property ▸ i.val.2
      invFun := fun i => ⟨⟨a, i⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨b, i⟩, h⟩
        cases h
        rfl
      right_inv := by intro i; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem exactWords_nonempty (counts : A → ℕ) : Nonempty (ExactWords counts) := by
  classical
  let e : Fin (∑ a, counts a) ≃ (Σ a, Fin (counts a)) :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨⟨(fun i : Σ a, Fin (counts a) => i.1) ∘ e, ?_⟩⟩
  intro a
  rw [wordPopulation_reindex, wordPopulation_sigma_fst]

omit [Fintype A] [DecidableEq I] in
theorem samePopulation_iff_permutation (w v : I → A) :
    (∀ a, wordPopulation v a = wordPopulation w a) ↔
      ∃ e : Equiv.Perm I, w ∘ e = v := by
  classical
  constructor
  · intro h
    let es : ∀ a, {i // v i = a} ≃ {i // w i = a} :=
      fun a => Fintype.equivOfCardEq (h a)
    refine ⟨Equiv.ofFiberEquiv es, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map es i
  · rintro ⟨e, rfl⟩ a
    exact wordPopulation_reindex w e a

theorem samePopulation_card_mul (w : I → A) :
    Fintype.card {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} *
      (∏ a, (wordPopulation w a).factorial) = (Fintype.card I).factorial := by
  classical
  let G := DomMulAct (Equiv.Perm I)
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  let eOrbit : {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} ≃
      MulAction.orbit G w :=
    Equiv.subtypeEquivRight fun v => by
      rw [samePopulation_iff_permutation, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨e, he⟩
        exact ⟨DomMulAct.mk e, he⟩
      · rintro ⟨g, hg⟩
        exact ⟨DomMulAct.mk.symm g, hg⟩
  let eStab : MulAction.stabilizer G w ≃
      {e : Equiv.Perm I // w ∘ e = w} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
  have hstab : Fintype.card (MulAction.stabilizer G w) =
      ∏ a, (wordPopulation w a).factorial := by
    rw [Fintype.card_congr eStab]
    exact DomMulAct.stabilizer_card w
  have hgroup : Fintype.card G = (Fintype.card I).factorial :=
    (Fintype.card_congr DomMulAct.mk.symm).trans Fintype.card_perm
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w
  rw [← Fintype.card_congr eOrbit, hstab, hgroup] at h
  exact h

theorem exactWords_card (counts : A → ℕ) :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts := by
  classical
  obtain ⟨w⟩ := exactWords_nonempty counts
  let e : ExactWords counts ≃
      {v : Fin (∑ a, counts a) → A // ∀ a,
        wordPopulation v a = wordPopulation w.val a} :=
    Equiv.subtypeEquivRight fun v => by simp only [w.property]
  have h := samePopulation_card_mul w.val
  rw [← Fintype.card_congr e] at h
  simp only [w.property, Fintype.card_fin] at h
  exact Nat.eq_div_of_mul_eq_left
    (ne_of_gt (Nat.prod_factorial_pos Finset.univ counts)) h

theorem exactWords_card_pos (counts : A → ℕ) : 0 < Fintype.card (ExactWords counts) := by
  rw [exactWords_card]
  exact Nat.multinomial_pos Finset.univ counts

theorem exactWords_card_le (counts : A → ℕ) :
    Fintype.card (ExactWords counts) ≤ (Fintype.card A) ^ (∑ a, counts a) := by
  classical
  calc
    Fintype.card (ExactWords counts) ≤
        Fintype.card (Fin (∑ a, counts a) → A) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

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

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (s := Finset.univ) (f := fun a => (Nat.factorial (counts a) : ℝ))
      (fun a _ => by positivity)] at hlog
  linarith

private theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

theorem log_multinomial_eq_entropy_add_remainder (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  rw [log_multinomial_eq_main_add_remainder, finiteEntropy_nat_normalize counts hD,
    mul_sub, mul_div_cancel₀ _ hD']

theorem log_multinomial_sub_entropy_eq_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  by_cases hD : 0 < ∑ a, counts a
  · rw [log_multinomial_eq_entropy_add_remainder counts hD]
    ring
  · have hzero : (∑ a, counts a) = 0 := Nat.eq_zero_of_not_pos hD
    have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, Nat.multinomial]

theorem abs_log_multinomial_sub_entropy_le (counts : A → ℕ) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  rw [log_multinomial_sub_entropy_eq_remainder]
  have hsum_nonneg : 0 ≤ ∑ a, factorialLogRemainder (counts a) :=
    Finset.sum_nonneg (fun a _ => factorialLogRemainder_nonneg (counts a))
  have heach (a : A) : factorialLogRemainder (counts a) ≤
      1 + Real.log ((∑ b, counts b) + 1 : ℕ) := by
    refine (factorialLogRemainder_le_one_add_log (counts a)).trans ?_
    apply add_le_add_right
    apply Real.log_le_log
    · positivity
    · have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      exact_mod_cast Nat.add_le_add_right hle 1
  calc
    |factorialLogRemainder (∑ a, counts a) - ∑ a, factorialLogRemainder (counts a)| ≤
        |factorialLogRemainder (∑ a, counts a)| +
          |∑ a, factorialLogRemainder (counts a)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (factorialLogRemainder (∑ a, counts a))
          (-(∑ a, factorialLogRemainder (counts a)))
    _ = factorialLogRemainder (∑ a, counts a) +
        ∑ a, factorialLogRemainder (counts a) := by
      rw [abs_of_nonneg (factorialLogRemainder_nonneg _), abs_of_nonneg hsum_nonneg]
    _ ≤ (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) +
        ∑ _a : A, (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) :=
      add_le_add (factorialLogRemainder_le_one_add_log _)
        (Finset.sum_le_sum (fun a _ => heach a))
    _ = ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem abs_log_multinomial_div_sub_entropy_le (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  calc
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| =
        |(Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))) /
              (∑ a, counts a : ℕ)| := by
      rw [sub_div, mul_div_cancel_left₀ _ hD'.ne']
    _ = |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| /
              (∑ a, counts a : ℕ) := by
      rw [abs_div, abs_of_pos hD']
    _ ≤ ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (abs_log_multinomial_sub_entropy_le counts) hD'.le

private theorem tendsto_one_add_log_succ_div :
    Tendsto (fun n : ℕ => (1 + Real.log (n + 1 : ℕ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hshift := Real.tendsto_log_nat_add_one_sub_log.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => (1 : ℝ) / n +
        ((Real.log ((n : ℝ) + 1) - Real.log n) / n + Real.log n / n))
      atTop (𝓝 0) := by
    simpa using hconstant.add (hshift.add hlog)
  apply hsum.congr
  intro n
  push_cast
  ring

theorem tendsto_log_multinomial_div_sub_entropy {I : Type*} {l : Filter I}
    (counts : I → A → ℕ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
          (∑ a, counts i a : ℕ) -
        finiteEntropy (fun a => (counts i a : ℝ) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
  have hbound : Tendsto
      (fun i => ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts i a) + 1 : ℕ)) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
    simpa using (tendsto_one_add_log_succ_div.comp htotal).const_mul
      ((Fintype.card A : ℝ) + 1)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [htotal.eventually (eventually_gt_atTop (0 : ℕ))] with i hi
  simpa only [Real.norm_eq_abs] using
    abs_log_multinomial_div_sub_entropy_le (counts i) hi

theorem tendsto_log_multinomial_of_empirical_tendsto {I : Type*} {l : Filter I}
    (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  have herror := tendsto_log_multinomial_div_sub_entropy counts htotal
  have hentropy := tendsto_finiteEntropy_of_tendsto hmass
  simpa only [zero_add, sub_add_cancel] using herror.add hentropy

private theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) =
      (x * Real.log x) * y + x * (y * Real.log y) := by
  calc
    (x * y) * Real.log (x * y) = -entropyTerm (x * y) := by
      simp [entropyTerm]
    _ = -(y * entropyTerm x + x * entropyTerm y) := by
      rw [entropyTerm_mul]
    _ = (x * Real.log x) * y + x * (y * Real.log y) := by
      unfold entropyTerm
      ring

theorem log_multinomial_mul_eq (counts : A → ℕ) (t : ℕ) :
    Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) =
      (t : ℝ) *
          ((∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
            ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (t * ∑ a, counts a) -
        ∑ a, factorialLogRemainder (t * counts a) := by
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a :=
    (Finset.mul_sum Finset.univ counts t).symm
  have hlogs :
      (∑ a, ((t : ℝ) * counts a) * Real.log ((t : ℝ) * counts a)) =
        ((t : ℝ) * Real.log t) * (∑ a, counts a : ℕ) +
          (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ) := by
    simp only [mul_log_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Nat.cast_sum]
  rw [log_multinomial_eq_main_add_remainder, hsum]
  simp only [Nat.cast_mul]
  rw [mul_log_mul, hlogs]
  ring

theorem tendsto_log_multinomial_mul (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  have hsum :
      Tendsto (fun t : ℕ => ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ
      (fun a _ => tendsto_factorialLogRemainder_mul_div (counts a))
  have herror : Tendsto
      (fun t : ℕ =>
        (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
          ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
            (∑ a, counts a : ℕ)) atTop (𝓝 0) := by
    simpa using ((tendsto_factorialLogRemainder_mul_div (∑ a, counts a)).sub
      hsum).div_const (∑ a, counts a : ℕ)
  have hlimit : Tendsto
      (fun t : ℕ =>
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
          (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
            ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
              (∑ a, counts a : ℕ))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply hlimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  rw [log_multinomial_mul_eq, finiteEntropy_nat_normalize counts hD,
    ← Finset.sum_div]
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  field_simp [ht', hD']
  ring

theorem tendsto_log_multinomial_repetitions {I : Type*} {l : Filter I}
    (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (repetitions : I → ℕ) (hrep : Tendsto repetitions l atTop) :
    Tendsto
      (fun i =>
        Real.log (Nat.multinomial Finset.univ
          (fun a => repetitions i * counts a) : ℝ) /
            ((repetitions i : ℝ) * (∑ a, counts a : ℕ)))
      l (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  exact (tendsto_log_multinomial_mul counts hD).comp hrep

theorem tendsto_log_exactWords_card_mul [DecidableEq A] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [exactWords_card] using tendsto_log_multinomial_mul counts hD

theorem abs_log_exactWords_card_sub_entropy_le [DecidableEq A] (counts : A → ℕ) :
    |Real.log (Fintype.card (ExactWords counts) : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  simpa only [exactWords_card] using abs_log_multinomial_sub_entropy_le counts

theorem log_card_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) ≤
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  have hcard := Fintype.card_le_of_injective label hinj
  have hlog : Real.log (Fintype.card O : ℝ) ≤
      Real.log (Fintype.card (ExactWords counts) : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr Fintype.card_pos) (by exact_mod_cast hcard)
  have herror := (abs_le.mp (abs_log_exactWords_card_sub_entropy_le counts)).2
  linarith

theorem log_card_div_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) / (∑ a, counts a : ℕ) ≤
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  have h := div_le_div_of_nonneg_right
    (log_card_le_entropy_of_injective_exactWords counts label hinj) hD'.le
  rw [add_div, mul_div_cancel_left₀ _ hD'.ne', mul_div_assoc] at h
  exact h

theorem tendsto_log_exactWords_card_of_empirical_tendsto [DecidableEq A]
    {I : Type*} {l : Filter I} (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Fintype.card (ExactWords (counts i)) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  simpa only [exactWords_card] using
    tendsto_log_multinomial_of_empirical_tendsto counts p htotal hmass

namespace RationalLaw

theorem exists_exactWords_entropy_limit [DecidableEq A] (p : RationalLaw A) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      (∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a) ∧
      Tendsto
        (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) := by
  obtain ⟨counts, hD, hmass⟩ := p.exists_type_representation
  refine ⟨counts, hD, hmass, ?_⟩
  have hfun : (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      p.toFiniteLaw.mass := funext hmass
  rw [← hfun]
  exact tendsto_log_exactWords_card_mul counts hD

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

/-- The character contribution of all words of one prescribed type. -/
def typeContribution (values : A → ℝ) (p : ℝ) (counts : A → ℕ) (t : ℕ) : ℝ :=
  (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) ^ p *
    ∏ a, values a ^ (t * counts a)

theorem typeContribution_pos (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (t : ℕ) :
    0 < typeContribution values p counts t := by
  unfold typeContribution
  exact mul_pos
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p)
    (Finset.prod_pos (fun a _ => pow_pos (hvalues a) _))

theorem log_typeContribution (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (t : ℕ) :
    Real.log (typeContribution values p counts t) =
      p * Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) +
        (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (values a) := by
  unfold typeContribution
  rw [Real.log_mul
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p).ne'
    (Finset.prod_pos (fun a _ => pow_pos (hvalues a) _)).ne',
    Real.log_rpow (Nat.cast_pos.mpr (exactWords_card_pos _)),
    Real.log_prod (fun a _ => (pow_pos (hvalues a) _).ne')]
  simp only [Real.log_pow, Nat.cast_mul, mul_assoc, Finset.mul_sum]

/-- Repeating one exact type has its Shannon entropy growth rate. -/
theorem typeContribution_rate (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (typeContribution values p counts t) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (p * finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a))) := by
  have hlimit := ((tendsto_log_exactWords_card_mul counts hD).const_mul p).add_const
    (∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a))
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  rw [log_typeContribution values p counts hvalues]
  have ht' : (t : ℝ) ≠ 0 := (Nat.cast_pos.mpr ht).ne'
  have hD' : (∑ a, counts a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  push_cast
  field_simp

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
  obtain ⟨counts, hD, hmass⟩ := q.exists_type_representation
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

/-- It suffices to prove one finite inequality for every integral type. -/
theorem log_tag_of_integral_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p * ∏ a, values a ^ counts a ≤
        C * source ^ (∑ a, counts a)) :
    p * finiteEntropy q.mass +
      ∑ a, q.mass a * Real.log (values a) ≤ Real.log source := by
  apply log_tag_of_finite_type_bounds q values p source C hvalues hsource hC
  intro counts hD t ht
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a := by
    rw [Finset.mul_sum]
  have hpositive : 0 < ∑ a, t * counts a := by
    rw [hsum]
    exact Nat.mul_pos ht hD
  simpa only [typeContribution, hsum] using hfinite (fun a => t * counts a) hpositive

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

/- BEGIN all-fields module GenericProfile -/
section AllFieldsModule13


section ProfileModule0

namespace OAI

/-!
# The symmetrized tensor-character product

The sixfold product is defined on arbitrary finite, possibly different, leg
spaces. Its symmetry follows by permuting the factors and requires no symmetry
of the character itself.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character 𝕜))
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- The product of character values in the six orders of possibly different legs. -/
def sixfoldProduct (T : Tensor 𝕜 X Y Z) : ℝ :=
  χ.value T *
    χ.value (fun y z x => T x y z) *
    χ.value (fun z x y => T x y z) *
    χ.value (fun x z y => T x y z) *
    χ.value (fun z y x => T x y z) *
    χ.value (fun y x z => T x y z)

/-- Cycling the legs permutes the six factors. -/
theorem sixfoldProduct_cyclic (T : Tensor 𝕜 X Y Z) :
    χ.sixfoldProduct (fun y z x => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- Exchanging the first two legs permutes the six factors. -/
theorem sixfoldProduct_swap12 (T : Tensor 𝕜 X Y Z) :
    χ.sixfoldProduct (fun y x z => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- The leg exchange used by the middle convolution branch preserves the product. -/
theorem sixfoldProduct_swap23 (T : Tensor 𝕜 X Y Z) :
    χ.sixfoldProduct (fun x z y => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- Changing coordinates separately on the legs preserves the sixfold product. -/
theorem sixfoldProduct_reindex (T : Tensor 𝕜 X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.sixfoldProduct (Tensor.pullback ex ey ez T) = χ.sixfoldProduct T := by
  unfold sixfoldProduct
  rw [χ.value_reindex T ex ey ez]
  have h1 := χ.value_reindex (fun y z x => T x y z) ey ez ex
  have h2 := χ.value_reindex (fun z x y => T x y z) ez ex ey
  have h3 := χ.value_reindex (fun x z y => T x y z) ex ez ey
  have h4 := χ.value_reindex (fun z y x => T x y z) ez ey ex
  have h5 := χ.value_reindex (fun y x z => T x y z) ey ex ez
  change χ.value (fun y z x => T (ex x) (ey y) (ez z)) =
    χ.value (fun y z x => T x y z) at h1
  change χ.value (fun z x y => T (ex x) (ey y) (ez z)) =
    χ.value (fun z x y => T x y z) at h2
  change χ.value (fun x z y => T (ex x) (ey y) (ez z)) =
    χ.value (fun x z y => T x y z) at h3
  change χ.value (fun z y x => T (ex x) (ey y) (ez z)) =
    χ.value (fun z y x => T x y z) at h4
  change χ.value (fun y x z => T (ex x) (ey y) (ez z)) =
    χ.value (fun y x z => T x y z) at h5
  simp only [Tensor.pullback]
  rw [h1, h2, h3, h4, h5]

/-- Commuting convolution inputs preserves the sixfold character product. -/
theorem sixfoldProduct_convolution_comm (a b : ℕ) :
    χ.sixfoldProduct (convolution a b) = χ.sixfoldProduct (convolution b a) := by
  let e : Fin (a + b - 1) ≃ Fin (b + a - 1) := finCongr (by omega)
  have heq : Tensor.pullback (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
      (convolution (K := 𝕜) b a) = fun j i k => convolution a b i j k := by
    funext j i k
    exact (convolution_comm a b i j k).symm
  have h := χ.sixfoldProduct_reindex (convolution b a)
    (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
  rw [heq, χ.sixfoldProduct_swap12] at h
  exact h

/-- The Section 5 symmetrized value with mean singleton-leg exponent `t`. -/
def symmetrizedProfile (t : ℝ) (T : Tensor 𝕜 X Y Z) : ℝ :=
  χ.sixfoldProduct T ^ (1 / (6 * t))

theorem symmetrizedProfile_cyclic (t : ℝ) (T : Tensor 𝕜 X Y Z) :
    χ.symmetrizedProfile t (fun y z x => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_cyclic T)

theorem symmetrizedProfile_swap12 (t : ℝ) (T : Tensor 𝕜 X Y Z) :
    χ.symmetrizedProfile t (fun y x z => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_swap12 T)

theorem symmetrizedProfile_swap23 (t : ℝ) (T : Tensor 𝕜 X Y Z) :
    χ.symmetrizedProfile t (fun x z y => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_swap23 T)

theorem symmetrizedProfile_reindex (t : ℝ) (T : Tensor 𝕜 X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.symmetrizedProfile t (Tensor.pullback ex ey ez T) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_reindex T ex ey ez)

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end ProfileModule0


section ProfileModule1

namespace OAI

/-!
# Algebra and bounds for the sixfold character product

The product over all six leg orders is multiplicative and nonnegative. A
nonzero tensor has product at least one, and every rank decomposition bounds
the product by the sixth power of its size.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character 𝕜))
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

/-- Taking the product over all six leg orders preserves tensor multiplication. -/
theorem sixfoldProduct_product (T : Tensor 𝕜 X Y Z) (S : Tensor 𝕜 U V W) :
    χ.sixfoldProduct (Tensor.product T S) = χ.sixfoldProduct T * χ.sixfoldProduct S := by
  unfold sixfoldProduct
  change χ.value (Tensor.product T S) *
      χ.value (Tensor.product (fun y z x => T x y z) (fun v w u => S u v w)) *
      χ.value (Tensor.product (fun z x y => T x y z) (fun w u v => S u v w)) *
      χ.value (Tensor.product (fun x z y => T x y z) (fun u w v => S u v w)) *
      χ.value (Tensor.product (fun z y x => T x y z) (fun w v u => S u v w)) *
      χ.value (Tensor.product (fun y x z => T x y z) (fun v u w => S u v w)) = _
  simp only [χ.map_product]
  ring

/-- All six factors of the symmetrized product are nonnegative. -/
theorem sixfoldProduct_nonneg (T : Tensor 𝕜 X Y Z) : 0 ≤ χ.sixfoldProduct T := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (χ.nonneg T) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)

/-- Every nonzero tensor has symmetrized character product at least one. -/
theorem one_le_sixfoldProduct {T : Tensor 𝕜 X Y Z} (hT : T ≠ 0) :
    1 ≤ χ.sixfoldProduct T := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hT
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hy
  change T x y z ≠ 0 at hz
  have h0 := χ.one_le_value hT
  have h1 : 1 ≤ χ.value (fun y z x => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S y z x) h))
  have h2 : 1 ≤ χ.value (fun z x y => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S z x y) h))
  have h3 : 1 ≤ χ.value (fun x z y => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S x z y) h))
  have h4 : 1 ≤ χ.value (fun z y x => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S z y x) h))
  have h5 : 1 ≤ χ.value (fun y x z => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S y x z) h))
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2) h3) h4) h5

/-- In particular, the sixfold product of a nonzero tensor is positive. -/
theorem sixfoldProduct_pos {T : Tensor 𝕜 X Y Z} (hT : T ≠ 0) :
    0 < χ.sixfoldProduct T :=
  zero_lt_one.trans_le (χ.one_le_sixfoldProduct hT)

private theorem rankAtMost_swap12 {K X Y Z : Type*} [CommSemiring K]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    Tensor.RankAtMost (fun y x z => T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, a, c, ?_⟩
  funext y x z
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [Tensor.rankOne]
  ring

/-- A rank decomposition bounds each of the six character factors. -/
theorem sixfoldProduct_le_rank {T : Tensor 𝕜 X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost T r) : χ.sixfoldProduct T ≤ (r : ℝ) ^ 6 := by
  have h0 := χ.value_le_rank h
  have h1 := χ.value_le_rank h.cyclic
  have h2 := χ.value_le_rank h.cyclic.cyclic
  have h5 := χ.value_le_rank (rankAtMost_swap12 h)
  have h3 := χ.value_le_rank (rankAtMost_swap12 h).cyclic
  have h4 := χ.value_le_rank (rankAtMost_swap12 h).cyclic.cyclic
  unfold sixfoldProduct
  calc
    _ ≤ (r : ℝ) * r * r * r * r * r := by
      gcongr <;> first
        | exact χ.nonneg _
        | exact h0
        | exact h1
        | exact h2
        | exact h3
        | exact h4
    _ = _ := by ring

end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end ProfileModule1


section ProfileModule2

namespace OAI

/-!
# Positivity and rank bounds for the normalized profile

The normalization exponent is positive when the mean singleton-leg exponent
is positive. Under this hypothesis, passing to the profile preserves order,
and a rank bound `r` becomes the bound `r ^ (1 / t)`.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character 𝕜))
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

theorem symmetrizedProfile_nonneg (t : ℝ) (T : Tensor 𝕜 X Y Z) :
    0 ≤ χ.symmetrizedProfile t T :=
  Real.rpow_nonneg (χ.sixfoldProduct_nonneg T) _

theorem symmetrizedProfile_pos (t : ℝ) {T : Tensor 𝕜 X Y Z} (hT : T ≠ 0) :
    0 < χ.symmetrizedProfile t T :=
  Real.rpow_pos_of_pos (χ.sixfoldProduct_pos hT) _

theorem one_le_symmetrizedProfile {t : ℝ} (ht : 0 < t)
    {T : Tensor 𝕜 X Y Z} (hT : T ≠ 0) : 1 ≤ χ.symmetrizedProfile t T := by
  exact Real.one_le_rpow (χ.one_le_sixfoldProduct hT) (by positivity)

/-- Tensor products become products of normalized profile values. -/
theorem symmetrizedProfile_product (t : ℝ) (T : Tensor 𝕜 X Y Z)
    (S : Tensor 𝕜 U V W) :
    χ.symmetrizedProfile t (Tensor.product T S) =
      χ.symmetrizedProfile t T * χ.symmetrizedProfile t S := by
  simp only [symmetrizedProfile, χ.sixfoldProduct_product]
  exact Real.mul_rpow (χ.sixfoldProduct_nonneg T) (χ.sixfoldProduct_nonneg S)

/-- Positive normalization preserves the order of the underlying sixfold products. -/
theorem symmetrizedProfile_le_iff {t : ℝ} (ht : 0 < t)
    (T : Tensor 𝕜 X Y Z) (S : Tensor 𝕜 U V W) :
    χ.symmetrizedProfile t T ≤ χ.symmetrizedProfile t S ↔
      χ.sixfoldProduct T ≤ χ.sixfoldProduct S := by
  exact Real.rpow_le_rpow_iff (χ.sixfoldProduct_nonneg T)
    (χ.sixfoldProduct_nonneg S) (by positivity)

/-- The symmetrized profile has the rank bound used in Section 5. -/
theorem symmetrizedProfile_le_rank {t : ℝ} (ht : 0 < t)
    {T : Tensor 𝕜 X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.symmetrizedProfile t T ≤ (r : ℝ) ^ (1 / t) := by
  calc
    χ.symmetrizedProfile t T ≤ ((r : ℝ) ^ 6) ^ (1 / (6 * t)) :=
      Real.rpow_le_rpow (χ.sixfoldProduct_nonneg T) (χ.sixfoldProduct_le_rank h)
        (by positivity)
    _ = (r : ℝ) ^ (1 / t) := by
      rw [← Real.rpow_natCast (r : ℝ) 6, ← Real.rpow_mul (by positivity)]
      congr 1
      field_simp
      norm_num

/-- A factor `c ^ (6*t)` in the sixfold product becomes `c` in the profile. -/
theorem mul_symmetrizedProfile_le_of_le {t c : ℝ} (ht : 0 < t) (hc : 0 ≤ c)
    (T : Tensor 𝕜 X Y Z) (S : Tensor 𝕜 U V W)
    (h : c ^ (6 * t) * χ.sixfoldProduct T ≤ χ.sixfoldProduct S) :
    c * χ.symmetrizedProfile t T ≤ χ.symmetrizedProfile t S := by
  have hp := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg hc _) (χ.sixfoldProduct_nonneg T)) h
    (show 0 ≤ 1 / (6 * t) by positivity)
  rw [Real.mul_rpow (Real.rpow_nonneg hc _) (χ.sixfoldProduct_nonneg T),
    one_div, Real.rpow_rpow_inv hc (ne_of_gt (mul_pos (by norm_num) ht))] at hp
  simpa only [symmetrizedProfile, one_div] using hp

end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end ProfileModule2


section ProfileModule3

namespace OAI

/-!
# (Character 𝕜) identities for polynomial convolution

The boundary convolution tensors are dot products. In the sixfold character
product, each possible singleton leg appears exactly twice. Consequently the
normalization by the average dot-product exponent gives the boundary values
of the polynomial profile from Section 5.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
namespace Character

open MatrixMultiplication.Foundation

variable (χ : (Character 𝕜))

/-- A symmetric dot product occurs twice in each of its three leg positions. -/
theorem sixfoldProduct_dotPairing (n : ℕ) :
    χ.sixfoldProduct (Tensor.dotPairing (K := 𝕜) (Fin n)) =
      (χ.value (Tensor.dotPairing (K := 𝕜) (Fin n)) *
        χ.value (Tensor.cyclic (Tensor.dotPairing (K := 𝕜) (Fin n))) *
        χ.value (Tensor.cyclic (Tensor.cyclic
          (Tensor.dotPairing (K := 𝕜) (Fin n))))) ^ 2 := by
  let D := Tensor.dotPairing (K := 𝕜) (Fin n)
  have h3 : (fun (i : Fin n) (_ : Unit) (j : Fin n) => D i j ()) =
      Tensor.cyclic D := by
    funext i u j
    simp [D, Tensor.cyclic, Tensor.dotPairing, eq_comm]
  have h4 : (fun (_ : Unit) (j i : Fin n) => D i j ()) =
      Tensor.cyclic (Tensor.cyclic D) := by
    funext u j i
    simp [D, Tensor.cyclic, Tensor.dotPairing, eq_comm]
  have h5 : (fun (j i : Fin n) (_ : Unit) => D i j ()) = D := by
    funext j i u
    simp [D, Tensor.dotPairing, eq_comm]
  change χ.sixfoldProduct D = _
  unfold sixfoldProduct
  change χ.value D * χ.value (Tensor.cyclic D) *
      χ.value (Tensor.cyclic (Tensor.cyclic D)) *
      χ.value (fun (i : Fin n) (_ : Unit) (j : Fin n) => D i j ()) *
      χ.value (fun (_ : Unit) (j i : Fin n) => D i j ()) *
      χ.value (fun (j i : Fin n) (_ : Unit) => D i j ()) = _
  rw [h3, h4, h5]
  ring

/-- The boundary `C(1,b)` has the sixfold product of a dot product. -/
theorem sixfoldProduct_convolution_one_left (b : ℕ) :
    χ.sixfoldProduct (convolution 1 b) =
      χ.sixfoldProduct (Tensor.dotPairing (K := 𝕜) (Fin b)) := by
  have h := χ.sixfoldProduct_reindex (convolution 1 b)
    convolutionOneInputEquiv (Equiv.refl (Fin b)) (convolutionOneOutputEquiv b)
  rw [convolution_one_left_dotPairing] at h
  calc
    _ = χ.sixfoldProduct (Tensor.cyclic (Tensor.cyclic
        (Tensor.dotPairing (K := 𝕜) (Fin b)))) := h.symm
    _ = χ.sixfoldProduct (Tensor.cyclic (Tensor.dotPairing (K := 𝕜) (Fin b))) :=
      χ.sixfoldProduct_cyclic _
    _ = _ := χ.sixfoldProduct_cyclic _

/-- The boundary `C(a,1)` has the same dot-product product. -/
theorem sixfoldProduct_convolution_one_right (a : ℕ) :
    χ.sixfoldProduct (convolution a 1) =
      χ.sixfoldProduct (Tensor.dotPairing (K := 𝕜) (Fin a)) := by
  rw [χ.sixfoldProduct_convolution_comm, χ.sixfoldProduct_convolution_one_left]

/-- The mean of the character's three singleton-leg exponents. -/
def meanExponent : ℝ := (χ.pX + χ.pY + χ.pZ) / 3

theorem meanExponent_nonneg : 0 ≤ χ.meanExponent := by
  exact div_nonneg (add_nonneg (add_nonneg χ.pX_nonneg χ.pY_nonneg) χ.pZ_nonneg)
    (by norm_num)

theorem meanExponent_le_one : χ.meanExponent ≤ 1 := by
  unfold meanExponent
  have hx := χ.pX_le_one
  have hy := χ.pY_le_one
  have hz := χ.pZ_le_one
  linarith

/-- The three exponents occur twice in the sixfold boundary product. -/
theorem sixfoldProduct_dotPairing_eq_rpow {n : ℕ} (hn : 0 < n) :
    χ.sixfoldProduct (Tensor.dotPairing (K := 𝕜) (Fin n)) =
      (n : ℝ) ^ (6 * χ.meanExponent) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [χ.sixfoldProduct_dotPairing, χ.value_dotPairing hn,
    χ.value_cyclic_dotPairing hn, χ.value_cyclic_cyclic_dotPairing hn,
    ← Real.rpow_add hn', ← Real.rpow_add hn']
  calc
    ((n : ℝ) ^ (χ.pZ + χ.pY + χ.pX)) ^ 2 =
        (n : ℝ) ^ ((χ.pZ + χ.pY + χ.pX) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast hn'.le _ 2).symm
    _ = _ := by congr 1; unfold meanExponent; ring

/-- The positive-size boundary product has its exact normalized power. -/
theorem sixfoldProduct_convolution_one_left_eq_rpow {b : ℕ} (hb : 0 < b) :
    χ.sixfoldProduct (convolution 1 b) = (b : ℝ) ^ (6 * χ.meanExponent) := by
  rw [χ.sixfoldProduct_convolution_one_left, χ.sixfoldProduct_dotPairing_eq_rpow hb]

/-- The polynomial profile `P(a,b)` normalized by the actual mean exponent. -/
def convolutionProfile (a b : ℕ) : ℝ :=
  χ.symmetrizedProfile χ.meanExponent (convolution a b)

/-- Swapping the two polynomial inputs preserves the normalized profile. -/
theorem convolutionProfile_comm (a b : ℕ) :
    χ.convolutionProfile a b = χ.convolutionProfile b a := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * χ.meanExponent)))
    (χ.sixfoldProduct_convolution_comm a b)

theorem convolutionProfile_nonneg (a b : ℕ) : 0 ≤ χ.convolutionProfile a b :=
  χ.symmetrizedProfile_nonneg _ _

/-- Nonzero polynomial multiplication gives a positive normalized profile. -/
theorem convolutionProfile_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.convolutionProfile a b :=
  χ.symmetrizedProfile_pos _ (convolution_nonzero ha hb)

/-- The evaluation/interpolation algorithm bounds the normalized profile. -/
theorem convolutionProfile_le {a b : ℕ} (ht : 0 < χ.meanExponent) :
    χ.convolutionProfile a b ≤ (a + b - 1 : ℕ) ^ (1 / χ.meanExponent) :=
  χ.symmetrizedProfile_le_rank ht (convolution_rankAtMost a b)

/-- The normalization gives the exact initial value `P(1,b) = b`. -/
theorem convolutionProfile_one_left {b : ℕ} (ht : 0 < χ.meanExponent) (hb : 0 < b) :
    χ.convolutionProfile 1 b = b := by
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  unfold convolutionProfile symmetrizedProfile
  rw [χ.sixfoldProduct_convolution_one_left_eq_rpow hb, ← Real.rpow_mul hb'.le]
  rw [show (6 * χ.meanExponent) * (1 / (6 * χ.meanExponent)) = 1 by
    field_simp [ne_of_gt ht]]
  exact Real.rpow_one _

/-- Input symmetry gives the other exact initial value `P(a,1) = a`. -/
theorem convolutionProfile_one_right {a : ℕ} (ht : 0 < χ.meanExponent) (ha : 0 < a) :
    χ.convolutionProfile a 1 = a := by
  rw [χ.convolutionProfile_comm, χ.convolutionProfile_one_left ht ha]

/-- Interpolation bounds an individual character on polynomial convolution. -/
theorem value_convolution_le (a b : ℕ) :
    χ.value (convolution a b) ≤ (a + b - 1 : ℕ) :=
  χ.value_le_rank (convolution_rankAtMost a b)

/-- Positive input sizes give a positive individual character value. -/
theorem value_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.value (convolution a b) :=
  zero_lt_one.trans_le (χ.one_le_value (convolution_nonzero ha hb))

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end ProfileModule3


section ProfileModule4

namespace OAI

/-!
# The six permuted tensor characters

Precomposing a character with a leg permutation gives another character. The
six resulting values multiply to the symmetrized product, and each singleton
leg exponent occurs twice among their first-leg exponents.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable (χ : (Character 𝕜))

/-- The reflected character exchanges the second and third tensor legs. -/
def swap23Character : (Character 𝕜) where
  value T := χ.value (fun x z y => T x y z)
  nonneg T := χ.nonneg (fun x z y => T x y z)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    have heq : (fun x z y => Tensor.directSum T x y z) =
        Tensor.directSum (fun i x z y => T i x y z) := by
      funext x z y
      simp only [Tensor.directSum, and_comm]
    change χ.value (fun x z y => Tensor.directSum T x y z) = _
    rw [heq, χ.map_directSum]
  map_product T S := χ.map_product (fun x z y => T x y z) (fun x z y => S x y z)
  monotone T A B C := by
    have heq : (fun x z y => Tensor.restrict A B C T x y z) =
        Tensor.restrict A C B (fun x z y => T x y z) := by
      funext x z y
      simp only [Tensor.restrict]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring
    change χ.value (fun x z y => Tensor.restrict A B C T x y z) ≤ _
    rw [heq]
    exact χ.monotone (fun x z y => T x y z) A C B

@[simp] theorem swap23Character_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor 𝕜 X Y Z) :
    χ.swap23Character.value T = χ.value (fun x z y => T x y z) := rfl

/-- The three cyclic orders followed by their reflected orders. -/
def permutedCharacter (i : Fin 6) : (Character 𝕜) :=
  ![χ, χ.cyclicCharacter, χ.cyclicCharacter.cyclicCharacter,
    χ.swap23Character, χ.swap23Character.cyclicCharacter,
    χ.swap23Character.cyclicCharacter.cyclicCharacter] i

/-- The six permuted characters give exactly the sixfold product on any legs. -/
theorem prod_permutedCharacter_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor 𝕜 X Y Z) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value T) = χ.sixfoldProduct T := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change χ.value T * (χ.value (fun y z x => T x y z) *
      (χ.value (fun z x y => T x y z) * (χ.value (fun x z y => T x y z) *
      (χ.value (fun y x z => T x y z) * χ.value (fun z y x => T x y z))))) = _
  unfold sixfoldProduct
  ring

@[simp] theorem cyclicCharacter_pX : χ.cyclicCharacter.pX = χ.pZ := by
  rfl

@[simp] theorem cyclicCharacter_pY : χ.cyclicCharacter.pY = χ.pX := rfl

@[simp] theorem cyclicCharacter_pZ : χ.cyclicCharacter.pZ = χ.pY := rfl

@[simp] theorem swap23Character_pX : χ.swap23Character.pX = χ.pX := by
  unfold pX pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pY : χ.swap23Character.pY = χ.pZ := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pZ : χ.swap23Character.pZ = χ.pY := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

/-- Each singleton-leg exponent occurs twice among the first-leg exponents. -/
theorem sum_permutedCharacter_pX :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 2 * (χ.pX + χ.pY + χ.pZ) := by
  simp [permutedCharacter, Fin.sum_univ_succ]
  ring

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end ProfileModule4


end AllFieldsModule13
/- END all-fields module GenericProfile -/

/- BEGIN all-fields module GenericDeterminantCore -/
section AllFieldsModule14
set_option autoImplicit false

section Module0
namespace OAI

/-!
# Degree bounds for the binary determinant relation

The polynomial identity `A + X * B = 0` forces one extra degree of cancellation:
if `A` has degree less than `e + 1`, then `B` has degree less than `e`.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantBounds

open Polynomial

variable {R : Type*} [CommRing R]

/-- A degree bound on the first component of a diagonal relation bounds the
second component by one degree less. -/
theorem degree_lt_of_diagonal_eq_zero {e : ℕ} {A B : R[X]}
    (hA : A.degree < (e + 1 : ℕ)) (h : A + X * B = 0) :
    B.degree < e := by
  rw [degree_lt_iff_coeff_zero] at hA ⊢
  intro n hn
  have hc := congrArg (fun p : R[X] => p.coeff (n + 1)) h
  simpa only [coeff_add, coeff_X_mul, hA (n + 1) (by omega),
    zero_add, coeff_zero] using hc

/-- Multiplication by `-X` increases the strict degree bound by at most one. -/
theorem degree_neg_X_mul_lt {e : ℕ} {q : R[X]} (hq : q.degree < e) :
    (-(X * q) : R[X]).degree < (e + 1 : ℕ) := by
  rw [degree_lt_iff_coeff_zero] at hq ⊢
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [coeff_neg, Nat.succ_eq_add_one, coeff_X_mul]
  exact neg_eq_zero.mpr (hq k (by omega))

/-- The determinant generator preserves the two component degree bounds. -/
theorem determinant_degree_bounds {e : ℕ} {q : R[X]} (hq : q.degree < e) :
    (-(X * q) : R[X]).degree < (e + 1 : ℕ) ∧ q.degree < (e + 1 : ℕ) := by
  refine ⟨degree_neg_X_mul_lt hq, hq.trans_le ?_⟩
  exact_mod_cast Nat.le_succ e

/-- Pairs representing forms of bidegree `(e, 1)`. -/
abbrev BoundedPair (R : Type*) [CommRing R] (e : ℕ) :=
  degreeLT R (e + 1) × degreeLT R (e + 1)

/-- Diagonal substitution on the space with the prescribed degree bounds. -/
def diagonal (e : ℕ) : BoundedPair R e →ₗ[R] R[X] where
  toFun p := (p.1 : R[X]) + X * (p.2 : R[X])
  map_add' p q := by simp [mul_add]; ring
  map_smul' c p := by simp [smul_eq_C_mul]; ring

/-- The first component of multiplication by `uw-vs`. -/
def negativeShift (e : ℕ) : degreeLT R e →ₗ[R] degreeLT R (e + 1) :=
  ((LinearMap.mulLeft R (-X : R[X])).domRestrict (degreeLT R e)).codRestrict
    (degreeLT R (e + 1)) (fun q => mem_degreeLT.mpr <| by
      simpa only [LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, neg_mul] using
        degree_neg_X_mul_lt (mem_degreeLT.mp q.2))

/-- Increase the allowed degree bound by one. -/
def widen (e : ℕ) : degreeLT R e →ₗ[R] degreeLT R (e + 1) :=
  Submodule.inclusion (degreeLT_mono (Nat.le_succ e))

@[simp] theorem widen_coe (e : ℕ) (q : degreeLT R e) :
    (widen e q : R[X]) = (q : R[X]) :=
  Submodule.coe_inclusion _ q

/-- Multiplication by `uw-vs` lands in the bounded pair space. -/
def determinant (e : ℕ) : degreeLT R e →ₗ[R] BoundedPair R e where
  toFun q := (negativeShift e q, widen e q)
  map_add' p q := Prod.ext (map_add (negativeShift e) p q) (map_add (widen e) p q)
  map_smul' c p := Prod.ext (map_smul (negativeShift e) c p) (map_smul (widen e) c p)

@[simp] theorem diagonal_apply (e : ℕ) (p : BoundedPair R e) :
    diagonal e p = (p.1 : R[X]) + X * (p.2 : R[X]) := rfl

@[simp] theorem determinant_fst (e : ℕ) (q : degreeLT R e) :
    ((determinant e q).1 : R[X]) = -X * (q : R[X]) := rfl

@[simp] theorem determinant_snd (e : ℕ) (q : degreeLT R e) :
    ((determinant (R := R) e q).2 : R[X]) = (q : R[X]) := by
  change (widen e q : R[X]) = (q : R[X])
  exact widen_coe e q

@[simp] theorem diagonal_determinant (e : ℕ) (q : degreeLT R e) :
    diagonal e (determinant e q) = 0 := by
  simp only [diagonal_apply, determinant_fst, determinant_snd, neg_mul, neg_add_cancel]

/-- The determinant map with codomain restricted to the diagonal kernel. -/
def toKernel (e : ℕ) : degreeLT R e →ₗ[R] LinearMap.ker (diagonal (R := R) e) :=
  (determinant (R := R) e).codRestrict _ fun q => diagonal_determinant e q

@[simp] theorem toKernel_coe (e : ℕ) (q : degreeLT R e) :
    (toKernel e q : BoundedPair R e) = determinant e q := rfl

theorem toKernel_bijective (e : ℕ) : Function.Bijective (toKernel (R := R) e) := by
  constructor
  · intro p q h
    apply Subtype.ext
    have hc := congrArg (fun z : LinearMap.ker (diagonal (R := R) e) =>
      (z.1.2 : R[X])) h
    simpa only [toKernel_coe, determinant_snd] using hc
  · rintro ⟨p, hp⟩
    let q : degreeLT R e := ⟨(p.2 : R[X]), mem_degreeLT.mpr <|
      degree_lt_of_diagonal_eq_zero (mem_degreeLT.mp p.1.2) hp⟩
    refine ⟨q, Subtype.ext ?_⟩
    change determinant (R := R) e q = p
    apply Prod.ext
    · apply Subtype.ext
      rw [determinant_fst]
      have h : (p.1 : R[X]) + X * (p.2 : R[X]) = 0 := hp
      simpa only [q, neg_mul] using (eq_neg_of_add_eq_zero_left h).symm
    · apply Subtype.ext
      exact determinant_snd e q

/-- The bounded determinant kernel has exactly the degree-`< e` polynomials
as its parameters, including at `e = 0`. -/
def kernelEquiv (e : ℕ) : degreeLT R e ≃ₗ[R] LinearMap.ker (diagonal (R := R) e) :=
  LinearEquiv.ofBijective (toKernel e) (toKernel_bijective e)

/-- The finite determinant kernel has dimension `e`. -/
theorem finrank_kernel (K : Type*) [Field K] (e : ℕ) :
    Module.finrank K (LinearMap.ker (diagonal (R := K) e)) = e := by
  rw [← (kernelEquiv (R := K) e).finrank_eq]
  simpa using Module.finrank_eq_card_basis (degreeLT.basis K e)

/-- The diagonal has the next larger degree bound. -/
theorem degree_diagonal_lt (e : ℕ) (p : BoundedPair R e) :
    (diagonal e p).degree < (e + 2 : ℕ) := by
  change ((p.1 : R[X]) + X * (p.2 : R[X])).degree < ((e + 2 : ℕ) : WithBot ℕ)
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · refine (mem_degreeLT.mp p.1.2).trans_le ?_
    exact_mod_cast (show e + 1 ≤ e + 2 by omega)
  · simpa only [degree_neg, Nat.add_assoc] using
      degree_neg_X_mul_lt (mem_degreeLT.mp p.2.2)

/-- Diagonal substitution with both the domain and codomain degree bounded. -/
def diagonalToDegreeLT (e : ℕ) : BoundedPair R e →ₗ[R] degreeLT R (e + 2) :=
  (diagonal e).codRestrict _ fun p => mem_degreeLT.mpr (degree_diagonal_lt e p)

@[simp] theorem diagonalToDegreeLT_coe (e : ℕ) (p : BoundedPair R e) :
    (diagonalToDegreeLT e p : R[X]) = diagonal e p := rfl

/-- Removing the constant coefficient lowers the strict degree bound by one. -/
theorem degree_divX_lt {e : ℕ} {p : R[X]} (hp : p.degree < (e + 1 : ℕ)) :
    p.divX.degree < e := by
  rw [degree_lt_iff_coeff_zero] at hp ⊢
  intro n hn
  rw [coeff_divX]
  exact hp (n + 1) (by omega)

/-- Every polynomial of the output degree is a diagonal restriction of a
bounded pair. -/
theorem diagonalToDegreeLT_surjective (e : ℕ) :
    Function.Surjective (diagonalToDegreeLT (R := R) e) := by
  intro p
  let A : degreeLT R (e + 1) := ⟨C ((p : R[X]).coeff 0), mem_degreeLT.mpr <|
    degree_C_lt.trans_le (by exact_mod_cast (show 1 ≤ e + 1 by omega))⟩
  let B : degreeLT R (e + 1) := ⟨(p : R[X]).divX, mem_degreeLT.mpr <|
    degree_divX_lt (by simpa only [Nat.add_assoc] using mem_degreeLT.mp p.2)⟩
  refine ⟨(A, B), ?_⟩
  apply Subtype.ext
  change C ((p : R[X]).coeff 0) + X * (p : R[X]).divX = (p : R[X])
  simpa only [add_comm] using X_mul_divX_add (p : R[X])

@[simp] theorem ker_diagonalToDegreeLT (e : ℕ) :
    LinearMap.ker (diagonalToDegreeLT (R := R) e) = LinearMap.ker (diagonal e) := by
  ext p
  simp only [LinearMap.mem_ker]
  exact Subtype.val_inj.symm

end MatrixMultiplication.AuxiliarySeparation.DeterminantBounds

end

end OAI

end Module0


section Module1
namespace OAI

/-!
# The determinant kernel of diagonal substitution

A form `A(u,v)s + B(u,v)w` of bidegree `(e,1)` is represented on the affine chart
`u = 1` by the polynomial pair `(A(1,X), B(1,X))`. Diagonal substitution becomes
`(A,B) ↦ A + X * B`, and multiplication by `uw - vs` becomes
`p ↦ (-X * p, p)`.

The identities here hold over every commutative ring. They include the fixed
quotient/kernel coordinates and the monomial identities underlying the
simultaneous triangularization in Section 5.1 of *Matrix Multiplication via
Auxiliary Separation and Polynomial Multiplication*.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantKernel

open Polynomial

variable {R : Type*} [CommRing R]

/-- Affine representatives of forms linear in the second pair of variables. -/
abbrev FormPair (R : Type*) [CommRing R] := R[X] × R[X]

/-- Substitute the first variable pair into the second variable pair. -/
def diagonal : FormPair R →ₗ[R] R[X] where
  toFun p := p.1 + X * p.2
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, mul_add]; ring
  map_smul' c p := by simp [smul_eq_C_mul]; ring

/-- Multiplication by `D = uw - vs` after putting `u = 1`. -/
def determinant : R[X] →ₗ[R] FormPair R where
  toFun p := (-X * p, p)
  map_add' p q := by apply Prod.ext <;> simp [mul_add]
  map_smul' c p := by
    apply Prod.ext <;> simp [smul_eq_C_mul]
    ring

@[simp] theorem diagonal_apply (p : FormPair R) : diagonal p = p.1 + X * p.2 := rfl

@[simp] theorem determinant_apply (p : R[X]) : determinant p = (-X * p, p) := rfl

@[simp] theorem diagonal_determinant (p : R[X]) : diagonal (determinant p) = 0 := by
  simp [diagonal, determinant]

/-- The determinant factor can be recovered from the second component. -/
theorem determinant_injective : Function.Injective (determinant (R := R)) := by
  intro p q h
  exact congrArg Prod.snd h

/-- Vanishing after diagonal substitution is exactly divisibility by `uw - vs`. -/
theorem diagonal_eq_zero_iff (p : FormPair R) :
    diagonal p = 0 ↔ p = determinant p.2 := by
  constructor
  · intro h
    apply Prod.ext
    · change p.1 = -X * p.2
      have h' : p.1 + X * p.2 = 0 := h
      linear_combination h'
    · rfl
  · intro h
    rw [h]
    exact diagonal_determinant _

/-- The kernel parametrization does not require any field or domain hypothesis. -/
theorem mem_kernel_iff (p : FormPair R) :
    p ∈ LinearMap.ker diagonal ↔ ∃ q, determinant q = p := by
  rw [LinearMap.mem_ker, diagonal_eq_zero_iff]
  constructor
  · intro h
    exact ⟨p.2, h.symm⟩
  · rintro ⟨q, rfl⟩
    rfl

theorem kernel_eq_range : LinearMap.ker (diagonal (R := R)) = LinearMap.range determinant := by
  ext p
  exact mem_kernel_iff p

/-- A fixed linear complement to the determinant kernel on unrestricted polynomials. -/
def split : (R[X] × R[X]) ≃ₗ[R] FormPair R where
  toFun p := (p.1 - X * p.2, p.2)
  invFun p := (p.1 + X * p.2, p.2)
  left_inv p := by apply Prod.ext <;> simp
  right_inv p := by apply Prod.ext <;> simp
  map_add' p q := by
    apply Prod.ext <;> simp
    ring
  map_smul' c p := by
    apply Prod.ext <;> simp [smul_eq_C_mul]
    ring

@[simp] theorem split_apply (p : R[X] × R[X]) : split p = (p.1 - X * p.2, p.2) := rfl

@[simp] theorem split_symm_apply (p : FormPair R) : split.symm p = (diagonal p, p.2) := rfl

@[simp] theorem diagonal_split (p : R[X] × R[X]) : diagonal (split p) = p.1 := by
  simp [split, diagonal]

@[simp] theorem split_zero_left (q : R[X]) : split (0, q) = determinant q := by
  simp [split, determinant]

theorem diagonal_surjective : Function.Surjective (diagonal (R := R)) := by
  intro p
  exact ⟨(p, 0), by simp⟩

/-- The kernel is canonically isomorphic to one polynomial copy. -/
def kernelEquiv : R[X] ≃ₗ[R] LinearMap.ker (diagonal (R := R)) where
  toFun p := ⟨determinant p, by simp⟩
  invFun p := p.1.2
  left_inv p := rfl
  right_inv p := by
    apply Subtype.ext
    exact ((diagonal_eq_zero_iff p.1).mp p.2).symm
  map_add' p q := by apply Subtype.ext; exact map_add determinant p q
  map_smul' c p := by apply Subtype.ext; exact map_smul determinant c p

/-- Multiply both coefficients by a first-input polynomial. -/
def multiply (f : R[X]) : FormPair R →ₗ[R] FormPair R where
  toFun p := (f * p.1, f * p.2)
  map_add' p q := by apply Prod.ext <;> simp [mul_add]
  map_smul' c p := by apply Prod.ext <;> simp [smul_eq_C_mul] <;> ring

@[simp] theorem multiply_apply (f : R[X]) (p : FormPair R) :
    multiply f p = (f * p.1, f * p.2) := rfl

/-- The quotient action is ordinary polynomial multiplication. -/
theorem diagonal_multiply (f : R[X]) (p : FormPair R) :
    diagonal (multiply f p) = f * diagonal p := by
  simp [diagonal, multiply]
  ring

/-- The kernel action is ordinary polynomial multiplication with the same first input. -/
theorem multiply_determinant (f p : R[X]) :
    multiply f (determinant p) = determinant (f * p) := by
  apply Prod.ext <;> simp [multiply, determinant]
  ring

/-- Every first-input slice preserves the determinant kernel. -/
theorem multiply_mem_kernel (f : R[X]) {p : FormPair R}
    (hp : p ∈ LinearMap.ker diagonal) : multiply f p ∈ LinearMap.ker diagonal := by
  rw [LinearMap.mem_ker, diagonal_multiply, LinearMap.mem_ker.mp hp, mul_zero]

/-- Quotient and kernel coordinates transform simultaneously, with an unchanged first input. -/
theorem split_multiply (f : R[X]) (p : R[X] × R[X]) :
    multiply f (split p) = split (f * p.1, f * p.2) := by
  apply Prod.ext <;> simp [multiply, split]
  ring

/-- The ordinary quotient monomial `u^(e-j) v^j s`, with `j ≤ e`. -/
def quotientMonomial (j : ℕ) : FormPair R := (X ^ j, 0)

/-- The last quotient monomial `v^e w`. -/
def quotientTop (e : ℕ) : FormPair R := (0, X ^ e)

/-- The kernel monomial `(uw-vs) u^(e-1-j) v^j`, with `j < e`. -/
def kernelMonomial (j : ℕ) : FormPair R := determinant (X ^ j)

@[simp] theorem diagonal_quotientMonomial (j : ℕ) :
    diagonal (quotientMonomial (R := R) j) = X ^ j := by
  simp [diagonal, quotientMonomial]

@[simp] theorem diagonal_quotientTop (e : ℕ) :
    diagonal (quotientTop (R := R) e) = X ^ (e + 1) := by
  simp [diagonal, quotientTop, pow_succ, mul_comm]

@[simp] theorem diagonal_kernelMonomial (j : ℕ) :
    diagonal (kernelMonomial (R := R) j) = 0 := by
  simp [kernelMonomial]

@[simp] theorem multiply_quotientMonomial (i j : ℕ) :
    multiply (X ^ i) (quotientMonomial (R := R) j) = quotientMonomial (i + j) := by
  apply Prod.ext <;> simp [multiply, quotientMonomial, pow_add]

@[simp] theorem multiply_kernelMonomial (i j : ℕ) :
    multiply (X ^ i) (kernelMonomial (R := R) j) = kernelMonomial (i + j) := by
  rw [kernelMonomial, multiply_determinant, ← pow_add, kernelMonomial]

/-- The sole cross term in a nonfinal first-input slice has coefficient one. -/
theorem multiply_quotientTop_cross (i e : ℕ) :
    multiply (X ^ i) (quotientTop (R := R) e) =
      quotientMonomial (i + e + 1) + kernelMonomial (i + e) := by
  apply Prod.ext <;> simp [multiply, quotientTop, quotientMonomial, kernelMonomial, determinant,
    pow_add, pow_succ]
  ring

/-- For the final first-input monomial the last quotient vector remains the last vector. -/
theorem multiply_quotientTop_last (d e : ℕ) :
    multiply (X ^ d) (quotientTop (R := R) e) = quotientTop (d + e) := by
  apply Prod.ext <;> simp [multiply, quotientTop, pow_add]

/-- The actual quotient vectors used at degree `e`: there are `e + 2` of them. -/
def quotientVector (e : ℕ) (j : Fin (e + 2)) : FormPair R :=
  if (j : ℕ) < e + 1 then quotientMonomial j else quotientTop e

/-- The actual kernel vectors used at degree `e`: there are `e` of them. -/
def kernelVector (_e : ℕ) (j : Fin _e) : FormPair R := kernelMonomial j

@[simp] theorem diagonal_quotientVector (e : ℕ) (j : Fin (e + 2)) :
    diagonal (quotientVector (R := R) e j) = X ^ (j : ℕ) := by
  unfold quotientVector
  split_ifs with h
  · exact diagonal_quotientMonomial j
  · have hj : (j : ℕ) = e + 1 := by omega
    simpa [hj] using diagonal_quotientTop (R := R) e

@[simp] theorem diagonal_kernelVector (e : ℕ) (j : Fin e) :
    diagonal (kernelVector (R := R) e j) = 0 := by
  exact diagonal_kernelMonomial j

/-- Ordinary quotient columns have no kernel correction in the adapted output basis. -/
theorem multiply_quotientVector_ordinary (d e i j : ℕ)
    (hi : i ≤ d) (hj : j ≤ e) :
    multiply (X ^ i) (quotientVector (R := R) e ⟨j, by omega⟩) =
      quotientVector (d + e) ⟨i + j, by omega⟩ := by
  simp only [quotientVector, show j < e + 1 by omega,
    show i + j < d + e + 1 by omega, ↓reduceIte]
  exact multiply_quotientMonomial i j

/-- Nonfinal slices have exactly the quotient-top cross term described in Section 5.1. -/
theorem multiply_quotientVector_top_cross (d e i : ℕ) (hi : i < d) :
    multiply (X ^ i) (quotientVector (R := R) e ⟨e + 1, by omega⟩) =
      quotientVector (d + e) ⟨e + 1 + i, by omega⟩ +
        kernelVector (d + e) ⟨e + i, by omega⟩ := by
  simp only [quotientVector, lt_self_iff_false, ↓reduceIte,
    show e + 1 + i < d + e + 1 by omega, kernelVector]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    multiply_quotientTop_cross (R := R) i e

/-- The final slice has no cross term. -/
theorem multiply_quotientVector_top_last (d e : ℕ) :
    multiply (X ^ d) (quotientVector (R := R) e ⟨e + 1, by omega⟩) =
      quotientVector (d + e) ⟨d + e + 1, by omega⟩ := by
  simp only [quotientVector, lt_self_iff_false, ↓reduceIte]
  exact multiply_quotientTop_last d e

/-- All kernel columns have the convolution indices of the smaller branch. -/
theorem multiply_kernelVector (d e i j : ℕ) (hi : i ≤ d) (hj : j < e) :
    multiply (X ^ i) (kernelVector (R := R) e ⟨j, hj⟩) =
      kernelVector (d + e) ⟨i + j, by omega⟩ := by
  exact multiply_kernelMonomial i j


/-- Distinct bounded powers of `X` are independent even when the coefficient ring
has zero divisors. -/
theorem monomials_linearIndependent (n : ℕ) :
    LinearIndependent R (fun i : Fin n => (X : R[X]) ^ (i : ℕ)) := by
  have h := (Polynomial.degreeLT.basis R n).linearIndependent.map'
    (Polynomial.degreeLT R n).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  simpa only [Function.comp_def, Submodule.subtype_apply, Polynomial.degreeLT.basis_val] using h

/-- The quotient vectors followed by the kernel vectors are linearly independent.
This establishes nonsingularity of the simultaneous change of coordinates,
without any genericity assumption on the first input. -/
theorem adaptedVectors_linearIndependent (e : ℕ) :
    LinearIndependent R (Sum.elim (quotientVector (R := R) e) (kernelVector e)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hq : ∑ i : Fin (e + 2), c (Sum.inl i) • (X : R[X]) ^ (i : ℕ) = 0 := by
    have h := congrArg (diagonal (R := R)) hc
    simpa only [Fintype.sum_sum_type, map_add, map_sum, map_smul,
      Sum.elim_inl, Sum.elim_inr, diagonal_quotientVector, diagonal_kernelVector,
      smul_zero, Finset.sum_const_zero, add_zero, map_zero] using h
  have cq : ∀ i : Fin (e + 2), c (Sum.inl i) = 0 :=
    (Fintype.linearIndependent_iff.mp (monomials_linearIndependent (R := R) (e + 2))) _ hq
  have hk : ∑ i : Fin e, c (Sum.inr i) • (X : R[X]) ^ (i : ℕ) = 0 := by
    have h := congrArg Prod.snd hc
    simpa only [Fintype.sum_sum_type, Prod.snd_add, Prod.snd_sum,
      Sum.elim_inl, Sum.elim_inr, cq, zero_smul, Finset.sum_const_zero, zero_add,
      kernelVector, kernelMonomial, determinant_apply, Prod.snd_zero, Prod.smul_mk] using h
  have ck : ∀ i : Fin e, c (Sum.inr i) = 0 :=
    (Fintype.linearIndependent_iff.mp (monomials_linearIndependent (R := R) e)) _ hk
  exact Sum.rec cq ck

end MatrixMultiplication.AuxiliarySeparation.DeterminantKernel

end

end OAI

end Module1


section Module2
namespace OAI

/-!
# The finite adapted basis for the determinant filtration

The quotient vectors and determinant-kernel vectors of Section 5.1 form a basis
of the actual space of bidegree `(e,1)` forms. The proof works over every field,
including in the boundary case `e = 0` where the kernel has dimension zero.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantBasis

open Polynomial

variable {R : Type*} [CommRing R]

/-- Affine coefficient pairs of forms of bidegree `(e,1)`. -/
abbrev BoundedPair (R : Type*) [CommRing R] (e : ℕ) :=
  degreeLT R (e + 1) × degreeLT R (e + 1)

/-- Forget the degree bounds in the affine representation of binary forms. -/
def forget (e : ℕ) : BoundedPair R e →ₗ[R] DeterminantKernel.FormPair R where
  toFun p := ((p.1 : R[X]), (p.2 : R[X]))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem forget_injective (e : ℕ) : Function.Injective (forget (R := R) e) := by
  intro p q h
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- A quotient vector with both coefficient polynomials of degree at most `e`. -/
def quotientVector (e : ℕ) (j : Fin (e + 2)) : BoundedPair R e :=
  if h : (j : ℕ) < e + 1 then
    (⟨X ^ (j : ℕ), mem_degreeLT.mpr ((degree_X_pow_le _).trans_lt (by exact_mod_cast h))⟩, 0)
  else
    (0, ⟨X ^ e, mem_degreeLT.mpr ((degree_X_pow_le _).trans_lt (by exact_mod_cast Nat.lt_succ_self e))⟩)

/-- A bounded kernel vector, obtained by multiplication by `uw-vs`. -/
def kernelVector (e : ℕ) (j : Fin e) : BoundedPair R e :=
  (⟨-(X ^ ((j : ℕ) + 1)), mem_degreeLT.mpr <| by
      rw [degree_neg]
      exact (degree_X_pow_le _).trans_lt (by exact_mod_cast (show (j : ℕ) + 1 < e + 1 by omega))⟩,
   ⟨X ^ (j : ℕ), mem_degreeLT.mpr <|
      (degree_X_pow_le _).trans_lt (by exact_mod_cast (show (j : ℕ) < e + 1 by omega))⟩)

/-- The quotient vectors first, followed by the determinant-kernel vectors. -/
def vector (e : ℕ) : (Fin (e + 2) ⊕ Fin e) → BoundedPair R e :=
  Sum.elim (quotientVector e) (kernelVector e)

@[simp] theorem forget_quotientVector (e : ℕ) (j : Fin (e + 2)) :
    forget e (quotientVector (R := R) e j) = DeterminantKernel.quotientVector e j := by
  unfold quotientVector DeterminantKernel.quotientVector
  split_ifs <;> rfl

@[simp] theorem forget_kernelVector (e : ℕ) (j : Fin e) :
    forget e (kernelVector (R := R) e j) = DeterminantKernel.kernelVector e j := by
  apply Prod.ext
  · change -(X ^ ((j : ℕ) + 1)) = -X * X ^ (j : ℕ)
    rw [pow_succ, mul_comm, neg_mul]
  · rfl

@[simp] theorem forget_vector (e : ℕ) (j : Fin (e + 2) ⊕ Fin e) :
    forget e (vector (R := R) e j) =
      Sum.elim (DeterminantKernel.quotientVector e) (DeterminantKernel.kernelVector e) j := by
  cases j <;> simp [vector]

/-- Linear independence holds over a general commutative coefficient ring. -/
theorem vector_linearIndependent (e : ℕ) : LinearIndependent R (vector (R := R) e) := by
  apply LinearIndependent.of_comp (forget e)
  simpa only [Function.comp_def, forget_vector] using
    DeterminantKernel.adaptedVectors_linearIndependent (R := R) e

/-- The dimension of the original space of forms is twice `e+1`. -/
theorem finrank_boundedPair (K : Type*) [Field K] (e : ℕ) :
    Module.finrank K (BoundedPair K e) = 2 * (e + 1) := by
  have h : Module.finrank K (degreeLT K (e + 1)) = e + 1 := by
    simpa using Module.finrank_eq_card_basis (degreeLT.basis K (e + 1))
  rw [Module.finrank_prod, h]
  omega

/-- The fixed simultaneous change of basis used in the determinant degeneration. -/
def basis (K : Type*) [Field K] (e : ℕ) :
    Module.Basis (Fin (e + 2) ⊕ Fin e) K (BoundedPair K e) :=
  basisOfLinearIndependentOfCardEqFinrank (vector_linearIndependent e) (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_boundedPair]
    omega)

@[simp] theorem basis_apply (K : Type*) [Field K] (e : ℕ)
    (j : Fin (e + 2) ⊕ Fin e) : basis K e j = vector e j := by
  rw [basis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- Forgetting degree bounds identifies the finite basis with the explicit
polynomial-pair formulas. -/
@[simp] theorem forget_basis (K : Type*) [Field K] (e : ℕ)
    (j : Fin (e + 2) ⊕ Fin e) :
    forget e (basis K e j) =
      Sum.elim (DeterminantKernel.quotientVector e) (DeterminantKernel.kernelVector e) j := by
  rw [basis_apply, forget_vector]

end MatrixMultiplication.AuxiliarySeparation.DeterminantBasis

end

end OAI

end Module2



end AllFieldsModule14
/- END all-fields module GenericDeterminantCore -/

/- BEGIN all-fields module GenericDeterminantFiltration -/
section AllFieldsModule15
set_option autoImplicit false
namespace OAI
variable {K : Type*} [Field K]

/-!
# The finite determinant filtration of polynomial multiplication

The first leg is kept fixed throughout. The second and third legs use the
explicit quotient/kernel vectors of `DeterminantKernel`. The coefficient
identity `adaptedTensor_reconstruct` verifies the actual multiplication on
every basis input; it does not assume a simultaneous triangularization.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation Polynomial

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

abbrev Index (e : ℕ) := Sum (Fin (e + 2)) (Fin e)

/-- The ordered quotient/kernel vectors in the actual polynomial pair space. -/
def vector (e : ℕ) : Index e → DeterminantKernel.FormPair K :=
  Sum.elim (DeterminantKernel.quotientVector e) (DeterminantKernel.kernelVector e)

/-- All multiplication coefficients in the explicit adapted bases.
Here `a=d+1`, `b=e+1`, and no first-leg change of coordinates occurs. -/
def adaptedTensor (d e : ℕ) : Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inl j, .inr k =>
      if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

/-- The associated graded tensor, whose two branches still share the first leg. -/
def gradedTensor (d e : ℕ) : Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | _, .inl _, .inr _ => 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

private theorem sum_coordinate {n r : ℕ} (hr : r < n)
    (v : Fin n → DeterminantKernel.FormPair K) :
    (∑ k : Fin n, (if r = k.val then (1 : K) else 0) • v k) = v ⟨r, hr⟩ := by
  have h (k : Fin n) : r = k.val ↔ k = ⟨r, hr⟩ := by
    constructor
    · intro hk
      apply Fin.ext
      exact hk.symm
    · intro hk
      exact congrArg Fin.val hk.symm
  simp_rw [h]
  simp

/-- Exact coordinate reconstruction of every first-leg slice, in common bases. -/
theorem adaptedTensor_reconstruct (d e : ℕ) (i : Fin (d + 1)) (j : Index e) :
    (∑ k : Index (d + e), adaptedTensor (K := K) d e i j k • vector (K := K) (d + e) k) =
      DeterminantKernel.multiply (X ^ i.val) (vector (K := K) e j) := by
  have hi : i.val ≤ d := by omega
  rcases j with j | j
  · by_cases hj : j.val ≤ e
    · have hn : j.val ≠ e + 1 := by omega
      simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
        Sum.elim_inr, hn, false_and, ↓reduceIte, zero_smul, Finset.sum_const_zero,
        add_zero]
      rw [sum_coordinate (by omega)]
      exact (DeterminantKernel.multiply_quotientVector_ordinary d e i.val j.val hi hj).symm
    · have hj' : j.val = e + 1 := by omega
      have hjfin : j = ⟨e + 1, by omega⟩ := Fin.ext hj'
      rw [hjfin]
      by_cases hi' : i.val < d
      · simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
          Sum.elim_inr, hi', true_and]
        rw [sum_coordinate (by omega), sum_coordinate (by omega)]
        have h := DeterminantKernel.multiply_quotientVector_top_cross
          (R := K) d e i.val hi'
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
      · have hi'' : i.val = d := by omega
        simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
          Sum.elim_inr, hi', and_false, false_and, ↓reduceIte, zero_smul,
          Finset.sum_const_zero, add_zero]
        rw [sum_coordinate (by omega)]
        have h := DeterminantKernel.multiply_quotientVector_top_last (R := K) d e
        simpa only [hi'', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
  · simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
      Sum.elim_inr, zero_smul, Finset.sum_const_zero, zero_add]
    rw [sum_coordinate (by omega)]
    exact (DeterminantKernel.multiply_kernelVector d e i.val j.val hi j.isLt).symm

/-- The reconstruction uniquely determines every tensor coefficient. -/
theorem adaptedTensor_unique (d e : ℕ)
    (T : Tensor K (Fin (d + 1)) (Index e) (Index (d + e)))
    (hT : ∀ i j, (∑ k, T i j k • vector (K := K) (d + e) k) =
      DeterminantKernel.multiply (X ^ i.val) (vector (K := K) e j)) :
    T = adaptedTensor (K := K) d e := by
  funext i j k
  have h := (DeterminantKernel.adaptedVectors_linearIndependent (R := K) (d + e))
  have hs : ∑ z, (T i j z - adaptedTensor (K := K) d e i j z) • vector (K := K) (d + e) z = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hT, adaptedTensor_reconstruct, sub_self]
  exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp h) _ hs k)

/-- The quotient branch is exactly `C(a,b+1)`. -/
theorem gradedTensor_quotient (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 2)) (k : Fin (d + e + 2)) :
    gradedTensor (K := K) d e i (.inl j) (.inl k) =
      convolution (d + 1) (e + 2) i j (Fin.cast (by omega) k) := by
  simp only [gradedTensor, convolution, Fin.val_cast]
  rfl

/-- The kernel branch is exactly `C(a,b-1)`. -/
theorem gradedTensor_kernel (d e : ℕ) (i : Fin (d + 1))
    (j : Fin e) (k : Fin (d + e)) :
    gradedTensor (K := K) d e i (.inr j) (.inr k) =
      convolution (d + 1) e i j (Fin.cast (by omega) k) := by
  simp only [gradedTensor, convolution, Fin.val_cast]
  rfl

@[simp] theorem adaptedTensor_kernel_to_quotient (d e : ℕ)
    (i : Fin (d + 1)) (j : Fin e) (k : Fin (d + e + 2)) :
    adaptedTensor (K := K) d e i (.inr j) (.inl k) = 0 := rfl

/-- Polynomial diagonal maps; scaling the quotient input by `X` clears
the negative input-kernel weight without changing the leading tensor. -/
def inputScale (e : ℕ) : Index e → K[X]
  | .inl _ => X
  | .inr _ => 1

def outputScale (e : ℕ) : Index e → K[X]
  | .inl _ => 1
  | .inr _ => X

def diagonalMap {I : Type*} [DecidableEq I] (s : I → K[X]) : I → I → K[X] :=
  fun i j => if i = j then s i else 0

private theorem restrict_diagonal {I J JZ : Type*}
    [Fintype I] [Fintype J] [Fintype JZ]
    [DecidableEq I] [DecidableEq J] [DecidableEq JZ]
    (a : I → K[X]) (b : J → K[X]) (c : JZ → K[X])
    (T : Tensor K[X] I J JZ) (i : I) (j : J) (k : JZ) :
    Tensor.restrict (diagonalMap (K := K) a) (diagonalMap (K := K) b) (diagonalMap (K := K) c) T i j k =
      a i * b j * c k * T i j k := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

/-- A checked polynomial degeneration (K := K) to the two matched convolution (K := K) branches. -/
def degeneration (d e : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (adaptedTensor (K := K) d e)
      (gradedTensor (K := K) d e) 1 0 1 1 where
  leftMap := diagonalMap (K := K) (fun _ => 1)
  middleMap := diagonalMap (K := K) (inputScale (K := K) e)
  rightMap := diagonalMap (K := K) (outputScale (K := K) (d + e))
  left_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs <;> simp
  middle_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs
    · cases i <;> simp [inputScale]
    · simp
  right_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs
    · cases i <;> simp [outputScale]
    · simp
  vanishes := by
    intro i j k n hn
    have hn' : n = 0 := by omega
    rw [restrict_diagonal]
    rcases j with j | j <;> rcases k with k | k
    all_goals simp only [inputScale, outputScale, adaptedTensor, one_mul]
    all_goals (try split_ifs) <;> simp [hn', ← pow_two]
  leading := by
    intro i j k
    rw [restrict_diagonal]
    rcases j with j | j <;> rcases k with k | k
    all_goals simp only [inputScale, outputScale, adaptedTensor, gradedTensor, one_mul]
    all_goals (try split_ifs) <;> simp [← pow_two]

/-! The actual coordinate change from the original two-copy convolution. -/

abbrev OriginalIndex (e : ℕ) := Sum (Fin (e + 1)) (Fin (e + 1))

/-- The original monomial bases in the `s` and `w` components. -/
def originalBasis (e : ℕ) :
    Module.Basis (OriginalIndex e) K (DeterminantBasis.BoundedPair K e) :=
  (Polynomial.degreeLT.basis K (e + 1)).prod (Polynomial.degreeLT.basis K (e + 1))

private theorem degree_shift_lt (d e : ℕ) (i : Fin (d + 1))
    (p : Polynomial.degreeLT K (e + 1)) :
    ((X : K[X]) ^ i.val * (p : K[X])).degree < (d + e + 1 : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · have hp := Polynomial.mem_degreeLT.mp p.2
    rw [Polynomial.degree_lt_iff_coeff_zero] at hp
    exact hp (n - i.val) (by have hi := i.isLt; omega)
  · rfl

/-- Multiplication by a fixed first-input monomial between the bounded spaces. -/
def boundedShift (d e : ℕ) (i : Fin (d + 1)) :
    Polynomial.degreeLT K (e + 1) →ₗ[K] Polynomial.degreeLT K (d + e + 1) where
  toFun p := ⟨X ^ i.val * (p : K[X]), Polynomial.mem_degreeLT.mpr (degree_shift_lt d e i p)⟩
  map_add' p q := by apply Subtype.ext; simp [mul_add]
  map_smul' c p := by apply Subtype.ext; simp [Polynomial.smul_eq_C_mul]; ring

/-- The same first monomial multiplies both components. -/
def boundedMultiply (d e : ℕ) (i : Fin (d + 1)) :
    DeterminantBasis.BoundedPair K e →ₗ[K] DeterminantBasis.BoundedPair K (d + e) :=
  (boundedShift (K := K) d e i).prodMap (boundedShift (K := K) d e i)

@[simp] theorem forget_boundedMultiply (d e : ℕ) (i : Fin (d + 1))
    (p : DeterminantBasis.BoundedPair K e) :
    DeterminantBasis.forget (d + e) (boundedMultiply (K := K) d e i p) =
      DeterminantKernel.multiply (X ^ i.val) (DeterminantBasis.forget e p) := rfl

/-- Polynomial multiplication in its original monomial coordinates. -/
def sourceTensor (d e : ℕ) :
    Tensor K (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e)) :=
  fun i j k => (originalBasis (K := K) (d + e)).repr
    (boundedMultiply (K := K) d e i (originalBasis (K := K) e j)) k

@[simp] theorem sourceTensor_inl_inl (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor (K := K) d e i (.inl j) (.inl k) =
      convolution (d + 1) (e + 1) i j (Fin.cast (by omega) k) := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift,
    ← pow_add, convolution, eq_comm]

@[simp] theorem sourceTensor_inr_inr (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor (K := K) d e i (.inr j) (.inr k) =
      convolution (d + 1) (e + 1) i j (Fin.cast (by omega) k) := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift,
    ← pow_add, convolution, eq_comm]

@[simp] theorem sourceTensor_inl_inr (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor (K := K) d e i (.inl j) (.inr k) = 0 := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift]

@[simp] theorem sourceTensor_inr_inl (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor (K := K) d e i (.inr j) (.inl k) = 0 := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift]

/-- Record the polynomial coordinate and the choice of `s` or `w` separately. -/
def originalCoordinate (e : ℕ) : OriginalIndex e → Fin (e + 1) × Bool
  | .inl j => (j, false)
  | .inr j => (j, true)

/-- The source is exactly polynomial convolution (K := K) tensored with a two-coordinate
dot product whose singleton is on the unchanged first leg. -/
theorem sourceTensor_product (d e : ℕ) :
    sourceTensor (K := K) d e =
      Tensor.pullback (fun i : Fin (d + 1) => (i, ())) (originalCoordinate e)
        (fun k => (Fin.cast (by omega) (originalCoordinate (d + e) k).1,
          (originalCoordinate (d + e) k).2))
        (Tensor.product (convolution (d + 1) (e + 1))
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))) := by
  funext i j k
  rcases j with j | j <;> rcases k with k | k <;>
    simp [Tensor.pullback, Tensor.product, Tensor.cyclic, Tensor.dotPairing,
      originalCoordinate]

/-- The input matrix has adapted vectors as columns in the original basis. -/
def inputChange (e : ℕ) (j : Index e) (old : OriginalIndex e) : K :=
  (originalBasis (K := K) e).repr (DeterminantBasis.basis K e j) old

/-- The output-dual matrix uses the inverse basis change, as required for tensors. -/
def outputDualChange (e : ℕ) (k : Index e) (old : OriginalIndex e) : K :=
  (DeterminantBasis.basis K e).repr (originalBasis (K := K) e old) k

/-- The first input is unchanged, including throughout the basis change. -/
def fixedFirst (d : ℕ) (i j : Fin (d + 1)) : K := if i = j then 1 else 0

private theorem restrict_fixedFirst (d e : ℕ)
    (B : Index e → OriginalIndex e → K)
    (C : Index (d + e) → OriginalIndex (d + e) → K)
    (T : Tensor K (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e)))
    (i : Fin (d + 1)) (j : Index e) (k : Index (d + e)) :
    Tensor.restrict (fixedFirst (K := K) d) B C T i j k =
      ∑ y, ∑ z, B j y * C k z * T i y z := by
  simp [Tensor.restrict, fixedFirst, ite_mul]

theorem boundedMultiply_adapted_coordinates (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    (DeterminantBasis.basis K (d + e)).repr
      (boundedMultiply (K := K) d e i (DeterminantBasis.basis K e j)) k =
      adaptedTensor (K := K) d e i j k := by
  have h := adaptedTensor_unique d e
    (fun i j k => (DeterminantBasis.basis K (d + e)).repr
      (boundedMultiply (K := K) d e i (DeterminantBasis.basis K e j)) k) ?_
  · exact congrFun (congrFun (congrFun h i) j) k
  · intro i j
    have hsum := congrArg (DeterminantBasis.forget (R := K) (d + e))
      ((DeterminantBasis.basis K (d + e)).sum_repr
        (boundedMultiply (K := K) d e i (DeterminantBasis.basis K e j)))
    simpa only [map_sum, map_smul, DeterminantBasis.forget_basis,
      forget_boundedMultiply, vector] using hsum

/-- A concrete restriction, with the identity first map, changes the original
two-copy convolution (K := K) into the simultaneously triangular coefficient tensor. -/
theorem sourceTensor_coordinate_change (d e : ℕ) :
    Tensor.restrict (fixedFirst (K := K) d) (inputChange (K := K) e) (outputDualChange (K := K) (d + e))
      (sourceTensor (K := K) d e) = adaptedTensor (K := K) d e := by
  funext i j k
  rw [restrict_fixedFirst]
  simp only [inputChange, outputDualChange, sourceTensor]
  calc
    (∑ y, ∑ z,
        (originalBasis (K := K) e).repr (DeterminantBasis.basis K e j) y *
          (DeterminantBasis.basis K (d + e)).repr (originalBasis (K := K) (d + e) z) k *
          (originalBasis (K := K) (d + e)).repr (boundedMultiply (K := K) d e i (originalBasis (K := K) e y)) z) =
        ∑ y, (originalBasis (K := K) e).repr (DeterminantBasis.basis K e j) y *
          (DeterminantBasis.basis K (d + e)).repr
            (boundedMultiply (K := K) d e i (originalBasis (K := K) e y)) k := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      exact (DeterminantBasis.basis K (d + e)).sum_repr_mul_repr
        (originalBasis (K := K) (d + e)) _ k
    _ = (DeterminantBasis.basis K (d + e)).repr
          (boundedMultiply (K := K) d e i (DeterminantBasis.basis K e j)) k := by
      have hsum := congrArg (fun p => (DeterminantBasis.basis K (d + e)).repr
          (boundedMultiply (K := K) d e i p) k)
        ((originalBasis (K := K) e).sum_repr (DeterminantBasis.basis K e j))
      simpa only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
        smul_eq_mul] using hsum
    _ = adaptedTensor (K := K) d e i j k := boundedMultiply_adapted_coordinates d e i j k

end MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

end

end OAI



end AllFieldsModule15
/- END all-fields module GenericDeterminantFiltration -/

/- BEGIN all-fields module GenericFourier -/
section AllFieldsModule16

/-! Generic Fourier filters and characteristic-safe periods.
Adapted from the corresponding OAI complex Fourier proof. This file proves
only finite Fourier and period-selection lemmas, not a matrix multiplication bound.
-/

set_option autoImplicit false

namespace OAIAllFieldsFourier

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K]

lemma sum_pow_root_of_unity (z : K) (L : ℕ) (hz : z ^ L = 1) :
    (∑ r ∈ Finset.range L, z ^ r) = if z = 1 then (L : K) else 0 := by
  split_ifs with h
  · simp [h]
  · have hsum : (1 - z) * ∑ r ∈ Finset.range L, z ^ r = 0 := by
      rw [mul_neg_geom_sum, hz, sub_self]
    exact (mul_eq_zero.mp hsum).resolve_left (sub_ne_zero.mpr (Ne.symm h))

theorem sum_zpow_primitive_root {ζ : K} {L : ℕ}
    (hζ : IsPrimitiveRoot ζ L) (e : ℤ) :
    (∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e)) =
      if (L : ℤ) ∣ e then (L : K) else 0 := by
  have hpow : (ζ ^ e) ^ L = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow]
  have hterm (r : ℕ) : ζ ^ ((r : ℤ) * e) = (ζ ^ e) ^ r := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  simp_rw [hterm]
  rw [sum_pow_root_of_unity _ _ hpow]
  simp only [hζ.zpow_eq_one_iff_dvd]

theorem normalized_sum_zpow_primitive_root {ζ : K} {L : ℕ}
    (hL : (L : K) ≠ 0) (hζ : IsPrimitiveRoot ζ L) (e : ℤ) :
    (L : K)⁻¹ * (∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e)) =
      if (L : ℤ) ∣ e then 1 else 0 := by
  rw [sum_zpow_primitive_root hζ e]
  split_ifs <;> simp [hL]

theorem normalized_sum_zpow_primitive_root_of_abs_lt {ζ : K} {L : ℕ} {e : ℤ}
    (hL : (L : K) ≠ 0) (hζ : IsPrimitiveRoot ζ L) (he : |e| < (L : ℤ)) :
    (L : K)⁻¹ * (∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e)) =
      if e = 0 then 1 else 0 := by
  rw [normalized_sum_zpow_primitive_root hL hζ e]
  have hd : (L : ℤ) ∣ e ↔ e = 0 := by
    constructor
    · intro hd
      exact Int.eq_zero_of_abs_lt_dvd hd he
    · rintro rfl
      exact dvd_zero _
  simp only [hd]

/-- Two consecutive choices always include one nonzero scalar, in every field. -/
theorem exists_forward_period (K : Type*) [Field K] (M : ℕ) (hM : 0 < M) :
    ∃ L : ℕ, (L = 5 * M ∨ L = 5 * M + 1) ∧ (L : K) ≠ 0 ∧
      3 * (M - 1) < L ∧ L ≤ 6 * M := by
  by_cases h : ((5 * M : ℕ) : K) = 0
  · refine ⟨5 * M + 1, Or.inr rfl, ?_, by omega, by omega⟩
    simpa only [Nat.cast_add, Nat.cast_one, h, zero_add] using (one_ne_zero : (1 : K) ≠ 0)
  · exact ⟨5 * M, Or.inl rfl, h, by omega, by omega⟩

/-- Using the previous integer preserves the original upper bound of five M. -/
theorem exists_padded_period (K : Type*) [Field K] (M : ℕ) (hM : 0 < M) :
    ∃ L : ℕ, (L = 5 * M ∨ L = 5 * M - 1) ∧ (L : K) ≠ 0 ∧
      3 * (M - 1) < L ∧ L ≤ 5 * M := by
  by_cases h : ((5 * M : ℕ) : K) = 0
  · refine ⟨5 * M - 1, Or.inr rfl, ?_, by omega, by omega⟩
    have hc : ((5 * M - 1 : ℕ) : K) = -1 := by
      rw [Nat.cast_sub (show 1 ≤ 5 * M by omega), Nat.cast_one, h, zero_sub]
    rw [hc]
    exact neg_ne_zero.mpr one_ne_zero
  · exact ⟨5 * M, Or.inl rfl, h, by omega, by omega⟩

/-- Algebraic closure supplies a primitive root for the forward period. -/
theorem exists_forward_period_and_root (K : Type*) [Field K] [IsAlgClosed K]
    (M : ℕ) (hM : 0 < M) :
    ∃ (L : ℕ) (ζ : K), (L = 5 * M ∨ L = 5 * M + 1) ∧ (L : K) ≠ 0 ∧
      3 * (M - 1) < L ∧ L ≤ 6 * M ∧ IsPrimitiveRoot ζ L := by
  obtain ⟨L, hchoice, hL, hradius, hbound⟩ := exists_forward_period K M hM
  letI : NeZero (L : K) := ⟨hL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K L
  exact ⟨L, ζ, hchoice, hL, hradius, hbound, hζ⟩

/-- Algebraic closure supplies a primitive root without increasing the five M bound. -/
theorem exists_padded_period_and_root (K : Type*) [Field K] [IsAlgClosed K]
    (M : ℕ) (hM : 0 < M) :
    ∃ (L : ℕ) (ζ : K), (L = 5 * M ∨ L = 5 * M - 1) ∧ (L : K) ≠ 0 ∧
      3 * (M - 1) < L ∧ L ≤ 5 * M ∧ IsPrimitiveRoot ζ L := by
  obtain ⟨L, hchoice, hL, hradius, hbound⟩ := exists_padded_period K M hM
  letI : NeZero (L : K) := ⟨hL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K L
  exact ⟨L, ζ, hchoice, hL, hradius, hbound, hζ⟩


end OAIAllFieldsFourier


end AllFieldsModule16
/- END all-fields module GenericFourier -/

/- BEGIN all-fields module GenericFiniteProjection -/
section AllFieldsModule17

/-! OAI finite separation coefficients generalized to every field.
Integer square-weight lemmas are copied unchanged from the OAI source.
The Fourier period is any L with nonzero cast and sufficient phase radius.
-/
set_option autoImplicit false
namespace OAIAllFieldsSeparation
open scoped BigOperators
attribute [local instance] Classical.propDecidable
/-- The exponent occurring in the finite Fourier projection. -/
def phase (g h u v : ℤ) : ℤ := u - v + 2 * (g - h)

/-- Weight on the first tensor leg, which carries the guessed sector label. -/
def firstWeight (g : ℤ) : ℤ := g ^ 2

/-- Weight on the second tensor leg. -/
def secondWeight (h u : ℤ) : ℤ := h * u - h ^ 2

/-- Weight on the third tensor leg. -/
def thirdWeight (h v : ℤ) : ℤ := -(h * v)

/-- Total weight of a target monomial after the three independent substitutions. -/
def totalWeight (g h u v : ℤ) : ℤ :=
  firstWeight g + secondWeight h u + thirdWeight h v

theorem totalWeight_eq_square_add_phase (g h u v : ℤ) :
    totalWeight g h u v = (g - h) ^ 2 + h * phase g h u v := by
  unfold totalWeight firstWeight secondWeight thirdWeight phase
  ring

/-- The projection equation converts the total weight into a square. -/
theorem totalWeight_eq_sq_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalWeight g h u v = (g - h) ^ 2 := by
  rw [totalWeight_eq_square_add_phase, hphase, mul_zero, add_zero]

theorem totalWeight_nonneg_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) : 0 ≤ totalWeight g h u v := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase]
  exact sq_nonneg (g - h)

/-- On the Fourier support, precisely the correctly matched terms have weight zero. -/
theorem totalWeight_eq_zero_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalWeight g h u v = 0 ↔ g = h ∧ u = v := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase, sq_eq_zero_iff]
  constructor
  · intro hzero
    have hgh : g = h := sub_eq_zero.mp hzero
    refine ⟨hgh, ?_⟩
    unfold phase at hphase
    omega
  · rintro ⟨hgh, _⟩
    exact sub_eq_zero.mpr hgh

theorem phase_and_totalWeight_eq_zero_iff (g h u v : ℤ) :
    (phase g h u v = 0 ∧ totalWeight g h u v = 0) ↔ g = h ∧ u = v := by
  constructor
  · rintro ⟨hphase, hweight⟩
    exact (totalWeight_eq_zero_iff_of_phase_eq_zero hphase).mp hweight
  · rintro ⟨rfl, rfl⟩
    simp [phase, totalWeight, firstWeight, secondWeight, thirdWeight]

theorem totalWeight_pos_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    0 < totalWeight g h u v ↔ g ≠ h := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase, sq_pos_iff, sub_ne_zero]

/-- The degree bound in Section 4.3, for sector labels in `1, …, M`. -/
theorem totalWeight_le_of_labels {M g h u v : ℤ}
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hphase : phase g h u v = 0) :
    totalWeight g h u v ≤ (M - 1) ^ 2 := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase]
  have hprod : 0 ≤ ((M - 1) - (g - h)) * ((M - 1) + (g - h)) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- The polynomial degree attached to a surviving monomial. -/
def totalDegree (g h u v : ℤ) : ℕ := (totalWeight g h u v).toNat

theorem totalDegree_cast_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    (totalDegree g h u v : ℤ) = totalWeight g h u v := by
  exact Int.toNat_of_nonneg (totalWeight_nonneg_of_phase_eq_zero hphase)

theorem totalDegree_eq_zero_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalDegree g h u v = 0 ↔ g = h ∧ u = v := by
  have hcast := totalDegree_cast_of_phase_eq_zero hphase
  have hzero : totalDegree g h u v = 0 ↔ totalWeight g h u v = 0 := by omega
  exact hzero.trans (totalWeight_eq_zero_iff_of_phase_eq_zero hphase)

theorem totalDegree_le_of_labels {M : ℕ} {g h u v : ℤ}
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hphase : phase g h u v = 0) :
    totalDegree g h u v ≤ (M - 1) ^ 2 := by
  have hM : 1 ≤ M := by omega
  have hbound := totalWeight_le_of_labels hg hh hphase
  have hcast := totalDegree_cast_of_phase_eq_zero hphase
  have hsub : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
  exact_mod_cast (show (totalDegree g h u v : ℤ) ≤ ((M - 1 : ℕ) : ℤ) ^ 2 by
    rw [hcast, hsub]
    exact hbound)


variable {K : Type*} [Field K]

/-- A normalized finite Fourier average of one branch coefficient. -/
noncomputable def finiteFourierCoefficient (ζ : K) (L : ℕ) (e : ℤ) (c : K) : K :=
  (L : K)⁻¹ * ∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e) * c

/-- The Fourier average is a scalar support indicator, for every coefficient. -/
theorem finiteFourierCoefficient_eq_ite {ζ : K} {L : ℕ}
    (hL : (L : K) ≠ 0) (hζ : IsPrimitiveRoot ζ L) (e : ℤ) (c : K) :
    finiteFourierCoefficient ζ L e c = if (L : ℤ) ∣ e then c else 0 := by
  unfold finiteFourierCoefficient
  rw [← Finset.sum_mul, ← mul_assoc, OAIAllFieldsFourier.normalized_sum_zpow_primitive_root hL hζ]
  split_ifs <;> simp

/-- Averaging a finite family of branches agrees with averaging each branch. -/
theorem finiteFourierCoefficient_sum {ι : Type*} (s : Finset ι)
    (ζ : K) (L : ℕ) (e : ι → ℤ) (c : ι → K) :
    (L : K)⁻¹ * (∑ r ∈ Finset.range L, ∑ i ∈ s, ζ ^ ((r : ℤ) * e i) * c i) =
      ∑ i ∈ s, finiteFourierCoefficient ζ L (e i) (c i) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  rfl

/-- Any admissible period selects the exact integer support equation. -/
theorem admissibleFourierCoefficient_eq_ite {ζ : K} {M L : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : K) :
    finiteFourierCoefficient ζ L (phase g h u v) c =
      if phase g h u v = 0 then c else 0 := by
  have hb : |phase g h u v| ≤ 3 * ((M : ℤ) - 1) := by
    rw [abs_le']; unfold phase; constructor <;> omega
  have hsub : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
  have hc : (3 : ℤ) * ((M - 1 : ℕ) : ℤ) < (L : ℤ) := by exact_mod_cast hradius
  rw [hsub] at hc
  unfold finiteFourierCoefficient
  rw [← Finset.sum_mul, ← mul_assoc,
    OAIAllFieldsFourier.normalized_sum_zpow_primitive_root_of_abs_lt hL hζ (lt_of_le_of_lt hb hc)]
  split_ifs <;> simp

/-- A projected branch, recorded as an ordinary polynomial after Fourier averaging. -/
noncomputable def projectedBranchPolynomial (ζ : K) (L : ℕ)
    (g h u v : ℤ) (c : K) : Polynomial K :=
  Polynomial.monomial (totalDegree g h u v)
    (finiteFourierCoefficient ζ L (phase g h u v) c)

/-- The surviving polynomial weight is the square `(g - h)^2`. -/
theorem projectedBranchPolynomial_eq_ite {ζ : K} {M L : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : K) :
    projectedBranchPolynomial ζ L g h u v c =
      if phase g h u v = 0 then Polynomial.monomial ((g - h) ^ 2).toNat c else 0 := by
  unfold projectedBranchPolynomial
  rw [admissibleFourierCoefficient_eq_ite hM hL hradius hζ hg hh hu hv]
  split_ifs with hp
  · rw [totalDegree, totalWeight_eq_sq_of_phase_eq_zero hp]
  · simp

/-- A coefficient occurs exactly on the Fourier support at its integer total weight. -/
theorem projectedBranchPolynomial_coeff {ζ : K} {M L n : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : K) :
    (projectedBranchPolynomial ζ L g h u v c).coeff n =
      if phase g h u v = 0 ∧ totalWeight g h u v = (n : ℤ) then c else 0 := by
  unfold projectedBranchPolynomial
  rw [admissibleFourierCoefficient_eq_ite hM hL hradius hζ hg hh hu hv]
  by_cases hp : phase g h u v = 0
  · have hd : totalDegree g h u v = n ↔ totalWeight g h u v = (n : ℤ) := by
      have hcast := totalDegree_cast_of_phase_eq_zero hp
      omega
    simp only [hp, ↓reduceIte, Polynomial.coeff_monomial, hd, true_and]
  · simp [hp]

/-- Each projected branch has no polynomial coefficient above `(M - 1)^2`. -/
theorem projectedBranchPolynomial_coeff_eq_zero_of_lt
    {ζ : K} {M L n : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (hn : (M - 1) ^ 2 < n) (c : K) :
    (projectedBranchPolynomial ζ L g h u v c).coeff n = 0 := by
  unfold projectedBranchPolynomial
  rw [admissibleFourierCoefficient_eq_ite hM hL hradius hζ hg hh hu hv]
  split_ifs with hp
  · have hd := totalDegree_le_of_labels hg hh hp
    exact Polynomial.coeff_monomial_of_ne c (by omega)
  · simp

/-- Constant coefficient extraction is the exact square filter, with no restriction
on the original complex coefficient. -/
theorem projectedBranchPolynomial_coeff_zero {ζ : K} {M L : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : K) :
    (projectedBranchPolynomial ζ L g h u v c).coeff 0 =
      if g = h ∧ u = v then c else 0 := by
  unfold projectedBranchPolynomial
  rw [admissibleFourierCoefficient_eq_ite hM hL hradius hζ hg hh hu hv]
  by_cases hp : phase g h u v = 0
  · simp only [hp, ↓reduceIte, Polynomial.coeff_monomial,
      totalDegree_eq_zero_iff_of_phase_eq_zero hp]
  · have hlabels : ¬ (g = h ∧ u = v) := by
      rintro ⟨rfl, rfl⟩
      exact hp (by simp [phase])
    simp [hp, hlabels]

/-- Apply the finite Fourier projection and square weights branch by branch. -/
noncomputable def projectedPolynomial {ι : Type*} (s : Finset ι)
    (ζ : K) (L : ℕ) (g h u v : ι → ℤ) (c : ι → K) : Polynomial K :=
  ∑ i ∈ s, projectedBranchPolynomial ζ L (g i) (h i) (u i) (v i) (c i)

/-- Every coefficient of the projected polynomial has the exact integer support. -/
theorem projectedPolynomial_coeff {ι : Type*} (s : Finset ι)
    {ζ : K} {M L n : ℕ} (g h u v : ι → ℤ) (c : ι → K)
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ L g h u v c).coeff n =
      ∑ i ∈ s, if phase (g i) (h i) (u i) (v i) = 0 ∧
        totalWeight (g i) (h i) (u i) (v i) = (n : ℤ) then c i else 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  exact projectedBranchPolynomial_coeff hM hL hradius hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) (c i)

/-- Exact finite filtering for an arbitrary finite family of branch coefficients. -/
theorem projectedPolynomial_coeff_zero {ι : Type*} (s : Finset ι)
    {ζ : K} {M L : ℕ} (g h u v : ι → ℤ) (c : ι → K)
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ L g h u v c).coeff 0 =
      ∑ i ∈ s, if g i = h i ∧ u i = v i then c i else 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  exact projectedBranchPolynomial_coeff_zero hM hL hradius hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) (c i)

/-- The finite projected polynomial has support only in degrees at most `(M - 1)^2`. -/
theorem projectedPolynomial_coeff_eq_zero_of_lt {ι : Type*} (s : Finset ι)
    {ζ : K} {M L n : ℕ} (g h u v : ι → ℤ) (c : ι → K)
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M)
    (hn : (M - 1) ^ 2 < n) :
    (projectedPolynomial s ζ L g h u v c).coeff n = 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  exact projectedBranchPolynomial_coeff_eq_zero_of_lt hM hL hradius hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) hn (c i)

/-- The degree bound is independent of the number or values of the coefficients. -/
theorem projectedPolynomial_natDegree_le {ι : Type*} (s : Finset ι)
    {ζ : K} {M L : ℕ} (g h u v : ι → ℤ) (c : ι → K)
    (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ L g h u v c).natDegree ≤ (M - 1) ^ 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact projectedPolynomial_coeff_eq_zero_of_lt s g h u v c hM hL hradius hζ hg hh hu hv hn


end OAIAllFieldsSeparation


end AllFieldsModule17
/- END all-fields module GenericFiniteProjection -/

/- BEGIN all-fields module GenericSeparation -/
section AllFieldsModule18

/-! Explicit Fourier restriction and polynomial tensor over an arbitrary field.
The formulas and algebraic proofs are adapted from OAI Separation/Basic.lean;
period L has nonzero cast and exceeds the phase radius. No topology is used.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open OAI.MatrixMultiplication.Foundation
namespace OAIAllFieldsSeparation
variable {K : Type*} [Field K] {M L : ℕ} {X Y Z : Type*}

/-- The paper numbers sectors from one, while `Fin M` numbers them from zero. -/
def sectorNumber (i : Fin M) : ℤ := (i.val : ℤ) + 1

theorem sectorNumber_bounds (i : Fin M) :
    1 ≤ sectorNumber i ∧ sectorNumber i ≤ M := by
  have hi := i.isLt
  unfold sectorNumber
  omega

theorem sectorNumber_injective : Function.Injective (@sectorNumber M) := by
  intro i j hij
  apply Fin.ext
  unfold sectorNumber at hij
  omega

/-- Branches sharing X, with matching and disjoint Y and Z sectors. -/
def sharedFirstTensor (B : Fin M → Tensor K X Y Z) :
    Tensor K X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

/-- The first local Fourier substitution guesses the missing sector. -/
def firstProjectionMap (ζ : K) :
    (X × Fin M) → (Fin L × X) → K := by
  classical
  exact fun x r => if r.2 = x.1 then
    ζ ^ ((r.1.val : ℤ) * (2 * sectorNumber x.2)) else 0

/-- The second local map knows the sector through its original coordinate. -/
def secondProjectionMap (ζ : K) :
    ((Fin M × Y) × Fin M) → (Fin L × (Fin M × Y)) → K := by
  classical
  exact fun y r => if r.2 = y.1 then
    ζ ^ ((r.1.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) else 0

/-- The third local map carries the single Fourier normalization factor. -/
def thirdProjectionMap (ζ : K) :
    ((Fin M × Z) × Fin M) → (Fin L × (Fin M × Z)) → K := by
  classical
  exact fun z r => if r.2 = z.1 then
    (L : K)⁻¹ *
      ζ ^ ((r.1.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1)) else 0

private theorem restrict_constantCopies
    {K A B C A' B' C' R : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    (T : Tensor K A B C)
    (a : A' → R × A → K) (b : B' → R × B → K) (c : C' → R × C → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict a b c (Tensor.directSum (fun _ : R => T)) x y z =
      ∑ r : R, ∑ i, ∑ j, ∑ k, a x (r, i) * b y (r, j) * c z (r, k) * T i j k := by
  classical
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, mul_ite, ite_and]

private theorem restrict_constantCopies_delta
    {K A B C A' B' C' R : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Tensor K A B C) (fa : A' → A) (fb : B' → B) (fc : C' → C)
    (a : A' → R → K) (b : B' → R → K) (c : C' → R → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict
        (fun x r => if r.2 = fa x then a x r.1 else 0)
        (fun y r => if r.2 = fb y then b y r.1 else 0)
        (fun z r => if r.2 = fc z then c z r.1 else 0)
        (Tensor.directSum (fun _ : R => T)) x y z =
      (∑ r : R, a x r * b y r * c z r) * T (fa x) (fb y) (fc z) := by
  rw [restrict_constantCopies]
  simp [ite_mul, mul_ite, Finset.sum_mul]

/-- The exact coefficient tensor after Fourier projection, before weighting. -/
def projectedTensor (ζ : K) (B : Fin M → Tensor K X Y Z) :
    Tensor K (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if y.1.1 = z.1.1 then
    finiteFourierCoefficient ζ L
      (phase (sectorNumber x.2) (sectorNumber y.1.1)
        (sectorNumber y.2) (sectorNumber z.2)) (B y.1.1 x.1 y.1.2 z.1.2)
    else 0

/-- The chosen `L` copies and its three explicit local Fourier maps realize
the projected tensor by an ordinary restriction. -/
theorem finiteProjection_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (ζ : K) (hζ : ζ ≠ 0) (B : Fin M → Tensor K X Y Z) :
    Tensor.restrict (firstProjectionMap (L := L) ζ) (secondProjectionMap (L := L) ζ)
        (thirdProjectionMap (L := L) ζ)
        (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) =
      projectedTensor (L := L) ζ B := by
  classical
  funext x y z
  unfold firstProjectionMap secondProjectionMap thirdProjectionMap
  rw [restrict_constantCopies_delta (R := Fin L)
    (sharedFirstTensor B) Prod.fst Prod.fst Prod.fst
    (fun x r => ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)))
    (fun y r => ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)))
    (fun z r => (L : K)⁻¹ *
      ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1))) x y z]
  by_cases hyz : y.1.1 = z.1.1
  · simp only [sharedFirstTensor, projectedTensor, hyz, ↓reduceIte]
    have hterm (r : Fin L) :
        ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)) *
          ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) *
          ((L : K)⁻¹ *
            ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1))) =
        (L : K)⁻¹ *
          ζ ^ ((r.val : ℤ) * phase (sectorNumber x.2) (sectorNumber y.1.1)
            (sectorNumber y.2) (sectorNumber z.2)) := by
      rw [← hyz]
      calc
        _ = (L : K)⁻¹ *
            (ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)) *
            ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) *
            ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber y.1.1))) := by ring
        _ = (L : K)⁻¹ * ζ ^
            ((r.val : ℤ) * (2 * sectorNumber x.2) +
             (r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1) +
             (r.val : ℤ) * (-sectorNumber z.2 - sectorNumber y.1.1)) := by
          rw [zpow_add₀ hζ, zpow_add₀ hζ]
        _ = _ := by congr 2; unfold phase; ring
    simp only [← hyz] at hterm ⊢
    simp_rw [hterm]
    rw [← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun r : ℕ => ζ ^ ((r : ℤ) *
        phase (sectorNumber x.2) (sectorNumber y.1.1)
          (sectorNumber y.2) (sectorNumber z.2))) L]
    unfold finiteFourierCoefficient
    rw [← Finset.sum_mul]
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  · simp [sharedFirstTensor, projectedTensor, hyz]

/-- The polynomial after the Fourier projection and square weighting. -/
def separationPolynomial (ζ : K) (B : Fin M → Tensor K X Y Z) :
    Tensor (Polynomial K) (X × Fin M)
      ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if y.1.1 = z.1.1 then
    projectedBranchPolynomial ζ L (sectorNumber x.2) (sectorNumber y.1.1)
      (sectorNumber y.2) (sectorNumber z.2) (B y.1.1 x.1 y.1.2 z.1.2)
    else 0

/-- The surviving tensor: sector labels match on all three legs, while the
additional second/third coordinates form a dot product. -/
def separationTarget (B : Fin M → Tensor K X Y Z) :
    Tensor K (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2 then
    B y.1.1 x.1 y.1.2 z.1.2 else 0

/-- The square-weighted polynomial has exactly the advertised constant tensor. -/
theorem separationPolynomial_coeff_zero {ζ : K} (hM : 0 < M)
    (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L) (B : Fin M → Tensor K X Y Z) :
    (fun x y z => (separationPolynomial (L := L) ζ B x y z).coeff 0) =
      separationTarget B := by
  classical
  funext x y z
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, hyz, ↓reduceIte]
    rw [projectedBranchPolynomial_coeff_zero hM hL hradius hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _)]
    simp only [sectorNumber_injective.eq_iff, separationTarget, hyz, true_and]
  · simp [separationPolynomial, separationTarget, hyz]

/-- Its degree is bounded for each fixed finite separation construction. -/
theorem separationPolynomial_degree {ζ : K} (hM : 0 < M)
    (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L) (B : Fin M → Tensor K X Y Z)
    (x : X × Fin M) (y : (Fin M × Y) × Fin M) (z : (Fin M × Z) × Fin M) :
    (separationPolynomial (L := L) ζ B x y z).degree ≤ ((M - 1) ^ 2 : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, hyz, ↓reduceIte]
    exact projectedBranchPolynomial_coeff_eq_zero_of_lt hM hL hradius hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _) hn _
  · simp [separationPolynomial, hyz]

private theorem restrict_target_scalars
    {A B C A' B' C' : Type*} [Fintype A] [Fintype B] [Fintype C]
    (T : Tensor K A B C) (a : A' → A → K) (b : B' → B → K)
    (c : C' → C → K) (s : A' → K) (t : B' → K) (u : C' → K) :
    Tensor.restrict (fun x i => s x * a x i) (fun y j => t y * b y j)
        (fun z k => u z * c z k) T =
      fun x y z => (s x * t y * u z) * Tensor.restrict a b c T x y z := by
  funext x y z
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The first local Fourier map followed by its integer weight. -/
def firstSeparationMap (ζ t : K) (x : X × Fin M) (r : Fin L × X) : K :=
  t ^ firstWeight (sectorNumber x.2) * firstProjectionMap (L := L) ζ x r

/-- The second local Fourier map followed by its possibly negative weight. -/
def secondSeparationMap (ζ t : K) (y : (Fin M × Y) × Fin M)
    (r : Fin L × (Fin M × Y)) : K :=
  t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) * secondProjectionMap (L := L) ζ y r

/-- The third local Fourier map followed by its possibly negative weight. -/
def thirdSeparationMap (ζ t : K) (z : (Fin M × Z) × Fin M)
    (r : Fin L × (Fin M × Z)) : K :=
  t ^ thirdWeight (sectorNumber z.1.1) (sectorNumber z.2) * thirdProjectionMap (L := L) ζ z r

theorem weightedProjection_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (ζ t : K) (hζ : ζ ≠ 0) (B : Fin M → Tensor K X Y Z) :
    Tensor.restrict (firstSeparationMap (L := L) ζ t) (secondSeparationMap (L := L) ζ t)
        (thirdSeparationMap (L := L) ζ t)
        (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) =
      fun x y z =>
        (t ^ firstWeight (sectorNumber x.2) *
          t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) *
          t ^ thirdWeight (sectorNumber z.1.1) (sectorNumber z.2)) *
            projectedTensor (L := L) ζ B x y z := by
  unfold firstSeparationMap secondSeparationMap thirdSeparationMap
  rw [restrict_target_scalars, finiteProjection_restrict ζ hζ B]

/-- At every nonzero parameter the polynomial tensor is an ordinary restriction
of exactly `L` complete source copies. -/
theorem separationPolynomial_eval [Fintype X] [Fintype Y] [Fintype Z]
    {ζ : K} (hM : 0 < M) (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L)
    (B : Fin M → Tensor K X Y Z) (t : K) (ht : t ≠ 0) :
    (fun x y z => (separationPolynomial (L := L) ζ B x y z).eval t) =
      Tensor.restrict (firstSeparationMap (L := L) ζ t) (secondSeparationMap (L := L) ζ t)
        (thirdSeparationMap (L := L) ζ t)
        (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) := by
  rw [weightedProjection_restrict ζ t (hζ.ne_zero (by omega)) B]
  funext x y z
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, projectedTensor, hyz, ↓reduceIte,
      projectedBranchPolynomial, Polynomial.eval_monomial]
    simp only [← hyz]
    rw [admissibleFourierCoefficient_eq_ite hM hL hradius hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _)]
    split_ifs with hp
    · have he : t ^ firstWeight (sectorNumber x.2) *
          t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) *
          t ^ thirdWeight (sectorNumber y.1.1) (sectorNumber z.2) =
          t ^ totalWeight (sectorNumber x.2) (sectorNumber y.1.1)
            (sectorNumber y.2) (sectorNumber z.2) := by
        rw [totalWeight, zpow_add₀ ht, zpow_add₀ ht]
      rw [he, ← totalDegree_cast_of_phase_eq_zero hp, zpow_natCast]
      exact mul_comm _ _
    · simp
  · simp [separationPolynomial, projectedTensor, hyz]

/-- The first-leg relabeling adds the trivial first coordinate of the dot product. -/
def separationFirstEquiv : (X × Fin M) ≃ (Fin M × (X × Unit)) where
  toFun x := (x.2, (x.1, ()))
  invFun x := (x.2.1, x.1)
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨h, x, u⟩; cases u; rfl

/-- The other two relabelings merely reassociate their coordinates. -/
def separationSideEquiv (A : Type*) : ((Fin M × A) × Fin M) ≃
    (Fin M × (A × Fin M)) := Equiv.prodAssoc _ _ _

/-- The separated target, expressed as a genuine full direct sum of products. -/
theorem separationTarget_eq_directSum (B : Fin M → Tensor K X Y Z) :
    separationTarget B =
      Tensor.pullback
        separationFirstEquiv (separationSideEquiv Y) (separationSideEquiv Z)
        (Tensor.directSum (fun h => Tensor.product (B h)
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin M)))))) := by
  classical
  funext x y z
  simp only [separationTarget, Tensor.pullback, Tensor.directSum, Tensor.product,
    Tensor.cyclic, Tensor.dotPairing, separationFirstEquiv, separationSideEquiv,
    Equiv.coe_fn_mk, Equiv.prodAssoc_apply]
  by_cases hxy : x.2 = y.1.1
  · by_cases hyz : y.1.1 = z.1.1
    · simp [hxy, hyz]
    · simp [hxy, hyz]
  · simp [hxy]


/-- Every algebraically closed field admits the OAI finite separation polynomial,
with at most the original five M source copies, including in positive characteristic. -/
theorem exists_finiteSeparation [IsAlgClosed K]
    [Fintype X] [Fintype Y] [Fintype Z]
    (hM : 0 < M) (B : Fin M → Tensor K X Y Z) :
    ∃ (L : ℕ) (ζ : K), L ≤ 5 * M ∧
      (fun x y z => (separationPolynomial (L := L) ζ B x y z).coeff 0) =
        separationTarget B ∧
      (∀ x y z, (separationPolynomial (L := L) ζ B x y z).degree ≤
        ((M - 1) ^ 2 : ℕ)) ∧
      (∀ t : K, t ≠ 0 →
        (fun x y z => (separationPolynomial (L := L) ζ B x y z).eval t) =
          Tensor.restrict (firstSeparationMap (L := L) ζ t)
            (secondSeparationMap (L := L) ζ t) (thirdSeparationMap (L := L) ζ t)
            (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B))) := by
  obtain ⟨L, ζ, _, hL, hradius, hbound, hζ⟩ :=
    OAIAllFieldsFourier.exists_padded_period_and_root K M hM
  exact ⟨L, ζ, hbound, separationPolynomial_coeff_zero hM hL hradius hζ B,
    separationPolynomial_degree hM hL hradius hζ B,
    separationPolynomial_eval hM hL hradius hζ B⟩

end OAIAllFieldsSeparation

end

end AllFieldsModule18
/- END all-fields module GenericSeparation -/

/- BEGIN all-fields module GenericSeparationApproximation -/
section AllFieldsModule19
set_option autoImplicit false
noncomputable section
open OAI.MatrixMultiplication.Foundation
open scoped BigOperators
namespace OAIAllFieldsSeparation
variable {K : Type*} [Field K] {M L : ℕ} {X Y Z : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
private theorem polynomial_rank_bound
    (P : Tensor (Polynomial K) X Y Z) :
    Tensor.RankAtMost P (Fintype.card (X × Y)) := by
  classical
  let a : X × Y → X → Polynomial K := fun i x => if i.1 = x then 1 else 0
  let b : X × Y → Y → Polynomial K := fun i y => if i.2 = y then 1 else 0
  let c : X × Y → Z → Polynomial K := fun i z => P i.1 i.2 z
  have heq : P = fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
    funext x y z
    simp [Tensor.rankOne, a, b, c, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- The explicit separation polynomial, viewed as a polynomial approximation
to its constant tensor. Its rank bound is supplied by a coordinate expansion. -/
def separationPolynomialApproximation {ζ : K} (hM : 0 < M)
    (hL : (L : K) ≠ 0) (hradius : 3 * (M - 1) < L)
    (hζ : IsPrimitiveRoot ζ L) (B : Fin M → Tensor K X Y Z) :
    Tensor.PolynomialApproximation (separationTarget B)
      (Fintype.card ((X × Fin M) × ((Fin M × Y) × Fin M))) 0 ((M - 1) ^ 2) where
  polynomial := separationPolynomial (L := L) ζ B
  rank_bound := polynomial_rank_bound _
  vanishes := by
    intro _ _ _ k hk
    exact (Nat.not_lt_zero k hk).elim
  leading := by
    intro x y z
    exact congrFun (congrFun (congrFun (separationPolynomial_coeff_zero hM hL hradius hζ B) x) y) z
  degree_bound := separationPolynomial_degree hM hL hradius hζ B


end OAIAllFieldsSeparation

end

end AllFieldsModule19
/- END all-fields module GenericSeparationApproximation -/

/- BEGIN all-fields module GenericFiniteSeparation -/
section AllFieldsModule20

/-! Character accounting for characteristic-safe finite separation.
The period is at most 5*M, so the original separation constant is preserved.
-/
set_option autoImplicit false
noncomputable section
open OAI.MatrixMultiplication.Foundation
open OAIAllFieldsSeparation
open scoped BigOperators
namespace OAI.MatrixMultiplication.AuxiliarySeparation.Character

variable {K : Type*} [Field K] [IsAlgClosed K]
variable {M : ℕ} {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable (χ : Character K)

/-- Finite separation costs at most five M copies over any algebraically closed field. -/
theorem value_separationTarget_le (hM : 0 < M) (B : Fin M → Tensor K X Y Z) :
    χ.value (separationTarget B) ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  classical
  obtain ⟨L, ζ, _, hL, hradius, hcopies, hζ⟩ :=
    OAIAllFieldsFourier.exists_padded_period_and_root K M hM
  have hbound : χ.value (separationTarget B) ≤
      χ.value (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) := by
    apply χ.value_le_of_polynomialApproximation
      (separationPolynomialApproximation hM hL hradius hζ B) (χ.nonneg _)
    intro t ht
    change χ.value (fun x y z => (separationPolynomial (L := L) ζ B x y z).eval t) ≤ _
    rw [separationPolynomial_eval hM hL hradius hζ B t ht]
    exact χ.monotone _ _ _ _
  rw [χ.value_copies] at hbound
  calc
    χ.value (separationTarget B) ≤ (L : ℝ) * χ.value (sharedFirstTensor B) := hbound
    _ ≤ ((5 * M : ℕ) : ℝ) * χ.value (sharedFirstTensor B) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcopies) (χ.nonneg _)
    _ = 5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by simp

/-- The separated tensor is the full direct sum of branch/dot-product tensors. -/
theorem value_separationTarget (hM : 0 < M) (B : Fin M → Tensor K X Y Z) :
    χ.value (separationTarget B) =
      (∑ h, χ.value (B h)) * (M : ℝ) ^ χ.pX := by
  classical
  rw [separationTarget_eq_directSum, χ.value_reindex, χ.map_directSum]
  simp only [χ.map_product, χ.value_cyclic_cyclic_dotPairing hM, Finset.sum_mul]

/-- OAI's finite separation inequality, with its original constant, in arbitrary characteristic. -/
theorem finiteSeparation_bound (hM : 0 < M) (B : Fin M → Tensor K X Y Z) :
    (∑ h, χ.value (B h)) * (M : ℝ) ^ χ.pX ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  rw [← χ.value_separationTarget hM B]
  exact χ.value_separationTarget_le hM B

end OAI.MatrixMultiplication.AuxiliarySeparation.Character

end

end AllFieldsModule20
/- END all-fields module GenericFiniteSeparation -/

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

omit [Fintype X'] [Fintype Y'] [Fintype Z'] in
/-- Support in embedded coordinate sets reconstructs the tensor by zero extension. -/
theorem tensor_eq_extendByZero_pullback (T : Tensor 𝕜 X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    T = Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0)
      (Tensor.pullback fx fy fz T) := by
  classical
  funext x' y' z'
  by_cases hx' : x' ∈ Set.range fx
  · obtain ⟨x, rfl⟩ := hx'
    by_cases hy' : y' ∈ Set.range fy
    · obtain ⟨y, rfl⟩ := hy'
      by_cases hz' : z' ∈ Set.range fz
      · obtain ⟨z, rfl⟩ := hz'
        simp [Tensor.restrict, Tensor.pullback, hx.eq_iff, hy.eq_iff, hz.eq_iff,
          ite_mul, mul_ite]
      · have hzero : T (fx x) (fy y) z' = 0 := by
          by_contra h
          exact hz' (hs _ _ _ h).2.2
        have hnone : ∀ z, fz z ≠ z' := fun z h => hz' ⟨z, h⟩
        simp [Tensor.restrict, hzero, hnone]
    · have hzero : T (fx x) y' z' = 0 := by
        by_contra h
        exact hy' (hs _ _ _ h).2.1
      have hnone : ∀ y, fy y ≠ y' := fun y h => hy' ⟨y, h⟩
      simp [Tensor.restrict, hzero, hnone]
  · have hzero : T x' y' z' = 0 := by
      by_contra h
      exact hx' (hs _ _ _ h).1
    have hnone : ∀ x, fx x ≠ x' := fun x h => hx' ⟨x, h⟩
    simp [Tensor.restrict, hzero, hnone]

namespace Character

/-- A character ignores ambient coordinates outside a tensor's support. -/
theorem value_eq_pullback_of_support (χ : (Character 𝕜)) (T : Tensor 𝕜 X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    χ.value T = χ.value (Tensor.pullback fx fy fz T) := by
  calc
    χ.value T = χ.value (Tensor.restrict
        (fun x' x => if fx x = x' then 1 else 0)
        (fun y' y => if fy y = y' then 1 else 0)
        (fun z' z => if fz z = z' then 1 else 0)
        (Tensor.pullback fx fy fz T)) :=
      congrArg χ.value (tensor_eq_extendByZero_pullback T fx fy fz hx hy hz hs)
    _ = _ := χ.value_extendByZero _ fx fy fz hx hy hz

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

/-- Branches sharing their first input but with independently sized other legs. -/
def sharedFirstDependentTensor (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) :
    Tensor 𝕜 X (Σ i, Y i) (Σ i, Z i) :=
  fun x y z => if h : z.1 = y.1 then B y.1 x y.2 (h ▸ z.2) else 0

/-- A branch in the two common sigma coordinate spaces, with zero padding. -/
def paddedSharedBranch (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) (i : Fin M) :
    Tensor 𝕜 X (Σ i, Y i) (Σ i, Z i) :=
  Tensor.restrict (fun x' x => if x = x' then 1 else 0)
    (fun y b => if Sigma.mk i b = y then 1 else 0)
    (fun z c => if Sigma.mk i c = z then 1 else 0) (B i)

omit [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)] in
@[simp] theorem sharedFirstDependentTensor_matching
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Y i) (z : Z i) :
    sharedFirstDependentTensor B x ⟨i, y⟩ ⟨i, z⟩ = B i x y z := by
  simp [sharedFirstDependentTensor]

@[simp] theorem paddedSharedBranch_matching
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Y i) (z : Z i) :
    paddedSharedBranch B i x ⟨i, y⟩ ⟨i, z⟩ = B i x y z := by
  simp [paddedSharedBranch, Tensor.restrict, ite_mul, mul_ite]

theorem paddedSharedBranch_pullback
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) (i : Fin M) :
    Tensor.pullback id (Sigma.mk i) (Sigma.mk i) (paddedSharedBranch B i) = B i := by
  funext x y z
  exact paddedSharedBranch_matching B i x y z

/-- A nonzero branch remains nonzero after padding. -/
theorem paddedSharedBranch_ne_zero
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) (i : Fin M) (hB : B i ≠ 0) :
    paddedSharedBranch B i ≠ 0 := by
  intro h
  apply hB
  rw [← paddedSharedBranch_pullback B i, h]
  rfl

theorem paddedSharedBranch_zero_middle
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Σ i, Y i) (z : Σ i, Z i) (hy : y.1 ≠ i) :
    paddedSharedBranch B i x y z = 0 := by
  have hzero : ∀ b : Y i, Sigma.mk i b ≠ y :=
    fun b h => hy (congrArg Sigma.fst h).symm
  simp [paddedSharedBranch, Tensor.restrict, hzero]

theorem paddedSharedBranch_zero_right
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Σ i, Y i) (z : Σ i, Z i) (hz : z.1 ≠ i) :
    paddedSharedBranch B i x y z = 0 := by
  have hzero : ∀ c : Z i, Sigma.mk i c ≠ z :=
    fun c h => hz (congrArg Sigma.fst h).symm
  simp [paddedSharedBranch, Tensor.restrict, hzero]

/-- Redundant branch labels zero-extend the varying-dimension shared tensor. -/
theorem sharedFirstTensor_paddedSharedBranch
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) :
    sharedFirstTensor (paddedSharedBranch B) = Tensor.restrict
      (fun (x' : X) x => if x = x' then 1 else 0)
      (fun (y' : Fin M × (Σ i, Y i)) y => if (y.1, y) = y' then 1 else 0)
      (fun (z' : Fin M × (Σ i, Z i)) z => if (z.1, z) = z' then 1 else 0)
      (sharedFirstDependentTensor B) := by
  funext x' y' z'
  rcases y' with ⟨i, ⟨iy, y⟩⟩
  rcases z' with ⟨j, ⟨iz, z⟩⟩
  have hgraph {A : Type} (f : A → Fin M) (a x : A) (i : Fin M) :
      (f a, a) = (i, x) ↔ a = x ∧ f x = i := by
    constructor
    · intro h
      have ha : a = x := congrArg Prod.snd h
      refine ⟨ha, ?_⟩
      rw [← ha]
      exact congrArg Prod.fst h
    · rintro ⟨rfl, h⟩
      simp [h]
  simp only [Tensor.restrict, hgraph, ite_and]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : iy = i
  · subst iy
    by_cases hz : iz = i
    · subst iz
      by_cases hij : i = j
      · subst j
        simp [sharedFirstTensor, sharedFirstDependentTensor]
      · simp [sharedFirstTensor, hij]
    · simp [sharedFirstTensor, sharedFirstDependentTensor,
        paddedSharedBranch_zero_right B i x' ⟨i, y⟩ ⟨iz, z⟩ hz, hz]
  · simp [sharedFirstTensor,
      paddedSharedBranch_zero_middle B i x' ⟨iy, y⟩ ⟨iz, z⟩ hi, hi]

namespace Character

/-- Padding a branch changes no character value. -/
@[simp] theorem value_paddedSharedBranch (χ : (Character 𝕜))
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) (i : Fin M) :
    χ.value (paddedSharedBranch B i) = χ.value (B i) := by
  simpa only [paddedSharedBranch, id_eq] using
    χ.value_extendByZero (B i) id (Sigma.mk i) (Sigma.mk i)
      Function.injective_id
      (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
      (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)

/-- Passing to uniform ambient branch spaces adds no character cost. -/
@[simp] theorem value_sharedFirstTensor_padded (χ : (Character 𝕜))
    (B : ∀ i, Tensor 𝕜 X (Y i) (Z i)) :
    χ.value (sharedFirstTensor (paddedSharedBranch B)) =
      χ.value (sharedFirstDependentTensor B) := by
  rw [sharedFirstTensor_paddedSharedBranch]
  simpa only [id_eq] using
    χ.value_extendByZero (sharedFirstDependentTensor B) id
      (fun y => (y.1, y)) (fun z => (z.1, z)) Function.injective_id
      (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)

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

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Recovering the two coordinate labels identifies the tagged tensor with
the coefficientwise sum of the branches. -/
theorem sharedFirstTensor_pullback_labels
    (B : Fin M → Tensor 𝕜 X Y Z) (ly : Y → Fin M) (lz : Z → Fin M)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    Tensor.pullback id (fun y => (ly y, y)) (fun z => (lz z, z))
      (sharedFirstTensor B) = ∑ i, B i := by
  classical
  funext x y z
  simp only [Finset.sum_apply]
  change (if ly y = lz z then B (ly y) x y z else 0) = ∑ i, B i x y z
  have hsum : (∑ i, B i x y z) = B (ly y) x y z := by
    apply Finset.sum_eq_single (ly y)
    · intro i _ hi
      by_contra h
      exact hi (hsupport i x y z h).1.symm
    · simp
  rw [hsum]
  split_ifs with h
  · rfl
  · symm
    by_contra hb
    exact h ((hsupport (ly y) x y z hb).2.symm)

namespace Character

/-- Branch labels determined by both non-shared coordinates can be inserted
or forgotten without changing a character. -/
theorem value_sharedFirstTensor_eq_sum (χ : (Character 𝕜))
    (B : Fin M → Tensor 𝕜 X Y Z) (ly : Y → Fin M) (lz : Z → Fin M)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    χ.value (sharedFirstTensor B) = χ.value (∑ i, B i) := by
  have hs : ∀ x y z, sharedFirstTensor B x y z ≠ 0 →
      x ∈ Set.range (id : X → X) ∧
        y ∈ Set.range (fun y => (ly y, y)) ∧
        z ∈ Set.range (fun z => (lz z, z)) := by
    intro x y z h
    have hyz : y.1 = z.1 := by
      by_contra hne
      exact h (by simp [sharedFirstTensor, hne])
    have hb : B y.1 x y.2 z.2 ≠ 0 := by
      simpa only [sharedFirstTensor, hyz, ↓reduceIte] using h
    obtain ⟨hy, hz⟩ := hsupport y.1 x y.2 z.2 hb
    exact ⟨⟨x, rfl⟩, ⟨y.2, Prod.ext hy rfl⟩,
      ⟨z.2, Prod.ext (hz.trans hyz) rfl⟩⟩
  have heq := χ.value_eq_pullback_of_support (sharedFirstTensor B) id
    (fun y => (ly y, y)) (fun z => (lz z, z)) Function.injective_id
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h) hs
  rw [sharedFirstTensor_pullback_labels B ly lz hsupport] at heq
  exact heq

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

/-- For a character, nonzero tensors supply all positivity needed by the
entropy limit. The only quantitative premise is the finite integral-type
comparison with the paper's fixed loss five. -/
theorem log_tag_of_integral_type_comparison (χ : (Character 𝕜))
    (q : FiniteLaw I) (T : Tensor 𝕜 X Y Z)
    (B : ∀ a, Tensor 𝕜 (BX a) (BY a) (BZ a)) (p : ℝ)
    (hT : T ≠ 0) (hB : ∀ a, B a ≠ 0)
    (hfinite : ∀ counts : I → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p *
          ∏ a, χ.value (B a) ^ counts a ≤
        5 * χ.value T ^ (∑ a, counts a)) :
    p * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (χ.value (B a)) ≤
      Real.log (χ.value T) :=
  MatrixMultiplication.AuxiliarySeparation.log_tag_of_integral_bounds q (fun a => χ.value (B a)) p
    (χ.value T) 5 (fun a => lt_of_lt_of_le zero_lt_one (χ.one_le_value (hB a)))
    (lt_of_lt_of_le zero_lt_one (χ.one_le_value hT)) (by norm_num) hfinite

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

/-- A word prescribes one branch tensor at each tensor-product position. -/
def branchWordTensor (B : Fin s → Tensor 𝕜 X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    Tensor 𝕜 (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, B (w i) (x i) (y i) (z i)

/-- The canonical branch word tensor evaluates multiplicatively. -/
theorem Character.value_branchWordTensor (χ : (Character 𝕜))
    (B : Fin s → Tensor 𝕜 X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    χ.value (branchWordTensor B w) = ∏ i, χ.value (B (w i)) := by
  induction n with
  | zero =>
      have hzero : branchWordTensor B w = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) unitTensor := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, unitTensor]
      rw [hzero, χ.value_reindex, χ.map_one]
      simp
  | succ n ih =>
      have heq : branchWordTensor B w = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product (B (w 0)) (branchWordTensor B (Fin.tail w))) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, Fin.prod_univ_succ]
      rfl

/-- All words of an exact type have the same character value. -/
theorem Character.value_exact_branchWordTensor (χ : (Character 𝕜))
    (B : Fin s → Tensor 𝕜 X Y Z) (counts : Fin s → ℕ) (w : ExactWords counts) :
    χ.value (branchWordTensor B w.val) = ∏ a, χ.value (B a) ^ counts a := by
  rw [χ.value_branchWordTensor,
    ← Fintype.prod_fiberwise' w.val (fun a => χ.value (B a))]
  simp only [Finset.prod_const, Finset.card_univ]
  apply Finset.prod_congr rfl
  intro a _
  rw [show Fintype.card {i // w.val i = a} = counts a from w.property a]

/-- A coordinate on a retained split leg remembers its type word. -/
def typeWordCoordinate (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts)
    {U : Type} (y : Fin (Fintype.card (ExactWords counts)) ×
      (Fin (∑ a, counts a) → U)) : Fin (∑ a, counts a) → (Fin s × U) :=
  fun i => ((e y.1).val i, y.2 i)

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Restricting both split legs to one exact type produces a shared-first
tensor whose branches are precisely the prescribed branch products. -/
theorem exactType_power_pullback (B : Fin s → Tensor 𝕜 X Y Z)
    (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    Tensor.pullback id (typeWordCoordinate counts e) (typeWordCoordinate counts e)
        (Tensor.power (sharedFirstTensor B) (∑ a, counts a)) =
      sharedFirstTensor (fun h => branchWordTensor B (e h).val) := by
  funext x y z
  by_cases h : y.1 = z.1
  · simp [Tensor.pullback, Tensor.power, typeWordCoordinate, sharedFirstTensor,
      branchWordTensor, h]
  · have hword : (e y.1).val ≠ (e z.1).val := by
      intro heq
      exact h (e.injective (Subtype.ext heq))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hword
    simp only [Tensor.pullback, Tensor.power, sharedFirstTensor, h, ↓reduceIte,
      typeWordCoordinate, id_eq]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- The exact-type restriction never exceeds the source power in character. -/
theorem Character.exactType_value_le_power (χ : (Character 𝕜))
    (B : Fin s → Tensor 𝕜 X Y Z) (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    χ.value (sharedFirstTensor (fun h => branchWordTensor B (e h).val)) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  rw [← exactType_power_pullback B counts e, ← χ.value_power]
  exact χ.value_pullback_le _ _ _ _

/-- The finite separation construction and exact-type restriction give the
integral inequality, with no assumed character comparison. -/
theorem Character.integral_type_comparison (χ : (Character 𝕜))
    (B : Fin s → Tensor 𝕜 X Y Z) (counts : Fin s → ℕ) :
    (Fintype.card (ExactWords counts) : ℝ) ^ χ.pX *
        ∏ a, χ.value (B a) ^ counts a ≤
      5 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  let M := Fintype.card (ExactWords counts)
  let e : Fin M ≃ ExactWords counts := (Fintype.equivFin _).symm
  let W : Fin M → Tensor 𝕜 (Fin (∑ a, counts a) → X)
      (Fin (∑ a, counts a) → Y) (Fin (∑ a, counts a) → Z) :=
    fun h => branchWordTensor B (e h).val
  have hM : 0 < M := by
    simpa only [M, Fintype.card_eq_nat_card] using exactWords_card_pos counts
  have hsep : ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor W) := by
    simpa only [W, χ.value_exact_branchWordTensor, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      χ.finiteSeparation_bound hM W
  have hsource : χ.value (sharedFirstTensor W) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
    χ.exactType_value_le_power B counts e
  have hcancel : (M : ℝ) *
      ((M : ℝ) ^ χ.pX * ∏ a, χ.value (B a) ^ counts a) ≤
        (M : ℝ) * (5 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a)) := by
    calc
      _ = ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX := by ring
      _ ≤ 5 * (M : ℝ) * χ.value (sharedFirstTensor W) := hsep
      _ ≤ 5 * (M : ℝ) * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  have hbound := (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hM : (0 : ℝ) < M)).mp hcancel
  simpa only [M, Fintype.card_eq_nat_card] using hbound

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
  apply χ.tag_of_integral_type_comparison q (sharedFirstTensor B) B χ.pX hT hB
  intro counts _hcounts
  simpa only [Fintype.card_eq_nat_card] using χ.integral_type_comparison B counts

/-- The logarithmic form of the actual tensor tag inequality. -/
theorem Character.log_sharedFirst_tag (χ : (Character 𝕜))
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor 𝕜 X Y Z)
    (hB : ∀ a, B a ≠ 0) :
    χ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (χ.value (B a)) ≤
      Real.log (χ.value (sharedFirstTensor B)) := by
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
    subst s
    have htotal := q.total
    simp at htotal
  have hT : sharedFirstTensor B ≠ 0 :=
    sharedFirstTensor_ne_zero_of_branch B ⟨0, hs⟩ (hB ⟨0, hs⟩)
  apply χ.log_tag_of_integral_type_comparison q (sharedFirstTensor B) B χ.pX hT hB
  intro counts _hcounts
  simpa only [Fintype.card_eq_nat_card] using χ.integral_type_comparison B counts

section Dependent

variable {U V : Fin s → Type} [∀ a, Fintype (U a)] [∀ a, Fintype (V a)]

/-- Branches may have different second- and third-leg dimensions. Padding
those spaces preserves their character values and the shared-input tensor. -/
theorem Character.sharedFirstDependent_tag (χ : (Character 𝕜))
    (q : FiniteLaw (Fin s)) (B : ∀ a, Tensor 𝕜 X (U a) (V a))
    (hB : ∀ a, B a ≠ 0) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstDependentTensor B) := by
  simpa only [χ.value_paddedSharedBranch, χ.value_sharedFirstTensor_padded] using
    χ.sharedFirst_tag q (paddedSharedBranch B)
      (fun a => paddedSharedBranch_ne_zero B a (hB a))

/-- The logarithmic tag inequality for branches with varying dimensions. -/
theorem Character.log_sharedFirstDependent_tag (χ : (Character 𝕜))
    (q : FiniteLaw (Fin s)) (B : ∀ a, Tensor 𝕜 X (U a) (V a))
    (hB : ∀ a, B a ≠ 0) :
    χ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (χ.value (B a)) ≤
      Real.log (χ.value (sharedFirstDependentTensor B)) := by
  simpa only [χ.value_paddedSharedBranch, χ.value_sharedFirstTensor_padded] using
    χ.log_sharedFirst_tag q (paddedSharedBranch B)
      (fun a => paddedSharedBranch_ne_zero B a (hB a))

end Dependent

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end TagModule4


end AllFieldsModule21
/- END all-fields module GenericTags -/

/- BEGIN all-fields module GenericDeterminantCharacter -/
section AllFieldsModule22
set_option autoImplicit false
open OAIAllFieldsSeparation
namespace OAI
variable {K : Type*} [Field K] [IsAlgClosed K]

/-!
# The determinant inequality for an actual tensor character

The shared-input tag inequality is applied to the two concrete branches of the
checked determinant degeneration. All basis changes and the output-dual change
are supplied by `DeterminantFiltration`.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

/-- The two graded blocks, padded with zeros in common coordinate spaces. -/
def branch (d e : ℕ) (n : Fin 2) :
    Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if n = 0 then if i.val + j.val = k.val then 1 else 0 else 0
  | i, .inr j, .inr k => if n = 1 then if i.val + j.val = k.val then 1 else 0 else 0
  | _, _, _ => 0

def branchLabel (e : ℕ) : Index e → Fin 2
  | .inl _ => 0
  | .inr _ => 1

theorem branch_support (d e : ℕ) (n : Fin 2) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) (h : branch (K := K) d e n i j k ≠ 0) :
    branchLabel e j = n ∧ branchLabel (d + e) k = n := by
  fin_cases n <;> rcases j with j | j <;> rcases k with k | k <;>
    simp_all [branch, branchLabel]

theorem sum_branch (d e : ℕ) :
    (∑ n, branch (K := K) d e n) = gradedTensor (K := K) d e := by
  funext i j k
  rcases j with j | j <;> rcases k with k | k <;>
    simp [branch, gradedTensor]

theorem branch_ne_zero (d e : ℕ) (he : 0 < e) (n : Fin 2) :
    branch (K := K) d e n ≠ 0 := by
  intro h
  fin_cases n
  · have hv := congrFun (congrFun (congrFun h ⟨0, by omega⟩)
      (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩)
    simp [branch] at hv
  · have hv := congrFun (congrFun (congrFun h ⟨0, by omega⟩)
      (.inr ⟨0, he⟩)) (.inr ⟨0, by omega⟩)
    simp [branch] at hv

end DeterminantFiltration

namespace Character

open DeterminantFiltration

variable (χ : (Character K))

theorem value_determinant_branch_zero (d e : ℕ) :
    χ.value (branch (K := K) d e 0) = χ.value (convolution (d + 1) (e + 2)) := by
  let fz : Fin ((d + 1) + (e + 2) - 1) → Index (d + e) :=
    fun k => .inl (Fin.cast (by omega) k)
  have hfz : Function.Injective fz := by
    intro a b h
    exact Fin.ext (congrArg (fun z : Index (d + e) =>
      match z with | .inl k => k.val | .inr k => k.val) h)
  have hs : ∀ i j k, branch (K := K) d e 0 i j k ≠ 0 →
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
      j ∈ Set.range (Sum.inl : Fin (e + 2) → Index e) ∧ k ∈ Set.range fz := by
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    · exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz]⟩⟩
    all_goals simp [branch] at h
  have hv := χ.value_eq_pullback_of_support (branch (K := K) d e 0) id Sum.inl fz
    Function.injective_id Sum.inl_injective hfz hs
  have ht : Tensor.pullback id Sum.inl fz (branch (K := K) d e 0) =
      convolution (d + 1) (e + 2) := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  simpa only [ht] using hv

theorem value_determinant_branch_one (d e : ℕ) :
    χ.value (branch (K := K) d e 1) = χ.value (convolution (d + 1) e) := by
  let fz : Fin ((d + 1) + e - 1) → Index (d + e) :=
    fun k => .inr (Fin.cast (by omega) k)
  have hfz : Function.Injective fz := by
    intro a b h
    exact Fin.ext (congrArg (fun z : Index (d + e) =>
      match z with | .inl k => k.val | .inr k => k.val) h)
  have hs : ∀ i j k, branch (K := K) d e 1 i j k ≠ 0 →
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
      j ∈ Set.range (Sum.inr : Fin e → Index e) ∧ k ∈ Set.range fz := by
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    any_goals simp [branch] at h
    exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz]⟩⟩
  have hv := χ.value_eq_pullback_of_support (branch (K := K) d e 1) id Sum.inr fz
    Function.injective_id Sum.inr_injective hfz hs
  have ht : Tensor.pullback id Sum.inr fz (branch (K := K) d e 1) =
      convolution (d + 1) e := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  simpa only [ht] using hv

private theorem value_bool_dot :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool))) =
      (2 : ℝ) ^ χ.pX := by
  have hv := χ.value_reindex
    (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))
    (Equiv.refl Unit) finTwoEquiv finTwoEquiv
  have ht : Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv
      (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool))) =
        Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin 2))) := by
    funext i j k
    simp [Tensor.pullback, Tensor.cyclic, Tensor.dotPairing]
  rw [ht] at hv
  exact hv.symm.trans (χ.value_cyclic_cyclic_dotPairing (by decide))

/-- The auxiliary dot product is charged once, on the actual source tensor. -/
theorem value_determinant_source_le (d e : ℕ) :
    χ.value (sourceTensor (K := K) d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  rw [sourceTensor_product]
  apply (χ.value_pullback_le _ _ _ _).trans_eq
  rw [χ.map_product, χ.value_bool_dot]
  ring

/-- Actual basis-change and degeneration (K := K) certificates give this comparison. -/
theorem value_determinant_graded_le (d e : ℕ) :
    χ.value (gradedTensor (K := K) d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  calc
    χ.value (gradedTensor (K := K) d e) ≤ χ.value (adaptedTensor (K := K) d e) :=
      χ.value_polynomialRestrictionDegeneration_le (degeneration (K := K) d e)
    _ ≤ χ.value (sourceTensor (K := K) d e) := by
      simpa only [sourceTensor_coordinate_change] using
        χ.monotone (sourceTensor (K := K) d e) (fixedFirst (K := K) d) (inputChange (K := K) e)
          (outputDualChange (K := K) (d + e))
    _ ≤ _ := χ.value_determinant_source_le d e

/-- The binary tag bound before normalizing over all six characters. -/
theorem convolution_concavity_tag_dims (d e : ℕ) (he : 0 < e)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution (d + 1) (e + 2)) ^ q *
        χ.value (convolution (d + 1) e) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  have ht := χ.sharedFirst_tag (binaryLaw q hq₀ hq₁) (branch (K := K) d e)
    (branch_ne_zero d e he)
  rw [χ.value_sharedFirstTensor_eq_sum (branch (K := K) d e)
    (branchLabel e) (branchLabel (d + e)) (branch_support d e), sum_branch] at ht
  rw [binaryLaw_entropy, binaryLaw_product,
    χ.value_determinant_branch_zero, χ.value_determinant_branch_one] at ht
  apply le_trans (b := χ.value (gradedTensor (K := K) d e))
  · simpa only [mul_assoc] using ht
  · exact χ.value_determinant_graded_le d e

/-- The determinant inequality in the paper's positive-dimension notation. -/
theorem convolution_concavity_tag (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution (K := K) a (b + 1)) ^ q *
        χ.value (convolution (K := K) a (b - 1)) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (K := K) a b) := by
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  obtain ⟨e, rfl, he⟩ : ∃ e, b = e + 1 ∧ 0 < e := ⟨b - 1, by omega, by omega⟩
  simpa [Nat.add_assoc] using χ.convolution_concavity_tag_dims d e he q hq₀ hq₁

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI



end AllFieldsModule22
/- END all-fields module GenericDeterminantCharacter -/

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

/-- Number of second-leg coordinates in the original convolution. -/
def sourceWidth (a h : ℕ) : ℕ := 3 * h + a - 1

/-- Beginning of the right sector on both the second and third legs. -/
def rightStart (a h : ℕ) : ℕ := 2 * h + a - 1

/-- A coefficient-one term of the original convolution tensor. -/
def Support (a h i j k : ℕ) : Prop :=
  i < a ∧ j < sourceWidth a h ∧ k = i + j

/-- The middle interval on the second tensor leg. -/
def MiddleY (a h j : ℕ) : Prop := h ≤ j ∧ j < rightStart a h

/-- The middle interval on the third tensor leg. -/
def MiddleZ (a h k : ℕ) : Prop := h + a - 1 ≤ k ∧ k < rightStart a h

instance (a h j : ℕ) : Decidable (MiddleY a h j) := inferInstanceAs
  (Decidable (h ≤ j ∧ j < rightStart a h))

instance (a h k : ℕ) : Decidable (MiddleZ a h k) := inferInstanceAs
  (Decidable (h + a - 1 ≤ k ∧ k < rightStart a h))

/-- No weight is assigned to the common first leg. -/
def firstWeight (_i : ℕ) : ℤ := 0

/-- Weight one on the middle second-leg interval, zero elsewhere. -/
def secondWeight (a h j : ℕ) : ℤ := if MiddleY a h j then 1 else 0

/-- Weight minus one on the middle third-leg interval, zero elsewhere. -/
def thirdWeight (a h k : ℕ) : ℤ := if MiddleZ a h k then -1 else 0

/-- Exponent of the degeneration parameter on one term. -/
def totalWeight (a h i j k : ℕ) : ℤ :=
  firstWeight i + secondWeight a h j + thirdWeight a h k

/-- The three retained blocks have matching sector labels. -/
def MatchingSectors (a h j k : ℕ) : Prop :=
  (j < h ∧ k < h + a - 1) ∨
  (MiddleY a h j ∧ MiddleZ a h k) ∨
  (rightStart a h ≤ j ∧ rightStart a h ≤ k)

/-- A middle third-leg coordinate can only be reached from the middle second leg. -/
theorem middleY_of_middleZ {a h i j k : ℕ}
    (hs : Support a h i j k) (hz : MiddleZ a h k) : MiddleY a h j := by
  unfold Support at hs
  unfold MiddleY MiddleZ rightStart at *
  omega

/-- Every term has exponent zero or one, so no negative powers occur. -/
theorem totalWeight_eq_zero_or_one {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ∨ totalWeight a h i j k = 1 := by
  have hmiddle := middleY_of_middleZ hs
  by_cases hy : MiddleY a h j <;> by_cases hz : MiddleZ a h k
  all_goals simp [totalWeight, firstWeight, secondWeight, thirdWeight, hy, hz] at *

theorem totalWeight_nonneg {a h i j k : ℕ}
    (hs : Support a h i j k) : 0 ≤ totalWeight a h i j k := by
  rcases totalWeight_eq_zero_or_one hs with hw | hw <;> omega

/-- The constant coefficient consists exactly of the three matching blocks. -/
theorem totalWeight_eq_zero_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔ MatchingSectors a h j k := by
  unfold Support sourceWidth at hs
  unfold MatchingSectors MiddleY MiddleZ rightStart
  unfold totalWeight firstWeight secondWeight thirdWeight MiddleY MiddleZ rightStart
  split_ifs <;> omega

/-- Only a middle second-leg coordinate paired with an outer third-leg coordinate
is erased by the degeneration. -/
theorem totalWeight_eq_one_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 1 ↔ MiddleY a h j ∧ ¬ MiddleZ a h k := by
  have hmiddle := middleY_of_middleZ hs
  by_cases hy : MiddleY a h j <;> by_cases hz : MiddleZ a h k
  all_goals simp [totalWeight, firstWeight, secondWeight, thirdWeight, hy, hz] at *

/-- Parametrization of the left copy of `C(a,h)`. -/
def LeftBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧ j = r ∧ k = u + r

/-- Parametrization of the middle copy with the second and third legs exchanged. -/
def MiddleBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = a - 1 - u ∧
    j = h + u + r ∧ k = h + a - 1 + r

/-- Parametrization of the right translated copy of `C(a,h)`. -/
def RightBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧
    j = rightStart a h + r ∧ k = rightStart a h + u + r

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

/-- On the left coordinate block, the support equation is the ordinary
convolution equation. -/
theorem left_support_coordinates {a h i r s : ℕ} (hi : i < a) (hr : r < h) :
    Support a h i r s ↔ s = i + r := by
  unfold Support sourceWidth
  omega

/-- Translation of the right block preserves the convolution equation. -/
theorem right_support_coordinates {a h i r s : ℕ} (hi : i < a) (hr : r < h) :
    Support a h i (rightStart a h + r) (rightStart a h + s) ↔ s = i + r := by
  unfold Support sourceWidth rightStart
  omega

/-- In middle-block coordinates the support equation is convolution with the
first coordinate reversed and the other two coordinates exchanged. -/
theorem middle_support_coordinates {a h i s r : ℕ}
    (hi : i < a) (hr : r < h) :
    Support a h i (h + s) (h + a - 1 + r) ↔ s = a - 1 - i + r := by
  unfold Support sourceWidth
  omega

/-- Exact retained support of the three-sector degeneration. -/
theorem retained_support_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  rw [totalWeight_eq_zero_iff hs, leftBranch_iff hs, middleBranch_iff hs,
    rightBranch_iff hs]
  rfl

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

/-- Exact equality of the retained support and the three explicitly
parametrized convolution branches, without a pre-existing support assumption. -/
theorem support_and_weight_zero_iff (a h i j k : ℕ) :
    (Support a h i j k ∧ totalWeight a h i j k = 0) ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  constructor
  · rintro ⟨hs, hw⟩
    exact (retained_support_iff hs).mp hw
  · intro hb
    have hs : Support a h i j k := hb.elim LeftBranch.support
      (fun hb => hb.elim MiddleBranch.support RightBranch.support)
    exact ⟨hs, (retained_support_iff hs).mpr hb⟩

/-- The first-coordinate reversal is involutive on its natural range. -/
theorem reverse_reverse {a u : ℕ} (hu : u < a) :
    a - 1 - (a - 1 - u) = u := by
  omega

/-- The middle branch has unique reversed-convolution coordinates. -/
theorem middleBranch_coordinates_unique {a h i k u r u' r' : ℕ}
    (hu : u < a) (hu' : u' < a)
    (hi : i = a - 1 - u) (hi' : i = a - 1 - u')
    (hk : k = h + a - 1 + r) (hk' : k = h + a - 1 + r') :
    u = u' ∧ r = r' := by
  omega

/-- The left and middle branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_middleBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ MiddleBranch a h i j k := by
  intro hm
  have hl' := (leftBranch_iff hl.support).mp hl
  have hm' := (middleBranch_iff hm.support).mp hm
  unfold MiddleY at hm'
  omega

/-- The left and right branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_rightBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hl' := (leftBranch_iff hl.support).mp hl
  have hr' := (rightBranch_iff hr.support).mp hr
  have hi := hr.support.1
  unfold rightStart at hr'
  omega

/-- The middle and right branches use disjoint second-leg coordinates. -/
theorem middleBranch_not_rightBranch {a h i j k : ℕ}
    (hm : MiddleBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hm' := (middleBranch_iff hm.support).mp hm
  have hr' := (rightBranch_iff hr.support).mp hr
  unfold MiddleY at hm'
  omega

/-- Positivity of the two original dimensions makes the left branch nonempty. -/
theorem leftBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, LeftBranch a h i j k :=
  ⟨0, 0, 0, 0, 0, ha, hh, rfl, rfl, rfl⟩

/-- Positivity makes the exchanged middle branch nonempty as well. -/
theorem middleBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, MiddleBranch a h i j k := by
  refine ⟨a - 1, h, h + a - 1, 0, 0, ha, hh, ?_, ?_, ?_⟩ <;> omega

/-- Positivity also makes the translated right branch nonempty. -/
theorem rightBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, RightBranch a h i j k := by
  refine ⟨0, rightStart a h, rightStart a h, 0, 0, ha, hh, ?_, ?_, ?_⟩ <;> omega

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

abbrev YIndex (a h : ℕ) := Fin (sourceWidth a h)
abbrev ZIndex (a h : ℕ) := Fin (a + sourceWidth a h - 1)

/-- The source (K := K) coefficient tensor, with its actual shared first-input space. -/
def source (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  convolution (K := K) a (sourceWidth a h)

theorem source_ne_zero_iff {a h : ℕ} (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    source (K := K) a h i j k ≠ 0 ↔ Support a h i.val j.val k.val := by
  simp only [source, convolution_ne_zero_iff, Support]
  constructor
  · intro heq
    exact ⟨i.isLt, j.isLt, heq.symm⟩
  · intro hs
    exact hs.2.2.symm

/-- The weight-zero part in the original coordinate spaces. -/
def retained (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if totalWeight a h i.val j.val k.val = 0 then source (K := K) a h i j k else 0

/-- The positive-weight part, all of whose supported terms have weight one. -/
def erased (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if totalWeight a h i.val j.val k.val = 1 then source (K := K) a h i j k else 0

/-- The left retained (K := K) branch, still in the common ambient coordinate spaces. -/
def leftTensor (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if LeftBranch a h i.val j.val k.val then 1 else 0

/-- The middle retained (K := K) branch; its first leg is the actual shared first leg. -/
def middleTensor (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if MiddleBranch a h i.val j.val k.val then 1 else 0

/-- The right retained (K := K) branch in the original coordinate spaces. -/
def rightTensor (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if RightBranch a h i.val j.val k.val then 1 else 0

/-- The retained (K := K) tensor is exactly the sum of the three stated branches,
with coefficient one on each and the original first-leg coordinates shared. -/
theorem retained_eq_three_branches (a h : ℕ) :
    retained (K := K) a h = leftTensor (K := K) a h + middleTensor (K := K) a h + rightTensor (K := K) a h := by
  funext i j k
  by_cases hs : Support a h i.val j.val k.val
  · have hsource : source (K := K) a h i j k = 1 := by
      exact (convolution_eq_one_iff i j k).mpr hs.2.2.symm
    have hw := retained_support_iff hs
    have hlm := leftBranch_not_middleBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    have hlr := leftBranch_not_rightBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    have hmr := middleBranch_not_rightBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    by_cases hl : LeftBranch a h i.val j.val k.val <;>
      by_cases hm : MiddleBranch a h i.val j.val k.val <;>
      by_cases hr : RightBranch a h i.val j.val k.val
    all_goals simp_all [retained, leftTensor, middleTensor, rightTensor]
  · have hsource : source (K := K) a h i j k = 0 := by
      by_contra hz
      exact hs ((source_ne_zero_iff i j k).mp hz)
    have hl : ¬ LeftBranch a h i.val j.val k.val := fun hb => hs hb.support
    have hm : ¬ MiddleBranch a h i.val j.val k.val := fun hb => hs hb.support
    have hr : ¬ RightBranch a h i.val j.val k.val := fun hb => hs hb.support
    simp [retained, leftTensor, middleTensor, rightTensor, hsource, hl, hm, hr]

/-- Every source (K := K) term belongs either to the retained (K := K) tensor or the erased (K := K) one. -/
theorem source_eq_retained_add_erased (a h : ℕ) :
    source (K := K) a h = retained (K := K) a h + erased (K := K) a h := by
  funext i j k
  by_cases hs : source (K := K) a h i j k = 0
  · simp [retained, erased, hs]
  · rcases totalWeight_eq_zero_or_one ((source_ne_zero_iff i j k).mp hs) with hw | hw
    all_goals simp [retained, erased, hw]

/-- The normalized polynomial (K := K) family appearing in the unshifted weights. -/
def normalizedPolynomial (a h : ℕ) :
    Tensor (Polynomial K) (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => C (retained (K := K) a h i j k) + X * C (erased (K := K) a h i j k)

/-- The first local map fixes the common input basis. -/
def leftMap (a : ℕ) (output input : Fin a) : Polynomial K :=
  if input = output then 1 else 0

/-- The second local map assigns weight one to the middle interval. -/
def middleMap (a h : ℕ) (output input : YIndex a h) : Polynomial K :=
  if input = output then (if MiddleY a h output.val then X else 1) else 0

/-- Shift the third-leg weights by one, giving weight zero to the middle
interval and weight one to the two outer intervals. -/
def rightMap (a h : ℕ) (output input : ZIndex a h) : Polynomial K :=
  if input = output then (if MiddleZ a h output.val then 1 else X) else 0

/-- One simultaneous polynomial (K := K) restriction (K := K) of the whole source (K := K) tensor. -/
def polynomial (a h : ℕ) :
    Tensor (Polynomial K) (Fin a) (YIndex a h) (ZIndex a h) :=
  Tensor.restrict (leftMap (K := K) a) (middleMap (K := K) a h) (rightMap (K := K) a h)
    (fun i j k => C (source (K := K) a h i j k))

theorem polynomial_apply (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial (K := K) a h i j k =
      (if MiddleY a h j.val then X else 1) *
      (if MiddleZ a h k.val then 1 else X) * C (source (K := K) a h i j k) := by
  simp [polynomial, Tensor.restrict, leftMap, middleMap, rightMap, ite_mul, mul_ite]

/-- The shifted polynomial (K := K) restriction (K := K) has precisely two possible degrees. -/
theorem polynomial_identity (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial (K := K) a h i j k =
      X * C (retained (K := K) a h i j k) + X ^ 2 * C (erased (K := K) a h i j k) := by
  by_cases hs : source (K := K) a h i j k = 0
  · simp [polynomial_apply, retained, erased, hs]
  · have hsupport := (source_ne_zero_iff i j k).mp hs
    have hmiddle := middleY_of_middleZ hsupport
    by_cases hy : MiddleY a h j.val <;> by_cases hz : MiddleZ a h k.val
    all_goals
      simp_all [polynomial_apply, retained, erased, totalWeight, firstWeight,
        secondWeight, thirdWeight, pow_two]

theorem polynomial_eq_X_mul_normalized (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial (K := K) a h i j k = X * normalizedPolynomial (K := K) a h i j k := by
  rw [polynomial_identity, normalizedPolynomial]
  ring

theorem polynomial_coeff (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (n : ℕ) :
    (polynomial (K := K) a h i j k).coeff n =
      (if n = 1 then retained (K := K) a h i j k else 0) +
      (if n = 2 then erased (K := K) a h i j k else 0) := by
  rw [polynomial_identity, Polynomial.coeff_add,
    mul_comm X (C (retained (K := K) a h i j k)),
    mul_comm (X ^ 2) (C (erased (K := K) a h i j k)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem leftMap_degree (a : ℕ) (output input : Fin a) :
    (leftMap (K := K) a output input).degree ≤ 0 := by
  by_cases heq : input = output <;> simp [leftMap, heq]

theorem middleMap_degree (a h : ℕ) (output input : YIndex a h) :
    (middleMap (K := K) a h output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hy : MiddleY a h output.val <;>
    simp [middleMap, heq, hy]

theorem rightMap_degree (a h : ℕ) (output input : ZIndex a h) :
    (rightMap (K := K) a h output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hz : MiddleZ a h output.val <;>
    simp [rightMap, heq, hz]

/-- The three-sector construction is an actual polynomial (K := K) restriction
degeneration in the existing tensor API, with leading order one. -/
def restriction (a h : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (source (K := K) a h) (retained (K := K) a h) 1 0 1 1 where
  leftMap := leftMap (K := K) a
  middleMap := middleMap (K := K) a h
  rightMap := rightMap (K := K) a h
  left_degree := leftMap_degree a
  middle_degree := middleMap_degree a h
  right_degree := rightMap_degree a h
  vanishes := by
    intro i j k n hn
    change (polynomial (K := K) a h i j k).coeff n = 0
    rw [polynomial_coeff]
    have hn0 : n = 0 := by omega
    simp [hn0]
  leading := by
    intro i j k
    change (polynomial (K := K) a h i j k).coeff 1 = retained (K := K) a h i j k
    simp [polynomial_coeff]

@[simp] theorem restriction_basePolynomial (a h : ℕ) :
    (restriction (K := K) a h).basePolynomial = polynomial (K := K) a h := rfl

/-- Evaluation of the normalized family has exactly the paper's form. -/
theorem normalizedPolynomial_eval (a h : ℕ) (t : K) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) :
    (normalizedPolynomial (K := K) a h i j k).eval t =
      retained (K := K) a h i j k + t * erased (K := K) a h i j k := by
  simp only [normalizedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-- At nonzero parameters, the unshifted normalized polynomial (K := K) is still an
ordinary restriction: divide the first local map by the parameter. -/
theorem normalizedPolynomial_eval_restriction (a h : ℕ) (t : K) (ht : t ≠ 0) :
    (fun i j k => (normalizedPolynomial (K := K) a h i j k).eval t) =
      Tensor.restrict
        (fun output input => if input = output then t⁻¹ else 0)
        (fun output input => (middleMap (K := K) a h output input).eval t)
        (fun output input => (rightMap (K := K) a h output input).eval t)
        (source (K := K) a h) := by
  funext i j k
  have hev := congrArg (fun p : Polynomial K => p.eval t)
    (polynomial_eq_X_mul_normalized a h i j k)
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hev
  have hscaled :
      Tensor.restrict
          (fun output input => if input = output then t⁻¹ else 0)
          (fun output input => (middleMap (K := K) a h output input).eval t)
          (fun output input => (rightMap (K := K) a h output input).eval t)
          (source (K := K) a h) i j k = t⁻¹ * (polynomial (K := K) a h i j k).eval t := by
    rw [polynomial_apply]
    simp only [middleMap, rightMap, apply_ite, Polynomial.eval_zero,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
    simp [Tensor.restrict, ite_mul, mul_ite, mul_assoc]
  rw [hscaled, hev, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]

/-- Existing interpolation gives a rank bound with only linear overhead after
tensor powering. -/
theorem retained_power_rankAtMost [Infinite K] (a h r n : ℕ)
    (hsource : Tensor.RankAtMost (source (K := K) a h) r) :
    Tensor.RankAtMost (Tensor.power (retained (K := K) a h) n) ((2 * n + 1) * r ^ n) := by
  simpa using restrictionDegeneration_power_rankAtMost (restriction (K := K) a h) hsource n

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI

end Module1



end AllFieldsModule23
/- END all-fields module GenericSectorAlgebra -/

/- BEGIN all-fields module GenericSectorBranches -/
section AllFieldsModule24
set_option autoImplicit false
namespace OAI
variable {K : Type*} [Field K] [IsAlgClosed K]

/-!
# Coordinate identifications of the three retained sectors

Each outer branch is a zero extension of `C(a,h)`, using the same first-leg
coordinates. The middle branch is a zero extension after reversing the first
coordinate and exchanging the second and third tensor legs.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped Classical


namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- Embed the left second-leg interval. -/
def leftY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨r.val, by have hr := r.isLt; unfold sourceWidth; omega⟩

/-- Embed the left third-leg interval. -/
def leftZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨s.val, by have hs := s.isLt; unfold sourceWidth; omega⟩

/-- Embed the middle second-leg interval, which carries the convolution (K := K) output. -/
def middleY (a h : ℕ) (s : Fin (a + h - 1)) : YIndex a h :=
  ⟨h + s.val, by have hs := s.isLt; unfold sourceWidth; omega⟩

/-- Embed the middle third-leg interval, which carries the second input. -/
def middleZ (a h : ℕ) (r : Fin h) : ZIndex a h :=
  ⟨h + a - 1 + r.val, by have hr := r.isLt; unfold sourceWidth; omega⟩

/-- Embed the right second-leg interval. -/
def rightY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨rightStart a h + r.val,
    by have hr := r.isLt; unfold rightStart sourceWidth; omega⟩

/-- Embed the right third-leg interval. -/
def rightZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨rightStart a h + s.val,
    by have hs := s.isLt; unfold rightStart sourceWidth; omega⟩

theorem leftY_injective (a h : ℕ) : Function.Injective (leftY a h) := by
  intro r s heq
  apply Fin.ext
  exact congrArg (fun t : YIndex a h => t.val) heq

theorem leftZ_injective (a h : ℕ) : Function.Injective (leftZ a h) := by
  intro r s heq
  apply Fin.ext
  exact congrArg (fun t : ZIndex a h => t.val) heq

theorem middleY_injective (a h : ℕ) : Function.Injective (middleY a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [middleY] at hv
  omega

theorem middleZ_injective (a h : ℕ) : Function.Injective (middleZ a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [middleZ] at hv
  omega

theorem rightY_injective (a h : ℕ) : Function.Injective (rightY a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [rightY] at hv
  omega

theorem rightZ_injective (a h : ℕ) : Function.Injective (rightZ a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [rightZ] at hv
  omega

/-- Pulling back the left block gives ordinary convolution. -/
theorem leftTensor_pullback (a h : ℕ) :
    Tensor.pullback id (leftY a h) (leftZ a h) (leftTensor (K := K) a h) =
      convolution (K := K) a h := by
  funext i r s
  have hb : LeftBranch a h i.val r.val s.val ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hi, hr, hs⟩
      omega
    · intro hs
      exact ⟨i.val, r.val, i.isLt, r.isLt, rfl, rfl, hs.symm⟩
  simp only [Tensor.pullback, leftTensor, leftY, leftZ, id_eq, convolution, hb]

/-- Pulling back the translated right block also gives ordinary convolution. -/
theorem rightTensor_pullback (a h : ℕ) :
    Tensor.pullback id (rightY a h) (rightZ a h) (rightTensor (K := K) a h) =
      convolution (K := K) a h := by
  funext i r s
  have hb : RightBranch a h i.val (rightStart a h + r.val)
      (rightStart a h + s.val) ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hi, hr, hs⟩
      omega
    · intro hs
      refine ⟨i.val, r.val, i.isLt, r.isLt, rfl, rfl, ?_⟩
      omega
  simp only [Tensor.pullback, rightTensor, rightY, rightZ, id_eq, convolution, hb]

/-- Exchange the two outer convolution (K := K) legs while retaining the original input
order in the displayed coefficient equation. -/
def exchangedConvolution (a h : ℕ) :
    Tensor K (Fin a) (Fin (a + h - 1)) (Fin h) :=
  fun i s r => convolution (K := K) a h i r s

/-- The middle branch is exactly convolution (K := K) with its last two legs exchanged;
the first-leg reversal occurs solely in this individual branch identification. -/
theorem middleTensor_pullback (a h : ℕ) :
    Tensor.pullback Fin.rev (middleY a h) (middleZ a h) (middleTensor (K := K) a h) =
      exchangedConvolution (K := K) a h := by
  funext i s r
  have hi := i.isLt
  have hr := r.isLt
  have hb : MiddleBranch a h (a - (i.val + 1)) (h + s.val)
      (h + a - 1 + r.val) ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hx, hy, hz⟩
      omega
    · intro hs
      refine ⟨i.val, r.val, hi, hr, ?_, ?_, rfl⟩ <;> omega
  simp only [Tensor.pullback, middleTensor, middleY, middleZ,
    exchangedConvolution, convolution, Fin.val_rev, hb]

/-- All nonzero left-branch coordinates lie in the displayed embeddings. -/
theorem leftTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : leftTensor (K := K) a h i j k ≠ 0) :
    (∃ r, leftY a h r = j) ∧ (∃ s, leftZ a h s = k) := by
  have hb : LeftBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [leftTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  constructor
  · exact ⟨⟨r, hr⟩, Fin.ext hj.symm⟩
  · exact ⟨⟨u + r, by omega⟩, Fin.ext hk.symm⟩

/-- All nonzero right-branch coordinates lie in the translated embeddings. -/
theorem rightTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : rightTensor (K := K) a h i j k ≠ 0) :
    (∃ r, rightY a h r = j) ∧ (∃ s, rightZ a h s = k) := by
  have hb : RightBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [rightTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  constructor
  · exact ⟨⟨r, hr⟩, Fin.ext hj.symm⟩
  · refine ⟨⟨u + r, by omega⟩, Fin.ext ?_⟩
    dsimp [rightZ]
    omega

/-- All nonzero middle-branch coordinates lie in the exchanged embeddings. -/
theorem middleTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : middleTensor (K := K) a h i j k ≠ 0) :
    (∃ u, Fin.rev u = i) ∧ (∃ s, middleY a h s = j) ∧
      (∃ r, middleZ a h r = k) := by
  have hb : MiddleBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [middleTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  refine ⟨⟨⟨u, hu⟩, Fin.ext ?_⟩, ⟨⟨u + r, by omega⟩, Fin.ext ?_⟩,
    ⟨⟨r, hr⟩, Fin.ext ?_⟩⟩
  · simp only [Fin.val_rev]
    omega
  · dsimp [middleY]
    omega
  · exact hk.symm

/-- The left block is the zero extension of the ordinary convolution (K := K) tensor. -/
theorem leftTensor_eq_extension (a h : ℕ) :
    leftTensor (K := K) a h = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y r => if leftY a h r = y then 1 else 0)
      (fun z s => if leftZ a h s = z then 1 else 0) (convolution (K := K) a h) := by
  have hs (i : Fin a) (j : YIndex a h) (k : ZIndex a h)
      (hn : leftTensor (K := K) a h i j k ≠ 0) :
      i ∈ Set.range (id : Fin a → Fin a) ∧
        j ∈ Set.range (leftY a h) ∧ k ∈ Set.range (leftZ a h) := by
    exact ⟨⟨i, rfl⟩, leftTensor_support a h i j k hn⟩
  classical
  have heq := tensor_eq_extendByZero_pullback (leftTensor (K := K) a h) id (leftY a h) (leftZ a h)
    Function.injective_id (leftY_injective a h) (leftZ_injective a h) hs
  rw [leftTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The right block is the zero extension along the translated coordinates. -/
theorem rightTensor_eq_extension (a h : ℕ) :
    rightTensor (K := K) a h = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y r => if rightY a h r = y then 1 else 0)
      (fun z s => if rightZ a h s = z then 1 else 0) (convolution (K := K) a h) := by
  have hs (i : Fin a) (j : YIndex a h) (k : ZIndex a h)
      (hn : rightTensor (K := K) a h i j k ≠ 0) :
      i ∈ Set.range (id : Fin a → Fin a) ∧
        j ∈ Set.range (rightY a h) ∧ k ∈ Set.range (rightZ a h) := by
    exact ⟨⟨i, rfl⟩, rightTensor_support a h i j k hn⟩
  classical
  have heq := tensor_eq_extendByZero_pullback (rightTensor (K := K) a h) id (rightY a h) (rightZ a h)
    Function.injective_id (rightY_injective a h) (rightZ_injective a h) hs
  rw [rightTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The middle block is the zero extension of the exchanged convolution, with
one reversible change of basis on its first leg. -/
theorem middleTensor_eq_extension (a h : ℕ) :
    middleTensor (K := K) a h = Tensor.restrict
      (fun x i => if Fin.rev i = x then 1 else 0)
      (fun y s => if middleY a h s = y then 1 else 0)
      (fun z r => if middleZ a h r = z then 1 else 0) (exchangedConvolution (K := K) a h) := by
  classical
  have heq := tensor_eq_extendByZero_pullback (middleTensor (K := K) a h) Fin.rev (middleY a h)
    (middleZ a h) Fin.rev_injective (middleY_injective a h) (middleZ_injective a h)
    (middleTensor_support a h)
  rw [middleTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> split_ifs <;> rfl

/-- Every character assigns the left branch the value of `C(a,h)`. -/
theorem value_leftTensor (χ : (Character K)) (a h : ℕ) :
    χ.value (leftTensor (K := K) a h) = χ.value (convolution (K := K) a h) := by
  rw [leftTensor_eq_extension]
  exact χ.value_extendByZero _ id (leftY a h) (leftZ a h) Function.injective_id
    (leftY_injective a h) (leftZ_injective a h)

/-- Translation of the outer coordinates preserves the right-branch value. -/
theorem value_rightTensor (χ : (Character K)) (a h : ℕ) :
    χ.value (rightTensor (K := K) a h) = χ.value (convolution (K := K) a h) := by
  rw [rightTensor_eq_extension]
  exact χ.value_extendByZero _ id (rightY a h) (rightZ a h) Function.injective_id
    (rightY_injective a h) (rightZ_injective a h)

/-- The middle-branch value is the value of the exchanged convolution (K := K) tensor. -/
theorem value_middleTensor (χ : (Character K)) (a h : ℕ) :
    χ.value (middleTensor (K := K) a h) = χ.value (exchangedConvolution (K := K) a h) := by
  rw [middleTensor_eq_extension]
  exact χ.value_extendByZero _ Fin.rev (middleY a h) (middleZ a h)
    Fin.rev_injective (middleY_injective a h) (middleZ_injective a h)

/-- Exchanging two tensor legs preserves nonzeroness. -/
theorem exchangedConvolution_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    exchangedConvolution (K := K) a h ≠ 0 := by
  intro hz
  apply convolution_nonzero (K := K) ha hh
  funext i r s
  exact congrFun (congrFun (congrFun hz i) s) r

/-- The left retained branch is nonzero in every positive size. -/
theorem leftTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    leftTensor (K := K) a h ≠ 0 := by
  intro hz
  have hp := leftTensor_pullback (K := K) a h
  rw [hz] at hp
  exact convolution_nonzero ha hh hp.symm

/-- The translated right branch is nonzero in every positive size. -/
theorem rightTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    rightTensor (K := K) a h ≠ 0 := by
  intro hz
  have hp := rightTensor_pullback (K := K) a h
  rw [hz] at hp
  exact convolution_nonzero ha hh hp.symm

/-- The exchanged middle branch is nonzero in every positive size. -/
theorem middleTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    middleTensor (K := K) a h ≠ 0 := by
  intro hz
  have hp := middleTensor_pullback (K := K) a h
  rw [hz] at hp
  exact exchangedConvolution_nonzero ha hh hp.symm

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI



end AllFieldsModule24
/- END all-fields module GenericSectorBranches -/

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

/-- The actual three retained (K := K) tensors in their original ambient spaces. -/
def branchFamily (a h : ℕ) (b : Fin 3) :
    Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  if b = 0 then leftTensor (K := K) a h else if b = 1 then middleTensor (K := K) a h else rightTensor (K := K) a h

@[simp] theorem branchFamily_zero (a h : ℕ) :
    branchFamily (K := K) a h 0 = leftTensor (K := K) a h := by simp [branchFamily]

@[simp] theorem branchFamily_one (a h : ℕ) :
    branchFamily (K := K) a h 1 = middleTensor (K := K) a h := by simp [branchFamily]

@[simp] theorem branchFamily_two (a h : ℕ) :
    branchFamily (K := K) a h 2 = rightTensor (K := K) a h := by simp [branchFamily]

/-- Label a second-leg coordinate by its interval. -/
def yLabel (a h : ℕ) (j : YIndex a h) : Fin 3 :=
  if j.val < h then 0 else if j.val < rightStart a h then 1 else 2

/-- Label a third-leg coordinate by its corresponding interval. -/
def zLabel (a h : ℕ) (k : ZIndex a h) : Fin 3 :=
  if k.val < h + a - 1 then 0 else if k.val < rightStart a h then 1 else 2

/-- Every nonzero branch coefficient lies in the two matching labelled sectors. -/
theorem branchFamily_labels (a h : ℕ) (b : Fin 3) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) (hn : branchFamily (K := K) a h b i j k ≠ 0) :
    yLabel a h j = b ∧ zLabel a h k = b := by
  fin_cases b
  · have hb : LeftBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, leftTensor, hb])
    have h := (leftBranch_iff hb.support).mp hb
    simp [yLabel, zLabel, h.1, h.2]
  · have hb : MiddleBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, middleTensor, hb])
    rcases (middleBranch_iff hb.support).mp hb with ⟨⟨hy₀, hy₁⟩, ⟨hz₀, hz₁⟩⟩
    simp [yLabel, zLabel, not_lt.mpr hy₀, hy₁, not_lt.mpr hz₀, hz₁]
  · have hb : RightBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, rightTensor, hb])
    rcases (rightBranch_iff hb.support).mp hb with ⟨hy, hz⟩
    have hi := i.isLt
    have hy₀ : h ≤ j.val := by unfold rightStart at hy; omega
    have hz₀ : h + a - 1 ≤ k.val := by unfold rightStart at hz; omega
    simp [yLabel, zLabel, not_lt.mpr hy₀, not_lt.mpr hy,
      not_lt.mpr hz₀, not_lt.mpr hz]

/-- The branch family sums to exactly the retained (K := K) tensor. -/
theorem sum_branchFamily (a h : ℕ) :
    (∑ b : Fin 3, branchFamily (K := K) a h b) = retained (K := K) a h := by
  simp only [Fin.sum_univ_three, branchFamily_zero, branchFamily_one, branchFamily_two]
  exact (retained_eq_three_branches a h).symm

/-- The character comparison uses the actual polynomial degeneration. -/
theorem value_retained_le_source (χ : (Character K)) (a h : ℕ) :
    χ.value (retained (K := K) a h) ≤ χ.value (source (K := K) a h) :=
  χ.value_polynomialRestrictionDegeneration_le (restriction (K := K) a h)

/-- Both interval labels can be recovered without changing the common first
input, so the tagged branch tensor has precisely the retained (K := K) tensor's value. -/
theorem value_sharedFirst_branchFamily (χ : (Character K)) (a h : ℕ) :
    χ.value (sharedFirstTensor (branchFamily (K := K) a h)) = χ.value (retained (K := K) a h) := by
  rw [χ.value_sharedFirstTensor_eq_sum (branchFamily (K := K) a h)
    (yLabel a h) (zLabel a h) (branchFamily_labels a h), sum_branchFamily]

theorem branchFamily_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h)
    (b : Fin 3) : branchFamily (K := K) a h b ≠ 0 := by
  fin_cases b
  · simpa [branchFamily] using leftTensor_nonzero ha hh
  · simpa [branchFamily] using middleTensor_nonzero ha hh
  · simpa [branchFamily] using rightTensor_nonzero ha hh

/-- The uniform branch product combines the two outer convolution (K := K) values. -/
theorem uniform_branchFamily_product (χ : (Character K)) (a h : ℕ)
    (ha : 0 < a) (hh : 0 < h) :
    (∏ b, χ.value (branchFamily (K := K) a h b) ^ (FiniteLaw.uniform (Fin 3)).mass b) =
      χ.value (convolution (K := K) a h) ^ (2 / 3 : ℝ) *
        χ.value (exchangedConvolution (K := K) a h) ^ (1 / 3 : ℝ) := by
  rw [uniformThree_product]
  simp only [branchFamily_zero, branchFamily_one, branchFamily_two,
    value_leftTensor, value_middleTensor, value_rightTensor]
  have hc : 0 < χ.value (convolution (K := K) a h) :=
    lt_of_lt_of_le zero_lt_one (χ.one_le_value (convolution_nonzero ha hh))
  calc
    χ.value (convolution (K := K) a h) ^ (1 / 3 : ℝ) *
        χ.value (exchangedConvolution (K := K) a h) ^ (1 / 3 : ℝ) *
        χ.value (convolution (K := K) a h) ^ (1 / 3 : ℝ) =
      (χ.value (convolution (K := K) a h) ^ (1 / 3 : ℝ) *
        χ.value (convolution (K := K) a h) ^ (1 / 3 : ℝ)) *
          χ.value (exchangedConvolution (K := K) a h) ^ (1 / 3 : ℝ) := by ring
    _ = _ := by
      rw [← Real.rpow_add hc]
      norm_num

/-- The per-character three-sector inequality, before multiplication over
the six tensor-leg permutations. All tensor values are actual convolution
values, with only the middle branch exchanging its last two legs. -/
theorem convolution_tripling_tag (χ : (Character K)) (a h : ℕ)
    (ha : 0 < a) (hh : 0 < h) :
    (3 : ℝ) ^ χ.pX * χ.value (convolution (K := K) a h) ^ (2 / 3 : ℝ) *
      χ.value (fun i s r => convolution (K := K) a h i r s) ^ (1 / 3 : ℝ) ≤
        χ.value (convolution (K := K) a (3 * h + a - 1)) := by
  have htag := χ.sharedFirst_tag (FiniteLaw.uniform (Fin 3))
    (branchFamily (K := K) a h) (branchFamily_nonzero ha hh)
  rw [uniformThree_entropy_factor, uniform_branchFamily_product χ a h ha hh,
    value_sharedFirst_branchFamily] at htag
  have hresult := htag.trans (value_retained_le_source χ a h)
  change (3 : ℝ) ^ χ.pX * (χ.value (convolution (K := K) a h) ^ (2 / 3 : ℝ) *
    χ.value (fun i s r => convolution (K := K) a h i r s) ^ (1 / 3 : ℝ)) ≤
      χ.value (convolution (K := K) a (3 * h + a - 1)) at hresult
  simpa only [mul_assoc] using hresult

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI



end AllFieldsModule25
/- END all-fields module GenericSectorCharacter -/

/- BEGIN all-fields module GenericBound -/
section AllFieldsModule26


section BoundModule0

namespace OAI

/-!
# The inequalities for the polynomial profile

The six character values are combined before the common probability law is
optimized. Each first-leg exponent occurs twice, so the total entropy exponent
is exactly six times the mean exponent used to normalize the profile.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

variable (χ : (Character 𝕜))

/-- All six permuted characters have the same mean singleton-leg exponent. -/
theorem permutedCharacter_meanExponent (i : Fin 6) :
    (χ.permutedCharacter i).meanExponent = χ.meanExponent := by
  fin_cases i <;> simp [permutedCharacter, meanExponent] <;> ring

/-- The exponents of the six permuted characters have the normalization total. -/
theorem sum_permutedCharacter_pX_mean :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 6 * χ.meanExponent := by
  rw [χ.sum_permutedCharacter_pX]
  unfold meanExponent
  ring

/-- All six factors associated to a positive-size polynomial tensor are positive. -/
theorem permutedCharacter_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (i : Fin 6) : 0 < (χ.permutedCharacter i).value (convolution a b) :=
  (χ.permutedCharacter i).value_convolution_pos ha hb

/-- Exchanging the two output-side positions reorders the six convolution factors. -/
theorem prod_permutedCharacter_swapped_convolution (a b : ℕ) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value
      (fun x z y => convolution a b x y z)) =
    ∏ i : Fin 6, (χ.permutedCharacter i).value (convolution a b) := by
  rw [χ.prod_permutedCharacter_value, χ.prod_permutedCharacter_value]
  exact χ.sixfoldProduct_swap23 _

/-- The actual polynomial profile is concave in its second positive index. -/
theorem convolutionProfile_concave {a b : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hb : 2 ≤ b) :
    χ.convolutionProfile a (b - 1) + χ.convolutionProfile a (b + 1) ≤
      2 * χ.convolutionProfile a b := by
  have h := finite_product_concavity
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a b))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a (b + 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a (b - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) χ.sum_permutedCharacter_pX_mean
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i q hq₀ hq₁ =>
      (χ.permutedCharacter i).convolution_concavity_tag a b ha hb q hq₀ hq₁)
  simp only [χ.prod_permutedCharacter_value] at h
  change χ.convolutionProfile a (b + 1) + χ.convolutionProfile a (b - 1) ≤
    2 * χ.convolutionProfile a b at h
  simpa only [add_comm] using h

/-- The actual three-sector degeneration triples the normalized profile. -/
theorem convolutionProfile_tripling {a h : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hh : 0 < h) :
    3 * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3 * h + a - 1) := by
  have hsw : (fun i s r => convolution (K := 𝕜) a h i r s) ≠ 0 := by
    intro hz
    apply convolution_nonzero (K := 𝕜) ha hh
    exact congrArg
      (fun T : Tensor 𝕜 (Fin a) (Fin (a + h - 1)) (Fin h) => fun i j k => T i k j) hz
  have h := finite_product_tripling
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a (3 * h + a - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a h))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (fun x z y => convolution a h x y z))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) χ.sum_permutedCharacter_pX_mean
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha hh i)
    (fun i => (χ.permutedCharacter i).value_pos hsw)
    (fun i => Sector.convolution_tripling_tag (χ.permutedCharacter i) a h ha hh)
    (χ.prod_permutedCharacter_swapped_convolution a h)
  simpa only [χ.prod_permutedCharacter_value, convolutionProfile, symmetrizedProfile] using h

/-- The polynomial profile satisfies every hypothesis of the scalar growth theorem. -/
def toScalarProfile (ht : 0 < χ.meanExponent) : ScalarProfile χ.meanExponent where
  value := χ.convolutionProfile
  positive a b ha hb := χ.convolutionProfile_pos (by omega) (by omega)
  symmetric a b _ _ := χ.convolutionProfile_comm a b
  boundary b hb := χ.convolutionProfile_one_left ht (by omega)
  concave a b ha hb := χ.convolutionProfile_concave ht (by omega) hb
  tripling a h ha hh := χ.convolutionProfile_tripling ht (by omega) (by omega)
  rank_bound a b ha hb := by
    have h := χ.convolutionProfile_le (a := a) (b := b) ht
    have hab : 1 ≤ a + b := by omega
    simpa only [Nat.cast_sub hab, Nat.cast_add, Nat.cast_one] using h

/-- Every actual tensor character has mean singleton-leg exponent at most `3/4`. -/
theorem meanExponent_le_three_quarters : χ.meanExponent ≤ 3 / 4 := by
  by_cases ht : 0 < χ.meanExponent
  · exact (χ.toScalarProfile ht).exponent_le_three_quarters ht
  · have hle : χ.meanExponent ≤ 0 := le_of_not_gt ht
    linarith

/-- The three dot-product exponents of an actual character sum to at most `9/4`. -/
theorem exponent_sum_le_nine_quarters : χ.pX + χ.pY + χ.pZ ≤ 9 / 4 := by
  have h := χ.meanExponent_le_three_quarters
  unfold meanExponent at h
  linarith

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end BoundModule0


section BoundModule1

namespace OAI

/-!
# Integer rounding in the detecting-character argument

The character used at a matrix size may depend on that size. A uniform bound
on all those characters is enough: the loss of one in rounding their target
values cannot change a positive power exponent. The character-existence and
character-growth assumptions remain explicit in the final implications.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

open MatrixMultiplication.Foundation

/-- Rounding strictly down works at integers too: use `ceil x - 1`. -/
theorem exists_nat_sub_one_le_lt {x : ℝ} (hx : 0 < x) :
    ∃ k : ℕ, x - 1 ≤ (k : ℝ) ∧ (k : ℝ) < x := by
  have hc : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
  refine ⟨⌈x⌉₊ - 1, ?_, ?_⟩
  · rw [Nat.cast_sub hc]
    norm_num only [Nat.cast_one]
    linarith [Nat.le_ceil x]
  · exact ((Nat.ceil_eq_iff (by omega : ⌈x⌉₊ ≠ 0)).1 rfl).1

/-- An additive loss of one does not affect a comparison to a nonnegative
power exponent. No sign assumption on the exponent on the left is needed. -/
theorem rpow_exponent_le_of_nat_sub_one_bound {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hbound : ∀ d : ℕ, 2 ≤ d → (d : ℝ) ^ ν - 1 ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  by_cases hd2 : 2 ≤ d
  · have h := hbound d hd2
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hpow : 1 ≤ (d : ℝ) ^ τ := Real.one_le_rpow hdreal hτ
    linarith
  · have hd1 : d = 1 := by omega
    simp [hd1]

/-- The integer witnesses in the final rounding argument can vary with `d`. -/
theorem exponent_le_of_integer_rounding {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hround : ∀ d : ℕ, 2 ≤ d →
      ∃ k : ℕ, (d : ℝ) ^ ν - 1 ≤ k ∧ (k : ℝ) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_sub_one_bound hτ
  intro d hd
  obtain ⟨k, hk, hk'⟩ := hround d hd
  exact hk.trans hk'

/-- A positive exponent on the left makes the target exponent nonnegative
automatically, so it is an alternative to that hypothesis above. -/
theorem exponent_le_of_integer_rounding_of_pos {ν τ : ℝ} (hν : 0 < ν)
    (hround : ∀ d : ℕ, 2 ≤ d →
      ∃ k : ℕ, (d : ℝ) ^ ν - 1 ≤ k ∧ (k : ℝ) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  have hτ : 0 ≤ τ := by
    by_contra hneg
    obtain ⟨k, hk, hk'⟩ := hround 2 le_rfl
    norm_num only [Nat.cast_ofNat] at hk hk'
    have hpτ : (2 : ℝ) ^ τ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (lt_of_not_ge hneg)
    have hklt : (k : ℝ) < 1 := hk'.trans_lt hpτ
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast hklt
      omega
    rw [hk0, Nat.cast_zero] at hk
    have hpν : 1 < (2 : ℝ) ^ ν := Real.one_lt_rpow (by norm_num) hν
    linarith
  exact exponent_le_of_integer_rounding hτ hround

/-- Explicitly conditional passage from detecting characters to the exponent
bound. The detecting character is allowed to depend on both `d` and `k`. -/
theorem exponent_le_of_detecting_characters {ν τ : ℝ} (hτ : 0 ≤ τ)
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, (k : ℝ) < (d : ℝ) ^ ν →
      ∃ χ : (Character 𝕜), (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d))
    (bound : ∀ χ : (Character 𝕜), ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matrixMultiplication d d d) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply exponent_le_of_integer_rounding hτ
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨k, hk, hk'⟩ :=
    exists_nat_sub_one_le_lt (Real.rpow_pos_of_pos hdpos ν)
  obtain ⟨χ, hχ⟩ := detect d hd k hk'
  exact ⟨k, hk, hχ.trans (bound χ d hd)⟩

/-- The character growth bound can be supplied as a uniform bound on its
exponent sum, together with the matrix-value identity. -/
theorem exponent_le_of_detecting_character_exponents {ν τ : ℝ} (hτ : 0 ≤ τ)
    (exponentSum : (Character 𝕜) → ℝ)
    (value : ∀ χ : (Character 𝕜), ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matrixMultiplication d d d) = (d : ℝ) ^ exponentSum χ)
    (upper : ∀ χ : (Character 𝕜), exponentSum χ ≤ τ)
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, (k : ℝ) < (d : ℝ) ^ ν →
      ∃ χ : (Character 𝕜), (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d)) :
    ν ≤ τ := by
  apply exponent_le_of_detecting_characters hτ detect
  intro χ d hd
  rw [value χ d hd]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ d by omega))
    (upper χ)

/-- The paper's final `ν ≤ 9/4` implication, with its two substantive character
inputs visible rather than incorporated into the definition of `ν`. -/
theorem exactRankExponent_le_nine_quarters_of_characters
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ,
      (k : ℝ) < (d : ℝ) ^ (exactRankExponent 𝕜) →
      ∃ χ : (Character 𝕜), (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d))
    (bound : ∀ χ : (Character 𝕜), ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matrixMultiplication d d d) ≤ (d : ℝ) ^ (9 / 4 : ℝ)) :
    (exactRankExponent 𝕜) ≤ 9 / 4 :=
  exponent_le_of_detecting_characters (by norm_num) detect bound

end MatrixMultiplication.AuxiliarySeparation

end OAI

end BoundModule1


section BoundModule2

namespace OAI

/-!
# The exact-rank exponent bound

Detecting characters exist by Appendix A. The determinant and three-sector
polynomial constructions bound the sum of their dot-product exponents by
`9/4`. Integer rounding then gives the same bound for the exact-rank exponent.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]

/-- The polynomial inequalities bound the actual exact-rank exponent. -/
theorem exactRankExponent_le_nine_quarters : (exactRankExponent 𝕜) ≤ (9 : ℝ) / 4 := by
  apply exactRankExponent_le_nine_quarters_of_characters
  · intro d hd k hk
    exact exists_detecting_character hd hk
  · intro χ d hd
    rw [χ.value_matrixMultiplication (by omega)]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ d by omega)) χ.exponent_sum_le_nine_quarters

end MatrixMultiplication.AuxiliarySeparation

end OAI

end BoundModule2




end AllFieldsModule26
/- END all-fields module GenericBound -/











/- BEGIN all-fields module FiniteRankDescent -/
section AllFieldsModule37

/-!
Finite-extension descent for the exact coefficient-tensor rank used by OAI.
The square of the extension degree is an overhead independent of tensor size.
This lemma alone does not establish the all-fields 9/4 exponent theorem.
-/

noncomputable section
open scoped BigOperators

namespace OAI.MatrixMultiplication.Foundation.Tensor

variable {K E X Y Z I : Type*} [Field K] [Field E] [Algebra K E]
variable [Fintype I]

theorem linear_projection_triple_product
    (b : Module.Basis I K E) (π : E →ₗ[K] K) (a c d : E) :
    π (a * c * d) = ∑ i, ∑ j,
      b.repr a i * b.repr c j * π (b i * b j * d) := by
  conv_lhs => rw [← b.sum_repr a, ← b.sum_repr c]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc,
    mul_smul_comm, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring

theorem RankAtMost.descend_with_projection
    (b : Module.Basis I K E) (π : E →ₗ[K] K) (hπ : π 1 = 1)
    {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost (fun x y z => algebraMap K E (T x y z)) r) :
    RankAtMost T (Fintype.card I * Fintype.card I * r) := by
  classical
  rcases h with ⟨a, c, d, ht⟩
  let aa : (I × I × Fin r) → X → K := fun s x => b.repr (a s.2.2 x) s.1
  let bb : (I × I × Fin r) → Y → K := fun s y => b.repr (c s.2.2 y) s.2.1
  let cc : (I × I × Fin r) → Z → K := fun s z =>
    π (b s.1 * b s.2.1 * d s.2.2 z)
  have heq : T = fun x y z => ∑ s, rankOne (aa s) (bb s) (cc s) x y z := by
    funext x y z
    have hp (t : K) : π (algebraMap K E t) = t := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]
    rw [← hp (T x y z)]
    have hxyz := congrFun (congrFun (congrFun ht x) y) z
    rw [hxyz, map_sum]
    calc
      (∑ t : Fin r, π (rankOne (a t) (c t) (d t) x y z)) =
          ∑ t : Fin r, ∑ i : I, ∑ j : I,
            b.repr (a t x) i * b.repr (c t y) j * π (b i * b j * d t z) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact linear_projection_triple_product b π (a t x) (c t y) (d t z)
      _ = _ := by
        simp only [rankOne, Fintype.sum_prod_type, aa, bb, cc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
  rw [heq]
  convert rankAtMost_sum_rankOne aa bb cc using 1
  simp [Fintype.card_prod, Nat.mul_assoc]

theorem RankAtMost.descend [FiniteDimensional K E]
    {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost (fun x y z => algebraMap K E (T x y z)) r) :
    RankAtMost T (Module.finrank K E ^ 2 * r) := by
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : E) ≠ 0)
  simpa only [Fintype.card_fin, pow_two] using
    h.descend_with_projection (Module.finBasis K E) π hπ


end OAI.MatrixMultiplication.Foundation.Tensor

end

end AllFieldsModule37
/- END all-fields module FiniteRankDescent -/

/- BEGIN all-fields module AlgebraicRankDescent -/
section AllFieldsModule38

set_option autoImplicit false

noncomputable section

open scoped BigOperators Topology
open Filter

namespace OAI.MatrixMultiplication.Foundation.Tensor

variable {K E X Y Z : Type*} [Field K] [Field E] [Algebra K E]

theorem exists_finite_coefficient_field [Algebra.IsAlgebraic K E]
    {ι : Type*} [Finite ι] (c : ι → E) :
    ∃ L : IntermediateField K E, FiniteDimensional K L ∧ ∀ i, c i ∈ L := by
  let S : Set E := Set.range c
  letI : Finite S := (Set.finite_range c).to_subtype
  refine ⟨IntermediateField.adjoin K S, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  · intro i
    exact IntermediateField.subset_adjoin K S ⟨i, rfl⟩

/-- A finite rank witness in an algebraic extension uses one finite coefficient field. -/
theorem RankAtMost.exists_finite_intermediateField
    [Algebra.IsAlgebraic K E] [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost (fun x y z => algebraMap K E (T x y z)) r) :
    ∃ L : IntermediateField K E, FiniteDimensional K L ∧
      RankAtMost (fun x y z => algebraMap K L (T x y z)) r := by
  classical
  rcases h with ⟨a, b, c, hT⟩
  let coeff : Fin r × (X ⊕ Y ⊕ Z) → E := fun p =>
    match p.2 with
    | .inl x => a p.1 x
    | .inr (.inl y) => b p.1 y
    | .inr (.inr z) => c p.1 z
  obtain ⟨L, hfinite, hcoeff⟩ := exists_finite_coefficient_field (K := K) coeff
  let aa : Fin r → X → L := fun i x => ⟨a i x, hcoeff (i, .inl x)⟩
  let bb : Fin r → Y → L := fun i y => ⟨b i y, hcoeff (i, .inr (.inl y))⟩
  let cc : Fin r → Z → L := fun i z => ⟨c i z, hcoeff (i, .inr (.inr z))⟩
  refine ⟨L, hfinite, aa, bb, cc, ?_⟩
  funext x y z
  apply (algebraMap L E).injective
  calc
    algebraMap L E (algebraMap K L (T x y z)) = algebraMap K E (T x y z) :=
      rfl
    _ = ∑ i, a i x * b i y * c i z :=
      congrFun (congrFun (congrFun hT x) y) z
    _ = algebraMap L E (∑ i, rankOne (aa i) (bb i) (cc i) x y z) := by
      simp [rankOne, aa, bb, cc]

omit [Algebra K E] in
theorem map_matrixMultiplication (f : K →+* E) (a b c : ℕ) :
    (fun x y z => f (matrixMultiplication (K := K) a b c x y z)) =
      matrixMultiplication (K := E) a b c := by
  funext x y z
  simp only [matrixMultiplication]
  split_ifs <;> simp

/-- Tensor powers of one matrix decomposition multiply the block sizes. -/
theorem RankAtMost.matrixMultiplication_power {n r : ℕ}
    (h : RankAtMost (matrixMultiplication (K := K) n n n) r) (t : ℕ) :
    RankAtMost (matrixMultiplication (K := K) (n ^ t) (n ^ t) (n ^ t)) (r ^ t) := by
  classical
  let e : Fin (n ^ t) ≃ (Fin t → Fin n) := Fintype.equivOfCardEq (by simp)
  let f : (Fin (n ^ t) × Fin (n ^ t)) → (Fin t → Fin n × Fin n) :=
    fun x i => (e x.1 i, e x.2 i)
  have hp := (h.power t).pullback f f f
  have heq : Tensor.pullback f f f (Tensor.power (matrixMultiplication (K := K) n n n) t) =
      matrixMultiplication (K := K) (n ^ t) (n ^ t) (n ^ t) := by
    funext x y z
    change Tensor.power (matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n)) t
      (fun i => (e x.1 i, e x.2 i))
      (fun i => (e y.1 i, e y.2 i))
      (fun i => (e z.1 i, e z.2 i)) = _
    rw [matrixCoefficients_power t (e x.1, e x.2) (e y.1, e y.2) (e z.1, e z.2)]
    simp only [matrixCoefficients, matrixMultiplication, e.injective.eq_iff]
  rw [heq] at hp
  exact hp

/- The same finite extension is used for every tensor power. -/
set_option backward.isDefEq.respectTransparency false in
theorem RankAtMost.algebraic_power_descent
    [Algebra.IsAlgebraic K E] {n r : ℕ}
    (h : RankAtMost (matrixMultiplication (K := E) n n n) r) :
    ∃ C : ℕ, ∀ t : ℕ,
      RankAtMost (matrixMultiplication (K := K) (n ^ t) (n ^ t) (n ^ t))
        (C * r ^ t) := by
  have hmap : RankAtMost
      (fun x y z => algebraMap K E (matrixMultiplication (K := K) n n n x y z)) r := by
    simpa only [map_matrixMultiplication] using h
  obtain ⟨L, hfinite, hL⟩ := hmap.exists_finite_intermediateField
  letI : FiniteDimensional K L := hfinite
  have hL' : RankAtMost (matrixMultiplication (K := L) n n n) r := by
    simpa only [map_matrixMultiplication] using hL
  refine ⟨Module.finrank K L ^ 2, ?_⟩
  intro t
  have hp : RankAtMost (fun x y z =>
      algebraMap K L (matrixMultiplication (K := K) (n ^ t) (n ^ t) (n ^ t) x y z))
        (r ^ t) := by
    simpa only [map_matrixMultiplication] using hL'.matrixMultiplication_power t
  exact hp.descend

end OAI.MatrixMultiplication.Foundation.Tensor

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open OAI.MatrixMultiplication.Foundation

/-- A fixed multiplicative overhead disappears from an exponential growth rate. -/
theorem le_of_forall_pow_le_constant_mul_pow {a r C : ℝ}
    (hr : 0 ≤ r) (h : ∀ n : ℕ, 0 < n → a ^ n ≤ C * r ^ n) :
    a ≤ r := by
  by_contra hnot
  have hra : r < a := lt_of_not_ge hnot
  have ha : 0 < a := hr.trans_lt hra
  have hratio : 0 ≤ r / a := div_nonneg hr ha.le
  have hratio_one : r / a < 1 := (div_lt_one ha).2 hra
  have hlim : Tendsto (fun n : ℕ => C * (r / a) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio_one).const_mul C
  have hsmall := hlim.eventually_lt_const (show (0 : ℝ) < 1 from zero_lt_one)
  have hbound : ∀ᶠ n : ℕ in atTop, a ^ n ≤ C * r ^ n :=
    eventually_atTop.2 ⟨1, fun n hn => h n (Nat.zero_lt_one.trans_le hn)⟩
  obtain ⟨n, hn, hlt⟩ := (hbound.and hsmall).exists
  have hge : (1 : ℝ) ≤ C * (r / a) ^ n := by
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos ha n)).2 (by simpa only [one_mul] using hn)
  exact (not_lt_of_ge hge) hlt

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem exactRankExponent_rpow_le_of_algebraic_rank
    [Algebra.IsAlgebraic K E] {n r : ℕ} (hn : 2 ≤ n)
    (h : Tensor.RankAtMost (Tensor.matrixMultiplication (K := E) n n n) r) :
    (n : ℝ) ^ exactRankExponent K ≤ (r : ℝ) := by
  obtain ⟨C, hC⟩ := h.algebraic_power_descent (K := K)
  apply le_of_forall_pow_le_constant_mul_pow (Nat.cast_nonneg r) (C := (C : ℝ))
  intro t ht
  have hnt : 2 ≤ n ^ t := hn.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have hlower := exactMatrixRank_rpow_lower (K := K) hnt
  have hupper : exactMatrixRank K (n ^ t) ≤ C * r ^ t := exactRank_le (hC t)
  have hbound := hlower.trans (Nat.cast_le.mpr hupper)
  simpa only [Nat.cast_mul, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg n)]
    using hbound

theorem exactRankExponent_le_logb_of_algebraic_rank
    [Algebra.IsAlgebraic K E] {n r : ℕ} (hn : 2 ≤ n)
    (h : Tensor.RankAtMost (Tensor.matrixMultiplication (K := E) n n n) r) :
    exactRankExponent K ≤ Real.logb (n : ℝ) (r : ℝ) := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hrnat : 0 < r :=
    (pow_pos (show 0 < n by omega) 2).trans_le
      (matrixMultiplication_rank_lower (K := E) (by omega) h)
  have hr : 0 < (r : ℝ) := by exact_mod_cast hrnat
  exact (Real.le_logb_iff_rpow_le hn1 hr).mpr
    (exactRankExponent_rpow_le_of_algebraic_rank (K := K) hn h)

/-- Algebraic field extensions do not lower the base field's asymptotic rank exponent. -/
theorem exactRankExponent_le_of_isAlgebraic [Algebra.IsAlgebraic K E] :
    exactRankExponent K ≤ exactRankExponent E := by
  apply le_csInf (exactRankExponentSet_nonempty (K := E))
  rintro τ ⟨n, hn, rfl⟩
  exact exactRankExponent_le_logb_of_algebraic_rank (K := K) hn
    (exactMatrixRank_spec (K := E) n)

theorem exactRankExponent_le_algebraicClosure :
    exactRankExponent K ≤ exactRankExponent (AlgebraicClosure K) :=
  exactRankExponent_le_of_isAlgebraic

theorem exactRankExponent_bound_of_algebraicClosure {τ : ℝ}
    (h : exactRankExponent (AlgebraicClosure K) ≤ τ) :
    exactRankExponent K ≤ τ :=
  exactRankExponent_le_algebraicClosure.trans h


end OAI.MatrixMultiplication.AuxiliarySeparation

end

end AllFieldsModule38
/- END all-fields module AlgebraicRankDescent -/


/- BEGIN all-fields module AllFields -/
section AllFieldsModule40

/-!
Matrix multiplication has exact tensor-rank exponent at most 9/4 over every field.
The algebraically closed construction uses a characteristic-safe Fourier period;
algebraic descent gives the same rank exponent bound over the base field.
-/

set_option autoImplicit false

namespace OAI.MatrixMultiplication

/-- The exact tensor-rank exponent is at most nine quarters in every characteristic. -/
theorem AuxiliarySeparation.exactRankExponent_le_nine_quarters_allFields
    (K : Type*) [Field K] : AuxiliarySeparation.exactRankExponent K ≤ (9 : ℝ) / 4 :=
  AuxiliarySeparation.exactRankExponent_bound_of_algebraicClosure
    (AuxiliarySeparation.exactRankExponent_le_nine_quarters
      (𝕜 := AlgebraicClosure K))


end OAI.MatrixMultiplication




end AllFieldsModule40
/- END all-fields module AllFields -/


section CampaignBridge

set_option maxHeartbeats 200000
universe u
noncomputable section
open PiTensorProduct BigOperators Module
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

namespace MMEBridge
variable {K : Type u} [Field K]

def mmBasis (K : Type u) [Field K] (n : ℕ) :
    ∀ s : Fin 3, Basis (Fin n × Fin n) K (MME.MMSpace K n n n s)
  | ⟨0, _⟩ => Pi.basisFun K _
  | ⟨1, _⟩ => Pi.basisFun K _
  | ⟨2, _⟩ => Pi.basisFun K _

def mmTensorBasis (K : Type u) [Field K] (n : ℕ) :=
  Basis.piTensorProduct (mmBasis K n)

theorem repr_tprod (n : ℕ) (v : ∀ s, MME.MMSpace K n n n s)
    (p : Fin 3 → Fin n × Fin n) :
    (mmTensorBasis K n).repr (tprod K v) p =
      v 0 (p 0) * v 1 (p 1) * v 2 (p 2) := by
  simp [mmTensorBasis, Basis.piTensorProduct_repr_tprod_apply,
    Fin.prod_univ_succ, mmBasis, Pi.basisFun_repr, mul_assoc]
  exact congrArg₂ (· * ·) (Pi.basisFun_repr K _ (v 0) (p 0))
    (congrArg₂ (· * ·) (Pi.basisFun_repr K _ (v 1) (p 1))
      (Pi.basisFun_repr K _ (v 2) (p 2)))


theorem repr_mmTensor (n : ℕ) (p : Fin 3 → Fin n × Fin n) :
    (mmTensorBasis K n).repr (MME.MMTensor K n n n) p =
      Tensor.matrixMultiplication (K := K) n n n (p 0) (p 1) (p 2) := by
  classical
  simp [MME.MMTensor, map_sum, repr_tprod,
    Tensor.matrixMultiplication, Pi.single_apply, Prod.ext_iff,
    mul_ite, ite_and]
  split_ifs <;> simp_all [eq_comm]


theorem tensorRank_le_of_rankAtMost {n r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixMultiplication (K := K) n n n) r) :
    MME.tensorRank (MME.MMTensor K n n n) ≤ r := by
  classical
  obtain ⟨a, b, c, h⟩ := h
  apply Nat.sInf_le
  let v : Fin r → ∀ s, MME.MMSpace K n n n s := fun j s =>
    match s with
    | ⟨0, _⟩ => a j
    | ⟨1, _⟩ => b j
    | ⟨2, _⟩ => c j
  refine ⟨v, (mmTensorBasis K n).repr.injective ?_⟩
  ext p
  simp only [map_sum, Finsupp.finset_sum_apply, repr_tprod, repr_mmTensor]
  have hp := congrFun (congrFun (congrFun h (p 0)) (p 1)) (p 2)
  exact hp

theorem tensorRank_le_exactMatrixRank (n : ℕ) :
    MME.tensorRank (MME.MMTensor K n n n) ≤ exactMatrixRank K n :=
  tensorRank_le_of_rankAtMost (exactMatrixRank_spec n)

end MMEBridge

namespace MMEBridge
variable {K : Type u} [Field K]

theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))

theorem mme_exponent_range_bddBelow :
    BddBelow (Set.range (fun n : ℕ =>
      if 1 < n then
        Real.log (MME.tensorRank (MME.MMTensor K n n n) : ℝ) / Real.log n
      else 3)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  dsimp only
  split_ifs
  · exact div_nonneg (log_nat_nonneg _) (log_nat_nonneg _)
  · norm_num

theorem matMulExp_le_exactRankExponent : MME.matMulExp K ≤ exactRankExponent K := by
  apply le_csInf (exactRankExponentSet_nonempty (K := K))
  rintro _ ⟨n, hn, rfl⟩
  have hle := ciInf_le (mme_exponent_range_bddBelow (K := K)) n
  have hn1 : 1 < n := by omega
  simp only [if_pos hn1] at hle
  apply hle.trans
  rw [Real.logb]
  apply div_le_div_of_nonneg_right _ (log_nat_nonneg n)
  by_cases hz : MME.tensorRank (MME.MMTensor K n n n) = 0
  · simpa only [hz, Nat.cast_zero, Real.log_zero] using log_nat_nonneg (exactMatrixRank K n)
  · apply Real.log_le_log
    · exact_mod_cast (Nat.pos_of_ne_zero hz)
    · exact_mod_cast (tensorRank_le_exactMatrixRank (K := K) n)

#print axioms matMulExp_le_exactRankExponent
end MMEBridge

end
end CampaignBridge

section CampaignGoal

universe u

/-- The campaign's PiTensorProduct rank exponent is at most 2.25 over every field. -/
theorem solution {K : Type u} [Field K] :
    MME.matMulExp K ≤ (2.25 : ℝ) := by
  calc
    MME.matMulExp K ≤ OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent K :=
      MMEBridge.matMulExp_le_exactRankExponent
    _ ≤ (9 : ℝ) / 4 :=
      OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_nine_quarters_allFields K
    _ = (2.25 : ℝ) := by norm_num

#print axioms solution

#check @solution
end CampaignGoal
