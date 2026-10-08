-- Prove2me | Definitions.Def_OAI429_GenericFiniteProjection
-- name    : OAI429_GenericFiniteProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-07T07:02:41.906994+00:00
-- url     : https://prove2.me/theorems/7ecb3248-96cb-4477-aa55-400d0a40d3ee
-- title:
--   Finite Fourier coefficients and polynomial separation weights
-- statement:
--   Finite Fourier phases and three coordinate weights assign each branch coefficient a normalized Fourier average and a polynomial degree.
--
--   The resulting projected branch polynomial distinguishes matching sectors and records the degree information used to bound the cost of finite separation.
-- source:
--   Extracted from the verified Lean proof at https://prove2.me/submissions/facf5b05-d302-42c1-a107-8ff40a0c2134; source module GenericFiniteProjection.

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
import Definitions.Def_OAI429_GenericFourier
import Definitions.Def_mme_omega

set_option autoImplicit false
set_option linter.all false
open scoped Classical


set_option linter.all false

set_option autoImplicit false

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












end OAIAllFieldsSeparation


end AllFieldsModule17
/- END all-fields module GenericFiniteProjection -/


