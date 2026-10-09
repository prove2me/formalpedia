-- Prove2me | Definitions.Def_Nonadditivity_WeylTensor
-- name    : Nonadditivity_WeylTensor
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:15.833258+00:00
-- url     : https://prove2.me/theorems/3f6790f6-ce46-47c9-9768-3b75cb78567f
-- title:
--   Independent Weyl orbits of joint states
-- statement:
--   For positive dimension $d$, two independent local Weyl families act on the joint space $\mathbb C^{(\mathbb Z/d\mathbb Z)^2}$. Their uniform orbit contains exactly $d^4$ labels. The average of a joint matrix $A$ is $\operatorname{Tr}(A)I_{d^2}/d^2$; a density-matrix orbit contained in the output set therefore defines a normalized finite ensemble. The bundle proves the orbit entropy and information identities used for the two-use lower bound.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/WeylTensor.lean#L25-L209

import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_Weyl
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# Independent local Weyl twirling of arbitrary joint quantum states

This uses the actual tensor unitaries `U(q) ⊗ U(r)`, with `d⁴` labels.
The twirling identity applies to every joint matrix, including entangled
density matrices; no factorization of its entries or state is assumed.
-/

noncomputable section

namespace Nonadditivity.WeylTensor

open scoped BigOperators Kronecker

variable {d : ℕ} [NeZero d]

abbrev Label (d : ℕ) := ZMod d × ZMod d
abbrev Basis (d : ℕ) := ZMod d × ZMod d

def family (q r : Label d) : Matrix.unitaryGroup (Basis d) ℂ :=
  Entropy.tensorUnitary (Weyl.family q) (Weyl.family r)

def shiftEquiv (q r : Label d) : Equiv.Perm (Basis d) :=
  Equiv.prodCongr (Equiv.addRight q.1) (Equiv.addRight r.1)

def amplitude (q r : Label d) (i : Basis d) : ℂ :=
  ZMod.stdAddChar (q.2 * i.1) * ZMod.stdAddChar (r.2 * i.2)

theorem family_matrix_eq (q r : Label d) :
    (family q r : Matrix (Basis d) (Basis d) ℂ) =
      Matrix.diagonal (amplitude q r) * (shiftEquiv q r).permMatrix ℂ := by
  ext i j
  simp only [family, Entropy.tensorUnitary, Matrix.kroneckerMap_apply, Weyl.family,
    Weyl.unitaryMatrix, Weyl.phase, Weyl.shift, Matrix.diagonal_mul,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply,
    amplitude, shiftEquiv, Equiv.prodCongr_apply]
  change (ZMod.stdAddChar (q.2 * i.1) * (if j.1 = i.1 + q.1 then 1 else 0)) *
    (ZMod.stdAddChar (r.2 * i.2) * (if j.2 = i.2 + r.1 then 1 else 0)) =
    (ZMod.stdAddChar (q.2 * i.1) * ZMod.stdAddChar (r.2 * i.2)) *
      (if j = (i.1 + q.1, i.2 + r.1) then 1 else 0)
  simp only [Prod.ext_iff]
  split_ifs <;> simp_all

theorem conjugation_apply (q r : Label d)
    (A : Matrix (Basis d) (Basis d) ℂ) (i j : Basis d) :
    ((family q r : Matrix (Basis d) (Basis d) ℂ) * A *
      (family q r : Matrix (Basis d) (Basis d) ℂ).conjTranspose) i j =
    (ZMod.stdAddChar (q.2 * (i.1 - j.1)) *
      ZMod.stdAddChar (r.2 * (i.2 - j.2))) *
        A (i.1 + q.1, i.2 + r.1) (j.1 + q.1, j.2 + r.1) := by
  rw [family_matrix_eq, Matrix.conjTranspose_mul]
  have hmat : (Matrix.diagonal (amplitude q r) * (shiftEquiv q r).permMatrix ℂ) * A *
      (((shiftEquiv q r).permMatrix ℂ).conjTranspose *
        (Matrix.diagonal (amplitude q r)).conjTranspose) =
      Matrix.diagonal (amplitude q r) *
        ((shiftEquiv q r).permMatrix ℂ * A *
          ((shiftEquiv q r).permMatrix ℂ).conjTranspose) *
        (Matrix.diagonal (amplitude q r)).conjTranspose := by
    simp only [Matrix.mul_assoc]
  rw [hmat]
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply,
    Equiv.Perm.inv_def, Equiv.symm_symm, id_eq, Pi.star_apply]
  change amplitude q r i * A (i.1 + q.1, i.2 + r.1) (j.1 + q.1, j.2 + r.1) *
      star (amplitude q r j) = _
  have h₁ : q.2 * (i.1 - j.1) = q.2 * i.1 + -(q.2 * j.1) := by ring
  have h₂ : r.2 * (i.2 - j.2) = r.2 * i.2 + -(r.2 * j.2) := by ring
  simp only [amplitude, star_mul, Weyl.char_star, h₁, h₂, AddChar.map_add_eq_mul]
  ring

def twirlSum (A : Matrix (Basis d) (Basis d) ℂ) : Matrix (Basis d) (Basis d) ℂ :=
  ∑ s : ZMod d, ∑ r : ZMod d, ∑ t : ZMod d, ∑ u : ZMod d,
    (family (s, t) (r, u) : Matrix (Basis d) (Basis d) ℂ) * A *
      (family (s, t) (r, u) : Matrix (Basis d) (Basis d) ℂ).conjTranspose

/-- Exact local-unitary twirl for arbitrary joint matrices. -/
theorem twirl_sum_eq (A : Matrix (Basis d) (Basis d) ℂ) :
    twirlSum A = Matrix.diagonal (fun _ => ((d : ℂ) * d) * Matrix.trace A) := by
  ext i j
  simp only [twirlSum, Matrix.sum_apply, conjugation_apply]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, Weyl.character_orthogonality]
  by_cases h₁ : i.1 = j.1
  · by_cases h₂ : i.2 = j.2
    · have hij : i = j := Prod.ext h₁ h₂
      subst j
      simp only [sub_self, if_pos]
      try simp only [← Finset.mul_sum]
      have htrace : (∑ s : ZMod d, ∑ r : ZMod d,
          A (i.1 + s, i.2 + r) (i.1 + s, i.2 + r)) = Matrix.trace A := by
        simpa only [Fintype.sum_prod_type, Matrix.trace, Equiv.prodCongr_apply] using
          Fintype.sum_equiv
            (Equiv.prodCongr (Equiv.addLeft i.1) (Equiv.addLeft i.2))
            (fun sr : Basis d => A (i.1 + sr.1, i.2 + sr.2) (i.1 + sr.1, i.2 + sr.2))
            (fun k : Basis d => A k k) (fun _ => rfl)
      rw [htrace]
      simp
    · have hij : i ≠ j := fun h => h₂ (congrArg Prod.snd h)
      simp [h₁, sub_ne_zero.mpr h₂, hij]
  · have hij : i ≠ j := fun h => h₁ (congrArg Prod.fst h)
    simp [sub_ne_zero.mpr h₁, hij]

def uniformAverage (A : Matrix (Basis d) (Basis d) ℂ) : Matrix (Basis d) (Basis d) ℂ :=
  (1 / ((d : ℂ) ^ 4)) • twirlSum A

theorem uniform_average_eq (A : Matrix (Basis d) (Basis d) ℂ) :
    uniformAverage A = (Matrix.trace A / ((d : ℂ) ^ 2)) • (1 : Matrix (Basis d) (Basis d) ℂ) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  ext i j
  rw [uniformAverage, twirl_sum_eq]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
    field_simp
  · simp [Matrix.smul_apply, hij]

def uniformWeight (_ : Label d × Label d) : ℝ := 1 / ((d : ℝ) ^ 4)

omit [NeZero d] in
theorem uniformWeight_nonneg (q : Label d × Label d) : 0 ≤ uniformWeight q := by
  dsimp [uniformWeight]
  positivity

theorem family_card : Fintype.card (Label d × Label d) = d ^ 4 := by
  simp only [Label, Fintype.card_prod, ZMod.card]
  ring

theorem uniformWeight_sum : (∑ q : Label d × Label d, uniformWeight q) = 1 := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [uniformWeight, Finset.sum_const, Finset.card_univ, family_card,
    nsmul_eq_mul, Nat.cast_pow]
  field_simp

theorem uniform_average_eq_weighted_sum (A : Matrix (Basis d) (Basis d) ℂ) :
    uniformAverage A = ∑ q : Label d × Label d,
      (uniformWeight q : ℂ) •
        ((family q.1 q.2 : Matrix (Basis d) (Basis d) ℂ) * A *
          (family q.1 q.2 : Matrix (Basis d) (Basis d) ℂ).conjTranspose) := by
  simp only [uniformAverage, twirlSum, uniformWeight, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast,
    Fintype.sum_prod_type, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact Finset.sum_comm

def orbitIndex : Fin (d ^ 4) ≃ (Label d × Label d) :=
  (Fintype.equivFinOfCardEq family_card).symm

/-- The orbit of a joint state under all independent local Weyl unitaries. -/
def orbitEnsemble (outputs : Set (Entropy.DensityMatrix (Basis d)))
    (ρ : Entropy.DensityMatrix (Basis d))
    (hclosed : ∀ q r : Label d, ρ.unitaryConjugate (family q r) ∈ outputs) :
    StateEnsembles.Ensemble outputs where
  size := d ^ 4
  weight := fun i => uniformWeight (orbitIndex i)
  weight_nonneg := fun _ => uniformWeight_nonneg _
  weight_sum := by
    have hs := Fintype.sum_equiv (orbitIndex (d := d))
      (fun i => uniformWeight (orbitIndex i)) uniformWeight (fun _ => rfl)
    exact hs.trans uniformWeight_sum
  state := fun i => ρ.unitaryConjugate (family (orbitIndex i).1 (orbitIndex i).2)
  state_mem := fun i => hclosed (orbitIndex i).1 (orbitIndex i).2

theorem orbit_ensemble_average (outputs : Set (Entropy.DensityMatrix (Basis d)))
    (ρ : Entropy.DensityMatrix (Basis d))
    (hclosed : ∀ q r : Label d, ρ.unitaryConjugate (family q r) ∈ outputs) :
    (orbitEnsemble outputs ρ hclosed).average = Entropy.maximallyMixed (Basis d) := by
  apply Entropy.DensityMatrix.ext
  change (∑ i : Fin (d ^ 4), (uniformWeight (orbitIndex i) : ℂ) •
    (ρ.unitaryConjugate (family (orbitIndex i).1 (orbitIndex i).2)).matrix) = _
  have hs := Fintype.sum_equiv (orbitIndex (d := d))
    (fun i => (uniformWeight (orbitIndex i) : ℂ) •
      (ρ.unitaryConjugate (family (orbitIndex i).1 (orbitIndex i).2)).matrix)
    (fun q => (uniformWeight q : ℂ) • (ρ.unitaryConjugate (family q.1 q.2)).matrix)
    (fun _ => rfl)
  rw [hs]
  change (∑ q : Label d × Label d, (uniformWeight q : ℂ) •
    ((family q.1 q.2 : Matrix (Basis d) (Basis d) ℂ) * ρ.matrix *
      (family q.1 q.2 : Matrix (Basis d) (Basis d) ℂ).conjTranspose)) = _
  rw [← uniform_average_eq_weighted_sum, uniform_average_eq, ρ.normalized]
  simp [Entropy.maximallyMixed, Basis, ZMod.card, pow_two]

theorem orbit_ensemble_entropy (outputs : Set (Entropy.DensityMatrix (Basis d)))
    (ρ : Entropy.DensityMatrix (Basis d))
    (hclosed : ∀ q r : Label d, ρ.unitaryConjugate (family q r) ∈ outputs)
    (i : Fin (d ^ 4)) :
    ((orbitEnsemble outputs ρ hclosed).state i).vonNeumann = ρ.vonNeumann :=
  ρ.unitaryConjugate_entropy _

/-- Two-use coding lower bound from an arbitrary joint quantum state and
its actual finite local Weyl orbit. -/
theorem orbit_information_lower_bound (outputs : Set (Entropy.DensityMatrix (Basis d)))
    (ρ : Entropy.DensityMatrix (Basis d))
    (hclosed : ∀ q r : Label d, ρ.unitaryConjugate (family q r) ∈ outputs) :
    2 * Real.log d - ρ.vonNeumann ≤ StateEnsembles.quantity outputs := by
  have hb := StateEnsembles.orbit_lower_bound
    (orbitEnsemble outputs ρ hclosed) ρ (orbit_ensemble_average outputs ρ hclosed)
    (orbit_ensemble_entropy outputs ρ hclosed)
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simpa [Basis, ZMod.card, Real.log_mul hd hd, two_mul] using hb

end Nonadditivity.WeylTensor


