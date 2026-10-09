-- Prove2me | Definitions.Def_Nonadditivity_Weyl
-- name    : Nonadditivity_Weyl
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:33:08.864573+00:00
-- url     : https://prove2.me/theorems/1b997465-6fb9-4080-94fc-1ee3f4730d31
-- title:
--   Finite Weyl unitaries and normalized orbit ensembles
-- statement:
--   For a positive integer $d$, this bundle constructs the phase and cyclic shift unitaries on $\mathbb C^{\mathbb Z/d\mathbb Z}$, their $d^2$-element Weyl family, and its uniform matrix average. The average of a matrix $A$ is $\operatorname{Tr}(A)I_d/d$. A density matrix whose unitary orbit lies in an output set yields a normalized finite ensemble with this maximally mixed average. The accompanying proved identities relate its information to the entropy of the starting state.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Weyl.lean#L30-L330

import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_StateEnsembles
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
# Explicit finite Weyl twirling

The basis is indexed by `ZMod d`.  The family consists of exactly `d²`
unitary matrices.  No random-matrix or channel theorem is assumed here.
-/

noncomputable section

namespace Nonadditivity.Weyl

open scoped BigOperators ComplexConjugate

variable {d : ℕ} [NeZero d]

def phase (t : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.diagonal (fun i => ZMod.stdAddChar (t * i))

def shift (s : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.addRight s).permMatrix ℂ

theorem char_star (a : ZMod d) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  simp only [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

theorem char_mul_star (a : ZMod d) :
    ZMod.stdAddChar a * star (ZMod.stdAddChar a) = 1 := by
  rw [char_star, ← AddChar.map_add_eq_mul]
  simp

theorem phase_unitary (t : ZMod d) : phase t ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose]
  simp only [phase, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
    exact char_mul_star _
  · simp [hij]

theorem shift_unitary (s : ZMod d) : shift s ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  simp only [shift, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

def unitaryMatrix (s t : ZMod d) : Matrix.unitaryGroup (ZMod d) ℂ :=
  ⟨phase t * shift s, (Matrix.unitaryGroup (ZMod d) ℂ).mul_mem
    (phase_unitary t) (shift_unitary s)⟩

theorem shifted_conjugation_apply (s : ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (i j : ZMod d) :
    (shift s * A * (shift s).conjTranspose) i j = A (i + s) (j + s) := by
  simp only [shift, Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, Equiv.Perm.inv_def, Equiv.symm_symm, id_eq]
  rfl

theorem conjugation_apply (s t : ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (i j : ZMod d) :
    ((unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ) * A *
      (unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose) i j =
    ZMod.stdAddChar (t * (i - j)) * A (i + s) (j + s) := by
  change ((phase t * shift s) * A * (phase t * shift s).conjTranspose) i j = _
  rw [Matrix.conjTranspose_mul]
  have hmat : (phase t * shift s) * A * ((shift s).conjTranspose * (phase t).conjTranspose) =
      phase t * (shift s * A * (shift s).conjTranspose) * (phase t).conjTranspose := by
    simp only [Matrix.mul_assoc]
  rw [hmat]
  simp only [phase, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_conjTranspose, Pi.star_apply, shifted_conjugation_apply]
  rw [char_star]
  have he : t * (i - j) = t * i + -(t * j) := by ring
  rw [he, AddChar.map_add_eq_mul]
  ring



theorem character_orthogonality (a : ZMod d) :
    (∑ t : ZMod d, ZMod.stdAddChar (t * a)) = if a = 0 then (d : ℂ) else 0 := by
  simpa [ZMod.card] using
    AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar d)

def twirlSum (A : Matrix (ZMod d) (ZMod d) ℂ) : Matrix (ZMod d) (ZMod d) ℂ :=
  ∑ s : ZMod d, ∑ t : ZMod d,
    (unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ) * A *
      (unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose

/-- Exact unnormalized Weyl twirl for every complex matrix. -/
theorem twirl_sum_eq (A : Matrix (ZMod d) (ZMod d) ℂ) :
    twirlSum A = Matrix.diagonal (fun _ => (d : ℂ) * Matrix.trace A) := by
  ext i j
  simp only [twirlSum, Matrix.sum_apply, conjugation_apply, ← Finset.sum_mul,
    character_orthogonality]
  by_cases hij : i = j
  · subst j
    simp only [sub_self, if_pos]
    rw [← Finset.mul_sum]
    have htrace : (∑ s : ZMod d, A (i + s) (i + s)) = Matrix.trace A := by
      exact Fintype.sum_bijective _ (AddGroup.addLeft_bijective i) _ _ (fun _ => rfl)
    rw [htrace]
    simp
  · simp [sub_ne_zero.mpr hij, hij]

def uniformAverage (A : Matrix (ZMod d) (ZMod d) ℂ) : Matrix (ZMod d) (ZMod d) ℂ :=
  (1 / ((d : ℂ) * d)) • twirlSum A

/-- The normalized twirl is the completely depolarizing map. -/
theorem uniform_average_eq (A : Matrix (ZMod d) (ZMod d) ℂ) :
    uniformAverage A = (Matrix.trace A / (d : ℂ)) • (1 : Matrix (ZMod d) (ZMod d) ℂ) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  ext i j
  rw [uniformAverage, twirl_sum_eq]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
    field_simp
  · simp [Matrix.smul_apply, hij]

theorem uniform_average_trace_one (A : Matrix (ZMod d) (ZMod d) ℂ)
    (hA : Matrix.trace A = 1) :
    uniformAverage A = (1 / (d : ℂ)) • (1 : Matrix (ZMod d) (ZMod d) ℂ) := by
  rw [uniform_average_eq, hA]

def family (q : ZMod d × ZMod d) : Matrix.unitaryGroup (ZMod d) ℂ :=
  unitaryMatrix q.1 q.2

theorem family_card : Fintype.card (ZMod d × ZMod d) = d ^ 2 := by
  simp [pow_two]

theorem uniform_average_eq_family_sum (A : Matrix (ZMod d) (ZMod d) ℂ) :
    uniformAverage A = ∑ q : ZMod d × ZMod d,
      (1 / ((d : ℂ) * d)) •
        ((family q : Matrix (ZMod d) (ZMod d) ℂ) * A *
          (family q : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose) := by
  simp only [uniformAverage, twirlSum, family, Fintype.sum_prod_type, Finset.smul_sum]

def uniformWeight (_ : ZMod d × ZMod d) : ℝ := 1 / ((d : ℝ) * d)

omit [NeZero d] in
theorem uniformWeight_nonneg (q : ZMod d × ZMod d) : 0 ≤ uniformWeight q := by
  dsimp [uniformWeight]
  positivity

theorem uniformWeight_sum : (∑ q : ZMod d × ZMod d, uniformWeight q) = 1 := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [uniformWeight, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card, nsmul_eq_mul, Nat.cast_mul]
  field_simp

omit [NeZero d] in
theorem uniformWeight_complex (q : ZMod d × ZMod d) :
    (uniformWeight q : ℂ) = 1 / ((d : ℂ) * d) := by
  simp [uniformWeight]

theorem uniform_average_eq_weighted_sum (A : Matrix (ZMod d) (ZMod d) ℂ) :
    uniformAverage A = ∑ q : ZMod d × ZMod d,
      (uniformWeight q : ℂ) •
        ((family q : Matrix (ZMod d) (ZMod d) ℂ) * A *
          (family q : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose) := by
  simp only [uniformWeight_complex, uniform_average_eq_family_sum]









def orbitIndex : Fin (d ^ 2) ≃ (ZMod d × ZMod d) :=
  (Fintype.equivFinOfCardEq family_card).symm

















/-- A concrete normalized orbit ensemble with exactly `d²` states. -/
def orbitEnsemble (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs) :
    StateEnsembles.Ensemble outputs where
  size := d ^ 2
  weight := fun i => uniformWeight (orbitIndex i)
  weight_nonneg := fun i => uniformWeight_nonneg _
  weight_sum := by
    have hs := Fintype.sum_equiv (orbitIndex (d := d))
      (fun i => uniformWeight (orbitIndex i)) uniformWeight (fun _ => rfl)
    exact hs.trans uniformWeight_sum
  state := fun i => ρ.unitaryConjugate (family (orbitIndex i))
  state_mem := fun i => hclosed (orbitIndex i)

theorem orbit_ensemble_average (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs) :
    (orbitEnsemble outputs ρ hclosed).average = Entropy.maximallyMixed (ZMod d) := by
  apply Entropy.DensityMatrix.ext
  change (∑ i : Fin (d ^ 2), (uniformWeight (orbitIndex i) : ℂ) •
    (ρ.unitaryConjugate (family (orbitIndex i))).matrix) = _
  have hs := Fintype.sum_equiv (orbitIndex (d := d))
    (fun i => (uniformWeight (orbitIndex i) : ℂ) •
      (ρ.unitaryConjugate (family (orbitIndex i))).matrix)
    (fun q => (uniformWeight q : ℂ) • (ρ.unitaryConjugate (family q)).matrix)
    (fun _ => rfl)
  rw [hs]
  change (∑ q : ZMod d × ZMod d, (uniformWeight q : ℂ) •
    ((family q : Matrix (ZMod d) (ZMod d) ℂ) * ρ.matrix *
      (family q : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose)) = _
  rw [← uniform_average_eq_weighted_sum, uniform_average_trace_one _ ρ.normalized]
  simp [Entropy.maximallyMixed, ZMod.card]

theorem orbit_ensemble_entropy (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs)
    (i : Fin (d ^ 2)) :
    ((orbitEnsemble outputs ρ hclosed).state i).vonNeumann = ρ.vonNeumann :=
  ρ.unitaryConjugate_entropy _



/-- The Weyl orbit lower bound is proved from an actual finite ensemble,
not from a postulated orbit or maximally mixed average. -/
theorem orbit_information_lower_bound
    (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs) :
    Real.log d - ρ.vonNeumann ≤ StateEnsembles.quantity outputs := by
  simpa only [ZMod.card] using StateEnsembles.orbit_lower_bound
    (orbitEnsemble outputs ρ hclosed) ρ (orbit_ensemble_average outputs ρ hclosed)
    (orbit_ensemble_entropy outputs ρ hclosed)





end Nonadditivity.Weyl


