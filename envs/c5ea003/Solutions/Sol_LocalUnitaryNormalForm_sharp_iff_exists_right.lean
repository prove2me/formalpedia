-- Prove2me | solution 1 for LocalUnitaryNormalForm.sharp_iff_exists_right
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:54:53.662047+00:00
-- url     : https://prove2.me/submissions/63324202-b130-4418-b00c-1f1bb35d4ab9

-- Sol generated from Combinatorics/LocalUnitaryNormalForm.lean
import Mathlib
import Definitions.Def_Combinatorics_LocalUnitaryNormalForm
import Theorems.Thm_LocalUnitaryNormalForm_frobSq_localAct
import Theorems.Thm_LocalUnitaryNormalForm_rowGram_of_sharp
import Theorems.Thm_LocalUnitaryNormalForm_sharpMaximizer_bell

/-!
# Local-unitary normal form for maximally entangled two-qubit states

A two-qubit pure state `∑ᵢⱼ Mᵢⱼ |ij⟩` is encoded by its `2 × 2` complex amplitude matrix
`M : Matrix (Fin 2) (Fin 2) ℂ`.  Its squared Frobenius norm `frobSq M` is the total
probability and its *concurrence* is `concurrence M = 2 ‖det M‖` (Wootters).  A **sharp
maximizer** is a normalized state whose concurrence attains the maximal value `1`.

The main results are:

* `two_mul_norm_det_le_frobSq` : the sharp inequality `2 ‖det M‖ ≤ ‖M‖_F²`, obtained from the
  two-dimensional Lagrange / Cauchy–Binet identity `lagrange_two` together with AM–GM;
  `concurrence_le_one` is the resulting bound on normalized states.
* `row_sq_of_sharp`, `rowGram_of_sharp` : the **row classification** — the two rows of a
  normalized sharp maximizer are orthogonal and each of squared length `1/2`, equivalently
  `M * Mᴴ = (1/2) • 1`: the reduced density matrix is maximally mixed.
* `sharp_iff_rowGram` : conversely, a maximally mixed reduced density matrix forces sharpness.
* `sqrtTwo_smul_mem_unitaryGroup` : the promised step "build a unitary from an orthonormal
  basis" — for a sharp maximizer `√2 • M` is a unitary matrix.
* `localAct` : the two-sided `U(2) × U(2)` action `M ↦ U M Vᵀ` of the local unitaries `U ⊗ V`
  on amplitude matrices, with its action laws (`localAct_one`, `localAct_mul`) and the
  invariance of both `frobSq` and `‖det ·‖` (`frobSq_localAct`, `norm_det_localAct`).
* `sharp_iff_localAct_bell` : **every** normalized sharp maximizer lies in the local-unitary
  orbit of `bell = diag(1/√2, 1/√2)`, and conversely every point of that orbit is a sharp
  maximizer.
* `sharp_iff_exists_left`, `sharp_iff_exists_right` : one-sided transitivity — either factor of
  the local group already acts transitively on sharp maximizers, because `bell` is a scalar
  matrix; `exists_lact_of_sharp_sharp` phrases this as transitivity on the orbit.
* `stabilizer_bell` : the stabilizer of `bell` is `{(U, U̅)}`, i.e. `U ⊗ V` fixes the Bell state
  iff `V` is the entrywise conjugate of `U` (`V = Uᴴᵀ`).
* `concurrence_eq_zero_iff_isProduct` and `sharp_not_isProduct` : the opposite extreme of the
  scale, and the fact that the two extremes are disjoint.
* `flat_sharp_iff`, `card_sharp_signMats` : the *flat* sharp maximizers (all amplitudes of
  modulus `1/2`) are exactly the images of `(1/2) F₂` under diagonal unitaries — the order-two
  case of the classification of complex Hadamard matrices — and exactly `8` of the `16` real
  sign patterns are sharp.
* `sharpMaximizer_bellBasis`, `hsInner_bellBasis`, `bellBasis_expansion` : the Pauli orbit of
  `bell` is an orthonormal basis of the state space consisting of sharp maximizers.
* `concurrence_sq_eq_two_mul_linearEntropy`, `sharp_iff_purity`, `half_le_purity` : the
  concurrence is twice the linear entropy of the marginal, and sharp maximizers are exactly the
  normalized states of minimal purity `1/2`.
* `marginal_quadratic`, `sharp_iff_schmidt_eq`, `isProduct_iff_schmidtLo_eq_zero` : the Schmidt
  spectrum `(1 ± √(1 - C²))/2` of the marginal, degenerate exactly at the maximizers and
  containing `0` exactly at the product states.
* `frobSq_marginal_eq`, `frobSq_marginal_le_deficit` : a quantitative form of the row
  classification — the squared Frobenius distance of the marginal from `(1/2)·I` is exactly
  `(1 - C²)/2`, hence at most the concurrence deficit `1 - C`.
-/

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

open LocalUnitaryNormalForm











/-! ## Algebra of the two actions -/






/-! ## Elementary facts about `U(2)` -/

theorem transpose_mem_unitaryGroup {V : Amp} (hV : V ∈ U2) : Vᵀ ∈ U2 := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : Vᴴ * V = 1 := by
    have := hV.1
    rwa [Matrix.star_eq_conjTranspose] at this
  calc Vᵀ * star (Vᵀ) = Vᵀ * (Vᴴ)ᵀ := by rw [Matrix.star_eq_conjTranspose]; rfl
    _ = (Vᴴ * V)ᵀ := by rw [Matrix.transpose_mul]
    _ = 1 := by rw [h, Matrix.transpose_one]


theorem norm_det_of_mem_unitaryGroup {U : Amp} (hU : U ∈ U2) : ‖U.det‖ = 1 := by
  have h : U.det * star U.det = 1 := (Matrix.det_of_mem_unitary hU).2
  have h2 : ‖U.det‖ * ‖U.det‖ = 1 := by
    have := congrArg norm h
    simpa [norm_mul, norm_star] using this
  nlinarith [norm_nonneg U.det]

/-! ## The Lagrange (Cauchy–Binet) identity in dimension two -/


/-! ## Rows, the Frobenius norm and the Gram relation -/









/-! ## The sharp inequality `2 |det M| ≤ ‖M‖_F²` -/




/-! ## Row classification of the sharp maximizers -/



/-- Building a unitary out of the orthonormal basis furnished by the rows: for a sharp
maximizer `√2 • M` is unitary. -/
theorem sqrtTwo_smul_mem_unitaryGroup {M : Amp} (hG : M * Mᴴ = (1/2 : ℂ) • (1 : Amp)) :
    ((Real.sqrt 2 : ℝ) : ℂ) • M ∈ U2 := by
  have hcc : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, hG, smul_smul, smul_smul]
  rw [show (star ((Real.sqrt 2 : ℝ) : ℂ)) = ((Real.sqrt 2 : ℝ) : ℂ) from Complex.conj_ofReal _,
    hcc]
  norm_num

/-! ## Sharpness ⟺ maximally mixed marginal -/




/-! ## The Bell state -/

theorem bell_eq_smul : bell = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Amp) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bell]


/-! ## Invariance of the invariants under the local action -/


theorem det_localAct (U V M : Amp) : (localAct U V M).det = U.det * M.det * V.det := by
  simp [localAct, Matrix.det_mul, Matrix.det_transpose]

theorem norm_det_localAct {U V : Amp} (hU : U ∈ U2) (hV : V ∈ U2) (M : Amp) :
    ‖(localAct U V M).det‖ = ‖M.det‖ := by
  rw [det_localAct]
  simp [norm_det_of_mem_unitaryGroup hU, norm_det_of_mem_unitaryGroup hV]

theorem concurrence_localAct {U V : Amp} (hU : U ∈ U2) (hV : V ∈ U2) (M : Amp) :
    concurrence (localAct U V M) = concurrence M := by
  simp [concurrence, norm_det_localAct hU hV]

theorem sharpMaximizer_localAct {U V : Amp} (hU : U ∈ U2) (hV : V ∈ U2) {M : Amp}
    (h : SharpMaximizer M) : SharpMaximizer (localAct U V M) :=
  ⟨by simpa [Normalized] using (frobSq_localAct hU hV M).trans h.1,
   by rw [concurrence_localAct hU hV]; exact h.2⟩

/-! ## The normal form theorem -/

theorem eq_lact_bell_of_sharp {M : Amp} (h : SharpMaximizer M) : ∃ U ∈ U2, M = lact U bell := by
  refine ⟨((Real.sqrt 2 : ℝ) : ℂ) • M, sqrtTwo_smul_mem_unitaryGroup (rowGram_of_sharp h), ?_⟩
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity : (Real.sqrt 2) ≠ 0)]
    norm_num
  rw [lact, bell_eq_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, hs, one_smul]






/-! ## The opposite extreme: product states -/




/-! ## Flat maximizers and complex Hadamard matrices of order two

A sharp maximizer is *flat* when all four amplitudes have the same modulus `1/2`.  Rescaled by
`2` such a matrix is precisely a complex Hadamard matrix of order two, and the classical fact
that all of them are equivalent to the Fourier matrix `F₂ = !![1, 1; 1, -1]` becomes here the
statement that the flat sharp maximizers form a single orbit of the *diagonal* subgroup of
`U(2) × U(2)`. -/











/-! ### The real flat maximizers: a finite count -/





/-! ## The Bell basis: an orthonormal basis made of maximal maximizers

The local-unitary orbit of `bell` is large enough to contain an orthonormal basis of the whole
four-dimensional state space: applying the three Pauli unitaries on the first qubit produces the
Bell basis.  This is the structural fact underlying dense coding and teleportation. -/
















/-! ## Entanglement versus mixedness: the linear-entropy identity

For a two-qubit pure state the reduced density matrix is `ρ = M Mᴴ`, and its purity
`tr ρ²` is a direct measure of how mixed the marginal is.  Cayley–Hamilton in dimension two
turns the concurrence into the linear entropy `1 - tr ρ²`; sharp maximizers are exactly the
normalized states of minimal purity `1/2`. -/









/-! ## The Schmidt spectrum of a two-qubit state

Cayley–Hamilton in dimension two determines the spectrum of the marginal `ρ = M Mᴴ` from the
two invariants `tr ρ = ‖M‖_F²` and `det ρ = |det M|²`.  For a normalized state the two
*Schmidt coefficients* are therefore the explicit numbers `(1 ± √(1 - C²))/2`, and `ρ` is
annihilated by the corresponding quadratic.  Sharp maximizers are exactly the states whose
Schmidt coefficients coincide, product states exactly those with a vanishing one. -/











/-! ## A quantitative row classification

The row classification is an equality statement; the computation behind it is in fact exact and
yields a *stability* statement: the squared Frobenius distance from the marginal to the
maximally mixed state is exactly `(1 - C²)/2`, hence at most the concurrence deficit `1 - C`.
So a state of nearly maximal concurrence has a nearly maximally mixed marginal. -/











open LocalUnitaryNormalForm in
theorem solution(M : Amp) : SharpMaximizer M ↔ ∃ V ∈ U2, M = ract V bell := by
  constructor
  · intro h
    obtain ⟨U, hU, hM⟩ := eq_lact_bell_of_sharp h
    refine ⟨Uᵀ, transpose_mem_unitaryGroup hU, ?_⟩
    have hcomm : bell * U = U * bell := by
      rw [bell_eq_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    rw [ract, Matrix.transpose_transpose, hcomm]
    exact hM
  · rintro ⟨V, hV, rfl⟩
    have h : ract V bell = localAct 1 V bell := by simp [ract, localAct]
    rw [h]
    exact sharpMaximizer_localAct (Submonoid.one_mem _) hV sharpMaximizer_bell
