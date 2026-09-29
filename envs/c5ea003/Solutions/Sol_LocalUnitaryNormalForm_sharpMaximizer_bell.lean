-- Prove2me | solution 1 for LocalUnitaryNormalForm.sharpMaximizer_bell
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:53:11.420183+00:00
-- url     : https://prove2.me/submissions/dee2aa81-cb17-4b6c-a11f-72a5281f5c29

-- Sol generated from Combinatorics/LocalUnitaryNormalForm.lean
import Mathlib
import Definitions.Def_Combinatorics_LocalUnitaryNormalForm

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




/-! ## The Lagrange (Cauchy–Binet) identity in dimension two -/


/-! ## Rows, the Frobenius norm and the Gram relation -/









/-! ## The sharp inequality `2 |det M| ≤ ‖M‖_F²` -/




/-! ## Row classification of the sharp maximizers -/




/-! ## Sharpness ⟺ maximally mixed marginal -/




/-! ## The Bell state -/

theorem bell_eq_smul : bell = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Amp) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bell]


/-! ## Invariance of the invariants under the local action -/






/-! ## The normal form theorem -/







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
theorem solution: SharpMaximizer bell := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  constructor
  · simp only [Normalized, frobSq, bell_eq_smul, Fin.sum_univ_two]
    simp [Complex.normSq_apply]
    field_simp
    nlinarith [hs]
  · simp only [concurrence, bell_eq_smul, Matrix.det_fin_two]
    simp
    rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
    field_simp
    nlinarith [hs]
