-- Prove2me | solution 1 for LocalUnitaryNormalForm.isProduct_iff_schmidtLo_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:53:09.780282+00:00
-- url     : https://prove2.me/submissions/0dbc06f9-a186-488e-a313-cb8cf9c751ce

-- Sol generated from Combinatorics/LocalUnitaryNormalForm.lean
import Mathlib
import Definitions.Def_Combinatorics_LocalUnitaryNormalForm
import Theorems.Thm_LocalUnitaryNormalForm_concurrence_eq_zero_iff_isProduct

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

/-- Lagrange's identity: for `u = (a,b)` and `v = (c,d)` in `ℂ²`,
`|⟨u,v⟩|² + |det [u;v]|² = ‖u‖² ‖v‖²`. -/
theorem lagrange_two (a b c d : ℂ) :
    Complex.normSq (a * conj c + b * conj d) + Complex.normSq (a * d - b * c)
      = (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ## Rows, the Frobenius norm and the Gram relation -/




theorem frobSq_eq_rows (M : Amp) : frobSq M = row0Sq M + row1Sq M := by
  simp [frobSq, row0Sq, row1Sq, Fin.sum_univ_two]

theorem row0Sq_nonneg (M : Amp) : 0 ≤ row0Sq M := by
  have h1 := Complex.normSq_nonneg (M 0 0)
  have h2 := Complex.normSq_nonneg (M 0 1)
  simp only [row0Sq]; linarith

theorem row1Sq_nonneg (M : Amp) : 0 ≤ row1Sq M := by
  have h1 := Complex.normSq_nonneg (M 1 0)
  have h2 := Complex.normSq_nonneg (M 1 1)
  simp only [row1Sq]; linarith


/-- The Gram relation for a `2 × 2` matrix: `|⟨r₀, r₁⟩|² + |det M|² = ‖r₀‖² ‖r₁‖²`. -/
theorem gram_identity (M : Amp) :
    Complex.normSq (rowInner M) + Complex.normSq M.det = row0Sq M * row1Sq M := by
  rw [Matrix.det_fin_two]
  exact lagrange_two (M 0 0) (M 0 1) (M 1 0) (M 1 1)

/-! ## The sharp inequality `2 |det M| ≤ ‖M‖_F²` -/


/-- Hadamard-type bound: twice the modulus of the determinant is at most the squared
Frobenius norm.  Equality is the sharp-maximizer condition analysed below. -/
theorem two_mul_norm_det_le_frobSq (M : Amp) : 2 * ‖M.det‖ ≤ frobSq M := by
  have hg := gram_identity M
  have hi := Complex.normSq_nonneg (rowInner M)
  have hn : ‖M.det‖ ^ 2 = Complex.normSq M.det := (Complex.normSq_eq_norm_sq _).symm
  have h0 := row0Sq_nonneg M
  have h1 := row1Sq_nonneg M
  have hd : (0:ℝ) ≤ ‖M.det‖ := norm_nonneg _
  rw [frobSq_eq_rows]
  nlinarith [sq_nonneg (row0Sq M - row1Sq M), sq_nonneg (row0Sq M + row1Sq M - 2 * ‖M.det‖)]

/-- On normalized states the concurrence never exceeds one. -/
theorem concurrence_le_one {M : Amp} (hM : Normalized M) : concurrence M ≤ 1 := by
  have h := two_mul_norm_det_le_frobSq M
  rw [Normalized] at hM
  simp only [concurrence]
  linarith [hM ▸ h]

/-! ## Row classification of the sharp maximizers -/




/-! ## Sharpness ⟺ maximally mixed marginal -/




/-! ## The Bell state -/



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




theorem concurrence_nonneg (M : Amp) : 0 ≤ concurrence M := by
  simp only [concurrence]; positivity







/-! ## A quantitative row classification

The row classification is an equality statement; the computation behind it is in fact exact and
yields a *stability* statement: the squared Frobenius distance from the marginal to the
maximally mixed state is exactly `(1 - C²)/2`, hence at most the concurrence deficit `1 - C`.
So a state of nearly maximal concurrence has a nearly maximally mixed marginal. -/











open LocalUnitaryNormalForm in
theorem solution{M : Amp} (h : Normalized M) :
    IsProduct M ↔ schmidtLo M = 0 := by
  have h0 := concurrence_nonneg M
  have hc := concurrence_le_one h
  have hsq : Real.sqrt (1 - concurrence M ^ 2) ^ 2 = 1 - concurrence M ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ Real.sqrt (1 - concurrence M ^ 2) := Real.sqrt_nonneg _
  rw [← concurrence_eq_zero_iff_isProduct]
  constructor
  · intro hz
    rw [hz] at hsq
    have h1 : Real.sqrt (1 - (0:ℝ) ^ 2) = 1 := by norm_num
    simp only [schmidtLo, hz, h1]
    norm_num
  · intro hz
    simp only [schmidtLo] at hz
    have h1 : Real.sqrt (1 - concurrence M ^ 2) = 1 := by linarith
    rw [h1] at hsq
    nlinarith
