-- Prove2me | Definitions.Def_Combinatorics_LocalUnitaryNormalForm
-- name    : Combinatorics_LocalUnitaryNormalForm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:44:17.978575+00:00
-- url     : https://prove2.me/theorems/0d4a14b5-b2db-4740-8556-c376ca8a2d2f
-- title:
--   Aether Catalog definitions — Combinatorics_LocalUnitaryNormalForm
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.LocalUnitaryNormalForm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/LocalUnitaryNormalForm.lean by skeleton subtraction
import Mathlib

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

namespace LocalUnitaryNormalForm

/-- Amplitude matrix of a two-qubit pure state. -/
abbrev Amp := Matrix (Fin 2) (Fin 2) ℂ

/-- The unitary group `U(2)`, as a submonoid of `2 × 2` complex matrices. -/
abbrev U2 : Submonoid Amp := Matrix.unitaryGroup (Fin 2) ℂ

/-- Squared Frobenius norm (total probability) of an amplitude matrix. -/
def frobSq (M : Amp) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

/-- A state is normalized when its total probability is one. -/
def Normalized (M : Amp) : Prop := frobSq M = 1

/-- Wootters' concurrence of a two-qubit pure state. -/
def concurrence (M : Amp) : ℝ := 2 * ‖M.det‖

/-- A *sharp maximizer* is a normalized state of maximal concurrence. -/
def SharpMaximizer (M : Amp) : Prop := Normalized M ∧ concurrence M = 1

/-- The canonical maximally entangled state `diag(1/√2, 1/√2)` (the Bell state `Φ⁺`). -/
def bell : Amp := Matrix.diagonal fun _ => ((Real.sqrt 2)⁻¹ : ℝ)

/-- Left action of `U(2)`: a unitary applied to the first qubit. -/
def lact (U : Amp) (M : Amp) : Amp := U * M

/-- Right action of `U(2)`: a unitary applied to the second qubit.  On amplitude matrices
`1 ⊗ V` acts through the transpose of `V`. -/
def ract (V : Amp) (M : Amp) : Amp := M * Vᵀ

/-- The two-sided local-unitary action of `U ⊗ V` on amplitude matrices. -/
def localAct (U V : Amp) (M : Amp) : Amp := U * M * Vᵀ

/-! ## Algebra of the two actions -/






/-! ## Elementary facts about `U(2)` -/




/-! ## The Lagrange (Cauchy–Binet) identity in dimension two -/


/-! ## Rows, the Frobenius norm and the Gram relation -/

/-- Squared length of the first row. -/
def row0Sq (M : Amp) : ℝ := Complex.normSq (M 0 0) + Complex.normSq (M 0 1)

/-- Squared length of the second row. -/
def row1Sq (M : Amp) : ℝ := Complex.normSq (M 1 0) + Complex.normSq (M 1 1)

/-- Hermitian inner product of the two rows. -/
def rowInner (M : Amp) : ℂ := M 0 0 * conj (M 1 0) + M 0 1 * conj (M 1 1)






/-! ## The sharp inequality `2 |det M| ≤ ‖M‖_F²` -/




/-! ## Row classification of the sharp maximizers -/




/-! ## Sharpness ⟺ maximally mixed marginal -/




/-! ## The Bell state -/



/-! ## Invariance of the invariants under the local action -/






/-! ## The normal form theorem -/







/-! ## The opposite extreme: product states -/

/-- A state is a product state when its amplitude matrix is an outer product. -/
def IsProduct (M : Amp) : Prop := ∃ u w : Fin 2 → ℂ, ∀ i j, M i j = u i * w j



/-! ## Flat maximizers and complex Hadamard matrices of order two

A sharp maximizer is *flat* when all four amplitudes have the same modulus `1/2`.  Rescaled by
`2` such a matrix is precisely a complex Hadamard matrix of order two, and the classical fact
that all of them are equivalent to the Fourier matrix `F₂ = !![1, 1; 1, -1]` becomes here the
statement that the flat sharp maximizers form a single orbit of the *diagonal* subgroup of
`U(2) × U(2)`. -/

/-- The order-two Fourier (Hadamard) matrix. -/
def fourier2 : Amp := !![1, 1; 1, -1]

/-- A state is flat when all four amplitudes have the same modulus. -/
def IsFlat (M : Amp) : Prop := ∀ i j, ‖M i j‖ = 1/2









/-! ### The real flat maximizers: a finite count -/

/-- The two possible real amplitudes of a flat normalized state. -/
def sgn (b : Bool) : ℂ := if b then 1/2 else -1/2

/-- The real flat state with the prescribed sign pattern. -/
def signMat (a b c d : Bool) : Amp := !![sgn a, sgn b; sgn c, sgn d]



/-! ## The Bell basis: an orthonormal basis made of maximal maximizers

The local-unitary orbit of `bell` is large enough to contain an orthonormal basis of the whole
four-dimensional state space: applying the three Pauli unitaries on the first qubit produces the
Bell basis.  This is the structural fact underlying dense coding and teleportation. -/

/-- Hilbert–Schmidt inner product on amplitude matrices. -/
def hsInner (M N : Amp) : ℂ := ∑ i, ∑ j, conj (M i j) * N i j

/-- The Pauli matrix `σₓ`. -/
def pauliX : Amp := !![0, 1; 1, 0]

/-- The Pauli matrix `σ_y`. -/
def pauliY : Amp := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `σ_z`. -/
def pauliZ : Amp := !![1, 0; 0, -1]

/-- The four Pauli matrices `1, σₓ, σ_y, σ_z`. -/
def pauliMat : Fin 4 → Amp := ![1, pauliX, pauliY, pauliZ]

/-- The Bell basis, obtained from `bell` by the Pauli unitaries on the first qubit. -/
def bellBasis (k : Fin 4) : Amp := lact (pauliMat k) bell










/-! ## Entanglement versus mixedness: the linear-entropy identity

For a two-qubit pure state the reduced density matrix is `ρ = M Mᴴ`, and its purity
`tr ρ²` is a direct measure of how mixed the marginal is.  Cayley–Hamilton in dimension two
turns the concurrence into the linear entropy `1 - tr ρ²`; sharp maximizers are exactly the
normalized states of minimal purity `1/2`. -/




/-- Purity `tr ρ²` of the reduced density matrix `ρ = M Mᴴ`. -/
def purity (M : Amp) : ℝ := ((M * Mᴴ) * (M * Mᴴ)).trace.re





/-! ## The Schmidt spectrum of a two-qubit state

Cayley–Hamilton in dimension two determines the spectrum of the marginal `ρ = M Mᴴ` from the
two invariants `tr ρ = ‖M‖_F²` and `det ρ = |det M|²`.  For a normalized state the two
*Schmidt coefficients* are therefore the explicit numbers `(1 ± √(1 - C²))/2`, and `ρ` is
annihilated by the corresponding quadratic.  Sharp maximizers are exactly the states whose
Schmidt coefficients coincide, product states exactly those with a vanishing one. -/


/-- The larger Schmidt coefficient of a normalized two-qubit state. -/
def schmidtHi (M : Amp) : ℝ := (1 + Real.sqrt (1 - concurrence M ^ 2)) / 2

/-- The smaller Schmidt coefficient of a normalized two-qubit state. -/
def schmidtLo (M : Amp) : ℝ := (1 - Real.sqrt (1 - concurrence M ^ 2)) / 2








/-! ## A quantitative row classification

The row classification is an equality statement; the computation behind it is in fact exact and
yields a *stability* statement: the squared Frobenius distance from the marginal to the
maximally mixed state is exactly `(1 - C²)/2`, hence at most the concurrence deficit `1 - C`.
So a state of nearly maximal concurrence has a nearly maximally mixed marginal. -/









end LocalUnitaryNormalForm

end


