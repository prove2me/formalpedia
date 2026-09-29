-- Prove2me | Theorems.Thm_hermitian_eigenspan_decomp
-- name    : hermitian_eigenspan_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-06T01:09:18.817546+00:00
-- url     : https://prove2.me/theorems/aba7d438-672c-4aff-88db-311461e444ef
-- statement:
--   Spectral decomposition primitive: for any Hermitian real matrix A and any subset S of the V-indexed eigenbasis, the span of {eigenvectorBasis j | j ∈ S} in (V → ℝ) has dimension equal to S.card; moreover any vector v in this span admits a coefficient function c : V → ℝ such that v ⬝ᵥ v = ∑_{j ∈ S} c_j² and A *ᵥ v ⬝ᵥ v = ∑_{j ∈ S} c_j² · eigenvalues j. This is the core Rayleigh-quotient-on-eigenspan primitive used by both halves of Courant–Fischer.
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

open Matrix

/-!
# Spectral decomposition on a subspace spanned by eigenvectors

Fundamental primitive of Hermitian-matrix spectral theory: pick any subset
`S` of indices into the eigenbasis of a Hermitian matrix `A`, form the
subspace spanned by the corresponding eigenvectors (viewed as functions
`V → ℝ`). Then:

* the dimension of that subspace equals `S.card` (orthonormal basis ⇒
  linear independence ⇒ rank = card);
* every vector in the span admits a coefficient function `c : V → ℝ` such
  that the Euclidean dot products on both `v` and `A *ᵥ v` reduce to
  squared / weighted-squared sums over `S`.

This is exactly the content needed to bound Rayleigh quotients on
eigenvector subspaces — the heart of the Courant–Fischer min-max
characterization. Both the lower-bound (`hermitian_kth_eigenvalue_witness`)
and upper-bound (`hermitian_kth_eigenvalue_dual_witness`) primitives reduce
to this lemma plus a one-line antitone-monotonicity argument.

Not currently in Mathlib in this form.
-/

/-- **Spectral decomposition on an eigenvector span.** For any real
Hermitian `A : Matrix V V ℝ` and any subset `S : Finset V` of the index
type, the span of `{⇑(hA.eigenvectorBasis j) | j ∈ S}` in `V → ℝ`:

* has `Module.finrank` equal to `S.card`;
* admits, for every `v` in the span, a coefficient function `c : V → ℝ`
  with `v ⬝ᵥ v = ∑ j ∈ S, (c j) ^ 2` and
  `A *ᵥ v ⬝ᵥ v = ∑ j ∈ S, (c j) ^ 2 * hA.eigenvalues j`. -/

theorem hermitian_eigenspan_decomp
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (S : Finset V) :
    Module.finrank ℝ
        (Submodule.span ℝ ((S : Set V).image
          (fun j => (⇑(hA.eigenvectorBasis j) : V → ℝ)))) = S.card ∧
    ∀ v : V → ℝ,
      v ∈ Submodule.span ℝ ((S : Set V).image
          (fun j => (⇑(hA.eigenvectorBasis j) : V → ℝ))) →
      ∃ c : V → ℝ,
        v ⬝ᵥ v = ∑ j ∈ S, (c j) ^ 2 ∧
        A *ᵥ v ⬝ᵥ v = ∑ j ∈ S, (c j) ^ 2 * hA.eigenvalues j := by sorry
