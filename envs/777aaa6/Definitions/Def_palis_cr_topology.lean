-- Prove2me | Definitions.Def_palis_cr_topology
-- name    : palis_cr_topology
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T02:54:11.280473+00:00
-- url     : https://prove2.me/theorems/4d077a5e-5797-4015-b31d-5625a65411e7
-- title:
--   $C^r$ convergence and $C^r$-dense sets of diffeomorphisms and vector fields
-- statement:
--   Let $M$ be a manifold modelled on $\mathbb R^n$ and $r\ge0$ an integer.
--
--   1. A sequence of maps $g_k:M\to M$ **converges in $C^r$** to $f:M\to M$ if (a) for every compact $K\subset M$ and open $U\supset f(K)$, eventually $g_k(K)\subset U$; and (b) for all charts $e,e'$ of the atlas, every compact $K$ in the image of $e$ with $f(e^{-1}K)$ inside the domain of $e'$, and every $j\le r$, the $j$-th derivatives $D^j(e'\circ g_k\circ e^{-1})$ converge uniformly on $K$ to $D^j(e'\circ f\circ e^{-1})$.
--   2. A set $D\subset\mathrm{Diff}^r(M)$ is **$C^r$-dense** if every $f\in\mathrm{Diff}^r(M)$ is the $C^r$ limit of a sequence of elements of $D$.
--   3. A sequence of vector fields $Y_k$ **converges in $C^r$** to $X$ if for every chart $e$ of the atlas, every compact $K$ in the image of $e$ and every $j\le r$, $D^j (Y_k)_e\to D^j X_e$ uniformly on $K$, where $X_e$ is the local representative of $X$.
--   4. A set $D$ of vector fields is **$C^r$-dense in $\mathfrak X^r(M)$** if every $C^r$ vector field is the $C^r$ limit of a sequence of elements of $D$.
--
--   For compact $M$ this is convergence in the usual $C^r$ topology on $\mathrm{Diff}^r(M)$ and $\mathfrak X^r(M)$. Since that topology is metrizable, sequential density is equivalent to density.
--
--   **Formalization Note** Derivatives are `iteratedFDeriv ℝ j` and uniform convergence is `TendstoUniformlyOn`. Since the derivative is local, the composite $e'\circ g_k\circ e^{-1}$ agrees near $K$ with the true chart representative once $g_k(e^{-1}K)$ lies in the domain of $e'$, which holds eventually by (a).
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_vector_field

/-!
# The `C^r` topology on `Diff^r(M)` and on `𝔛^r(M)` (via convergent sequences)

For a compact manifold the `C^r` topology is metrizable, so a set is dense iff every element
is the limit of a sequence from the set. We therefore describe density through `C^r`
convergence of sequences: uniform convergence together with uniform convergence of all
derivatives of order `≤ r` of the chart representatives on compact subsets of chart domains.
-/

namespace PalisConjecture

open Filter
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- `C^r` convergence `g k → f` of maps `M → M`:
1. compact-open (`C^0`) convergence: for every compact `K` and open `U` with `f(K) ⊆ U`,
   eventually `g k (K) ⊆ U`;
2. for all charts `e, e'` of the atlas, every compact `K ⊆ e.target` with `f(e⁻¹ K) ⊆ e'.source`,
   and every `j ≤ r`, the `j`-th derivatives of `e' ∘ g k ∘ e⁻¹` converge uniformly on `K` to
   the `j`-th derivative of `e' ∘ f ∘ e⁻¹`. -/
def CrConvergesMap (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (r : ℕ) (g : ℕ → M → M) (f : M → M) : Prop :=
  (∀ K : Set M, IsCompact K → ∀ U : Set M, IsOpen U → f '' K ⊆ U →
      ∀ᶠ k in atTop, g k '' K ⊆ U) ∧
  ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) M, ∀ e' ∈ atlas (EuclideanSpace ℝ (Fin n)) M,
    ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ e.target →
      e.symm '' K ⊆ f ⁻¹' e'.source → ∀ j : ℕ, j ≤ r →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ j (e' ∘ g k ∘ e.symm))
          (iteratedFDeriv ℝ j (e' ∘ f ∘ e.symm)) atTop K

/-- A set `D` of `C^r` diffeomorphisms of `M` is dense in `Diff^r(M)` for the `C^r` topology. -/
def IsCrDenseDiffeo [IsManifold (𝓡 n) ∞ M] (r : ℕ)
    (D : Set (M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M)) : Prop :=
  ∀ f : M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M,
    ∃ g : ℕ → (M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M), (∀ k, g k ∈ D) ∧
      CrConvergesMap n r (fun k => (g k : M → M)) f

/-- `C^r` convergence `Y k → X` of vector fields: for every chart `e` of the atlas, every compact
`K ⊆ e.target` and every `j ≤ r`, the `j`-th derivatives of the chart representatives converge
uniformly on `K`. -/
def CrConvergesVF [IsManifold (𝓡 n) ∞ M] (r : ℕ)
    (Y : ℕ → (x : M) → TangentSpace (𝓡 n) x) (X : (x : M) → TangentSpace (𝓡 n) x) : Prop :=
  ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) M,
    ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ e.target → ∀ j : ℕ, j ≤ r →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ j (vfLocalRep (Y k) e))
        (iteratedFDeriv ℝ j (vfLocalRep X e)) atTop K

/-- A set `D` of vector fields is dense in `𝔛^r(M)` for the `C^r` topology: every `C^r` vector
field is a `C^r` limit of a sequence of elements of `D`. -/
def IsCrDenseVF [IsManifold (𝓡 n) ∞ M] (r : ℕ)
    (D : Set ((x : M) → TangentSpace (𝓡 n) x)) : Prop :=
  ∀ X : (x : M) → TangentSpace (𝓡 n) x, IsCrVectorField r X →
    ∃ Y : ℕ → (x : M) → TangentSpace (𝓡 n) x, (∀ k, Y k ∈ D) ∧ CrConvergesVF r Y X

end PalisConjecture


