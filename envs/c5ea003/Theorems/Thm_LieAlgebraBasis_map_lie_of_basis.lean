-- Prove2me | Theorems.Thm_LieAlgebraBasis_map_lie_of_basis
-- name    : LieAlgebraBasis.map_lie_of_basis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T01:50:51.810957+00:00
-- url     : https://prove2.me/theorems/3675953a-b0fe-4849-9184-76e6b271dc9e
-- title:
--   A linear map preserving brackets on a basis preserves all brackets
-- statement:
--   Let $L$ be a Lie algebra over a commutative ring $R$ with a basis $(B_i)_{i\in\iota}$ of its underlying module, let $M$ be an $R$-module, and let $f:L\to\operatorname{End}_R(M)$ be $R$-linear. If
--
--   $$
--   [f(B_i),f(B_j)]=f\bigl([B_i,B_j]\bigr)\qquad\text{for all }i,j\in\iota,
--   $$
--
--   then the same holds for all $x,y\in L$, so $f$ is a homomorphism of Lie algebras.
--
--   **Role.** Representations are almost always specified by writing down what the generators do, and then the only thing to check is a finite list of bracket identities. This lemma is what licenses that: both sides of the defining identity are $R$-bilinear in $(x,y)$ --- the left because $f$ is linear and the commutator on $\operatorname{End}_R(M)$ is bilinear, the right because the bracket on $L$ is bilinear --- so agreement on pairs of basis vectors propagates to all pairs.
--
--   Note that a *basis* is needed, not merely a generating set: bilinearity extends an identity from a spanning family, but a spanning family that is not independent gives no way to define $f$ in the first place. When one starts instead from generators and relations, the corresponding statement requires a presentation of $L$, which is a different and much heavier piece of input.
--
--   Mathlib can construct a `LieHom` from a linear map together with the bracket condition for all pairs, but has no way to discharge that condition from a basis.
-- source:
--   Standard multilinear algebra. Needed to construct representations of a Lie algebra from prescribed actions on a basis, for instance the family tau(C, Phi) of Y. Chen and H. Tan, Simple sp_{2l}(C)-modules which are free over an abelian nilradical, Journal of Algebra 697 (2026), 341-372.

import Mathlib

namespace LieAlgebraBasis

theorem map_lie_of_basis {R L M ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] (B : Module.Basis ι R L)
    (f : L →ₗ[R] Module.End R M)
    (h : ∀ i j, ⁅f (B i), f (B j)⁆ = f ⁅B i, B j⁆) :
    ∀ x y : L, ⁅f x, f y⁆ = f ⁅x, y⁆ := by sorry

end LieAlgebraBasis
