-- Prove2me | Theorems.Thm_exists_residueField_of_isMaximal_of_finiteDimensional
-- name    : exists_residueField_of_isMaximal_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/477f36bc-9295-520e-9f47-8cf75c5067b9
-- title:
--   Residue field at a maximal ideal as a finite separable extension
-- statement:
--   Let $F$ be a field of characteristic zero, let $A$ be a commutative ring equipped with an $F$-algebra structure which is finite-dimensional as an $F$-vector space, and let $\mathfrak m$ be an ideal of $A$ that is maximal. Then there exist a type $K$ in the same universe as $A$, a field structure on $K$, an $F$-algebra structure on $K$ making $K$ finite-dimensional over $F$ and separable over $F$ (in the sense of Mathlib's `Algebra.IsSeparable`, i.e. every element of $K$ has separable minimal polynomial over $F$), and an $F$-algebra homomorphism $\theta \colon A \to K$ such that $\theta$ is surjective and, for every $a \in A$, one has $\theta(a) = 0$ if and only if $a \in \mathfrak m$. The field $K$, its instances and the map $\theta$ are all packaged inside a single existential statement, so that no structure on a quotient ring need be produced by the user of the statement.
--
--   This is the standard fact that the residue field of a finite-dimensional commutative algebra over a field of characteristic zero at a maximal ideal is a finite separable extension, stated with the residue field and the reduction map bundled existentially. It is used in the analysis of the rational Tate module of a modular curve, in [`ModularCurve.rationalTateModule_false_of_inertia_fixed_eigenplane`](thm.html#ModularCurve.rationalTateModule_false_of_inertia_fixed_eigenplane), where one passes from a Hecke algebra over $\mathbb{Q}$ to its residue field at a maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_residueField_of_isMaximal_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem exists_residueField_of_isMaximal_of_finiteDimensional
    (F : Type u) [Field F] [CharZero F]
    (A : Type v) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (K : Type v) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (_ : Algebra.IsSeparable F K)
      (θ : A →ₐ[F] K), Function.Surjective θ ∧ ∀ a : A, θ a = 0 ↔ a ∈ 𝔪 := by sorry
