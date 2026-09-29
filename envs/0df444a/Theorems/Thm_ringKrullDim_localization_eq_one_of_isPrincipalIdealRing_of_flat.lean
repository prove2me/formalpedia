-- Prove2me | Theorems.Thm_ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat
-- name    : ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/03b833d3-cc73-58b0-a956-1e415844c349
-- title:
--   Finite flat algebras over a PID have local dimension one
-- statement:
--   Let $D$ be a commutative ring which is an integral domain and a principal ideal ring, and assume $D$ is not a field. Let $C$ be a commutative ring equipped with a $D$-algebra structure such that $C$ is finite as a $D$-module and flat as a $D$-module. Let $m$ be an ideal of $C$ which is maximal. Then the Krull dimension of the localisation of $C$ at the prime $m$, taken in the sense of `ringKrullDim` (the supremum of lengths of chains of primes, valued in $\mathbb{Z}$ with $\pm\infty$ adjoined), equals $1$. Equivalently, $\operatorname{ht} m = 1$ for every maximal ideal $m$ of $C$; no irreducibility, reducedness or Noetherian hypothesis beyond those implied by finiteness over a principal ideal domain is imposed, and in particular $C$ need not be a domain.
--
--   This is the standard statement that a finite flat algebra over a Dedekind-type base (here a principal ideal domain that is not a field) is one-dimensional at each maximal ideal, i.e. equidimensional of relative dimension zero over a one-dimensional base. It is used in the project to compute Krull dimensions of local rings of finite flat algebras obtained by base change, being cited by [`IsIntegrallyClosed.ringKrullDim_localization_tensor_eq_one_of_irreducible`](thm.html#IsIntegrallyClosed.ringKrullDim_localization_tensor_eq_one_of_irreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat
    (D : Type*) {C : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D] (hD : ¬ IsField D)
    [CommRing C] [Algebra D C] [Module.Finite D C] [Module.Flat D C]
    (m : Ideal C) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by sorry
