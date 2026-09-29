-- Prove2me | Theorems.Thm_groupCohomology_Kummer_kummerClass_eq_zero_iff
-- name    : groupCohomology.Kummer.kummerClass_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/fb8bc90b-3b66-553d-9e5a-fddccfc7f9ee
-- title:
--   Vanishing of the Kummer class and p-th powers
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra such that $L/K$ is Galois (no finiteness is assumed), let $p$ be a natural number, and let $a \in K^\times$, $\alpha \in L^\times$ satisfy $\alpha^p = a$ in $L^\times$, i.e. the image of $a$ under the structure map $K \to L$ equals $(\alpha)^p$; $p$ is not assumed prime. Write $\mu_p(L)$ for the group `rootsOfUnity p L` of $p$-th roots of unity of $L$, regarded through its multiplicative distributive action of $\mathrm{Gal}(L/K)$ as a $\mathbb{Z}$-linear representation `kummerRep K L p` of the Galois group $L \simeq_{\mathrm{alg}[K]} L$. The datum of the above relation determines a $1$-cocycle `kummerCocycleRoots hα` of $\mathrm{Gal}(L/K)$ with values in $\mu_p(L)$, and `kummerClass hα` denotes its class in $H^1$ of `kummerRep K L p`, obtained by applying the canonical projection from $1$-cocycles to $H^1$. The theorem asserts that this class is zero if and only if there exists $b \in K^\times$ with $b^p = a$.
--
--   This is the standard injectivity statement of Kummer theory: the Kummer class attached to a $p$-th root of $a$ in a Galois extension measures precisely the failure of $a$ to be a $p$-th power already in $K^\times$. It is used to identify the kernel of the Kummer homomorphism, in [`groupCohomology.Kummer.ker_kummerHom`](thm.html#groupCohomology.Kummer.ker_kummerHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_kummerClass_eq_zero_iff.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.kummerClass_eq_zero_iff
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    kummerClass hα = 0 ↔ ∃ b : Kˣ, b ^ p = a := by sorry
