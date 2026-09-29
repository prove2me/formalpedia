-- Prove2me | Theorems.Thm_groupCohomology_d_cochainCup_apply
-- name    : groupCohomology.d_cochainCup_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/fd302c72-69a1-5b1b-8497-2c2948add24a
-- title:
--   Leibniz rule for the cup product of inhomogeneous cochains
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $A,B$ two $k$-linear representations of $G$ (objects of `Rep k G`), all in a single universe. Fix natural numbers $p,q$, an $A$-valued inhomogeneous $p$-cochain $f : G^p \to A$, a $B$-valued inhomogeneous $q$-cochain $g : G^q \to B$, and a tuple $\sigma : G^{p+q+1}$. Here $\mathrm{cochainCup}\,A\,B\,p\,q$ is the $k$-bilinear map sending $(f,g)$ to the $(A\otimes B)$-valued $(p+q)$-cochain whose value at $\tau \in G^{p+q}$ is $f(\tau \circ \mathrm{castAdd}) \otimes_k \rho_B\big(\tau_0\cdots\tau_{p-1}\big)\,g(\tau \circ \mathrm{natAdd})$, the first argument being the initial $p$ entries of $\tau$, the second the final $q$ entries, and the twisting element being `Fin.partialProd` of the initial segment evaluated at `Fin.last p`. The assertion is the pointwise identity, at the given $\sigma$, between the value of Mathlib's inhomogeneous differential $d^{p+q}$ on $f \cup g$ and the sum of two terms: the cochain $(d^p f) \cup g$ on $G^{(p+1)+q}$, evaluated at $\sigma$ precomposed with the reindexing `Fin.cast` coming from $(p+1)+q = p+q+1$, plus $(-1)^p$ times the value at $\sigma$ of $f \cup (d^q g)$, a cochain on $G^{p+(q+1)}$.
--
--   This is the Leibniz rule $d(f \cup g) = df \cup g + (-1)^p f \cup dg$ for the cup product on inhomogeneous cochains, stated pointwise at a tuple of group elements; the explicit `Fin.cast` records that $(p+1)+q = p+q+1$ is not a definitional identity in Lean, whereas $p+(q+1) = p+q+1$ is. It is the computational input for all cohomology-level properties of the cup product in this development, including the existence of a graded cup product, its compatibility with connecting homomorphisms, and the Tate-cohomology extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_d_cochainCup_apply.lean

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology

theorem groupCohomology.d_cochainCup_apply {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (p q : ℕ)
    (f : (Fin p → G) → A) (g : (Fin q → G) → B) (σ : Fin (p + q + 1) → G) :
    (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom (groupCohomology.cochainCup A B p q f g) σ
      = groupCohomology.cochainCup A B (p + 1) q ((inhomogeneousCochains.d A p).hom f) g
          (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i))
        + ((-1 : k) ^ p) • groupCohomology.cochainCup A B p (q + 1) f ((inhomogeneousCochains.d B q).hom g) σ := by sorry
