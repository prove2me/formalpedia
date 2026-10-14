-- Prove2me | Theorems.Thm_MomentAngleSurgery_cokernel_equiv_blocks
-- name    : MomentAngleSurgery.cokernel_equiv_blocks
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:11:24.83518+00:00
-- url     : https://prove2.me/theorems/f27cbd24-3a1c-4640-9060-90c14f3fa400
-- title:
--   Cokernel of the zero-surgery linking blocks
-- statement:
--   For natural numbers $n,k$, put $A_k=(\mathbb Z^k)^3$ and $\Lambda_{n,k}(a,b,c)=(0,nc,nb)$. The abelian group presented by this explicit matrix satisfies
--   $$
--   A_k/\operatorname{im}(\Lambda_{n,k})\cong
--   \mathbb Z^k\oplus(\mathbb Z/n\mathbb Z)^k\oplus(\mathbb Z/n\mathbb Z)^k.
--   $$
--   This computes the presentation group for the zero-surgery blocks used to realize arbitrary torsion. The assertion includes $k=0$ and $n=0$, with $\mathbb Z/0\mathbb Z=\mathbb Z$. No existence of a manifold or homology identification is assumed in this algebraic statement.
-- source:
--   Elementary block-matrix consequence of the first isomorphism theorem and integer reduction modulo n. The matrix is the specialization of Calegari, Chapter 6: Floer Theories, Section 1.1.4, Lemma 1.5, printed p. 4, https://math.uchicago.edu/~dannyc/courses/heegaard_2020/floer_theory_notes.pdf . The exact algebraic ingredients are Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, GroupTheory/QuotientGroup/Basic.lean, quotientKerEquivOfSurjective (and its additive version), lines 154-160, and Data/ZMod/Basic.lean, intCast_zmod_eq_zero_iff_dvd, line 511: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/GroupTheory/QuotientGroup/Basic.lean . This displayed block computation is derived here, rather than quoted as a separately numbered result in those sources.

import Definitions.Def_MomentAngle_surgery_blocks
import Mathlib.Data.ZMod.Basic

open MomentAngleSurgery

theorem MomentAngleSurgery.cokernel_equiv_blocks (n k : ℕ) : Nonempty (Cokernel n k ≃+
    ((Fin k → ℤ) × (Fin k → ZMod n) × (Fin k → ZMod n))) := by sorry
