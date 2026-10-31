-- Prove2me | Theorems.Thm_ZeroOneSimplex_lemma_7
-- name    : ZeroOneSimplex.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:32.576988+00:00
-- url     : https://prove2.me/theorems/11f092f0-06db-49bb-bc50-88506929ac8b
-- title:
--   Lemma 7 — for generic $c$ the chosen slope strictly decreases
-- statement:
--   Given an LP of form (1) with real data ($A$ of full row rank) and an auxiliary vector $v$, run the Shadow pivot rule from a feasible basis $B_0$ satisfying the slope condition of Theorem 7, entering $j_t$ (an improving pivot direction $z_t$ of largest slope) and removing $\ell_t$ at step $t$. Assume $c$ is generic: any two chosen pivot directions that are not parallel have different slopes $c^\top z/v^\top z$. Then for every iteration
--   $$
--   \frac{c^\top z_{t+1}}{v^\top z_{t+1}}<\frac{c^\top z_t}{v^\top z_t}.
--   $$
--
--   With the lexicographic rule this excludes cycling of the Shadow pivot rule.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - generalization: c, b, d, A and D integral (p.2) → c, A, b, D, d all real; reason: §3.4 treats a general LP (p.22), and the generic objective of p.25 is a random perturbation of c, so it is not integral; integrality is used only in Claims 2 and 3; integral data are a special case
--   - encoding: pivot direction z′ʲ(B) = A′_B⁻¹A′_j (pp.7, 11) → the unique w with A′w = 0, w_j = 1, w_k = 0 for nonbasic k ≠ j; reason: the printed formula has the wrong sign (the direction must satisfy A′w = 0); the ratio test (2) is unchanged
--   - reading: generic: for any two pivot directions z′, z″ chosen by the Shadow pivot rule, cᵀz′/vᵀz′ ≠ cᵀz″/vᵀz″ → any two chosen pivot directions that are not parallel have different slopes; reason: read literally, the condition is unsatisfiable when the same direction is chosen twice
--   - reading: in each iteration of the Shadow pivot rule → Phase 2 pivots from a feasible basis with the slope condition of Theorem 7; reason: §3.4 defines the Shadow pivot rule this way
--   - generalization: v defined according to a given Shadow rule → any v for which B 0 satisfies the slope condition; reason: the proof uses only the slope condition; every basis of the Shadow pivot rule after Phase 1 satisfies it
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Lemma 7, p.25 (genericity condition p.25)

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData_IsPivot
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Lemma 7** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, p.25). Given an LP of the
form (1) with a generic objective function, in each iteration of the Shadow pivot rule the value
`cᵀz_j / vᵀz_j` of the chosen pivot direction `z_j` is strictly less than that of the previous
iteration.

Here the Shadow pivot rule starts at a feasible basis `B 0` satisfying the condition of
Theorem 7 and at step `t` enters `j t` (an improving pivot direction of largest slope) and
removes `ℓ t`; "generic" is the condition of p.25: any two chosen pivot directions that are not
parallel have different slopes.

**Formalization Note.** All data, `c` included, are real: the generic objective of p.25 is a
random perturbation of `c`. The printed genericity condition asks for different slopes for any two
chosen directions; read literally it is unsatisfiable whenever the rule chooses the same
direction twice, so it is applied to non-parallel directions. -/
theorem lemma_7 {n m p : ℕ} (L : LPData n m p) (hA : L.A.rank = m) (v : Fin n → ℝ)
    (B : ℕ → Finset (Fin n ⊕ Fin p)) (j ℓ : ℕ → Fin n ⊕ Fin p) (T : ℕ)
    (hB0 : L.IsFeasibleBasis (B 0)) (hready : L.IsReady (B 0) v)
    (hstep : ∀ t < T, L.IsPivot (B t) (B (t + 1)) (j t) (ℓ t) ∧
      L.IsShadowEntering (B t) v (j t))
    (hgen : ∀ s < T, ∀ t < T, (∀ r : ℝ, L.edgeDir (B s) (j s) ≠ r • L.edgeDir (B t) (j t)) →
      L.c ⬝ᵥ L.edgeDir (B s) (j s) / v ⬝ᵥ L.edgeDir (B s) (j s) ≠
        L.c ⬝ᵥ L.edgeDir (B t) (j t) / v ⬝ᵥ L.edgeDir (B t) (j t)) :
    ∀ t, t + 1 < T →
      L.c ⬝ᵥ L.edgeDir (B (t + 1)) (j (t + 1)) / v ⬝ᵥ L.edgeDir (B (t + 1)) (j (t + 1)) <
        L.c ⬝ᵥ L.edgeDir (B t) (j t) / v ⬝ᵥ L.edgeDir (B t) (j t) := by sorry

end ZeroOneSimplex
