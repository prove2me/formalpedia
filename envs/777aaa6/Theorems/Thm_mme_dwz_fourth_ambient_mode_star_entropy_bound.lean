-- Prove2me | Theorems.Thm_mme_dwz_fourth_ambient_mode_star_entropy_bound
-- name    : mme_dwz_fourth_ambient_mode_star_entropy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T20:48:23.781373+00:00
-- url     : https://prove2.me/theorems/ee5a58ba-5d09-46a7-ab0e-9ca9fa8f449c
-- title:
--   Ambient fourth-level competitor bound with an explicit entropy ceiling
-- statement:
--   Let $N\geq0$ and let $M_i(g)$ be nonnegative integer marginal counts for
--   $i\in\{X,Y,Z\}$ and $g\in\{0,\ldots,8\}$. Write
--   $$
--   \mathcal C=\{(i,j,k)\in\{0,\ldots,8\}^3:i+j+k=8\}.
--   $$
--   Let $\mathcal A$ be a finite indexed family of triples of words
--   $a=(a_X,a_Y,a_Z)$ of length $N$. Suppose every member is coordinatewise
--   supported on $\mathcal C$, has marginal histograms $M_X,M_Y,M_Z$, and has a
--   different full three-mode address from every other member.
--
--   Fix a mode $s$ and a word $x$ with histogram $M_s$. Let $\mathcal H(M)$
--   consist of all tables $h:\mathcal C\to\{0,\ldots,N\}$ satisfying
--   $\sum_{c:c_i=g}h_c=M_i(g)$ for every $i,g$. Suppose $E\in\mathbb R$ satisfies
--   $$
--   \sum_{g=0}^{8}M_s(g)\log M_s(g)-\sum_{c\in\mathcal C}h_c\log h_c\leq E
--   \qquad(h\in\mathcal H(M)).
--   $$
--   Then
--   $$
--   \bigl|\{a\in\mathcal A:a_s=x\}\bigr|\leq(N+1)^{45}e^E.
--   $$
--
--   The logarithm is natural, with $0\log0=0$. Zero counts and $N=0$ are
--   included. The entropy ceiling ranges over all feasible joint tables, not
--   only a selected target type. The indexed family need not contain every
--   supported same-marginal address. For $N>0$, the exponent inside the ceiling is
--   $N\bigl(H(h/N)-H(M_s/N)\bigr)$, with natural-log Shannon entropy $H$.
--
--   This gives a finite ambient-competitor estimate for fourth-level asymmetric
--   hashing. It leaves the chosen-parameter entropy ceiling, compatible-Z rate,
--   modulus selection, and final extraction surplus as separate obligations.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Sections 3.6–3.10 and 6.2. https://arxiv.org/html/2210.10173v5 . Derived finite fourth-level ambient-star specialization, summing all same-marginal joint types. The entropy ceiling remains explicit; no numerical optimizer or final extraction bound is claimed.

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_dwz_fourth_ambient_mode_star_entropy_bound
    {N : ℕ} {ι : Type*} [DecidableEq ι]
    (address : ι → Fin 3 → Fin N → Fin 9)
    (M : Fin 3 → Fin 9 → ℕ) (ambient : Finset ι)
    (hsupport : ∀ j ∈ ambient, ∀ t, ∑ i, (address j i t).val = 8)
    (hmarginal : ∀ j ∈ ambient, ∀ i g,
      Fintype.card {t : Fin N // address j i t = g} = M i g)
    (hinj : Set.InjOn address (ambient : Set ι))
    (mode : Fin 3) (x : Fin N → Fin 9)
    (hx : ∀ g, Fintype.card {t : Fin N // x t = g} = M mode g)
    (E : ℝ) :
    let Cell := {sigma : Fin 3 → Fin 9 // (∑ i, (sigma i).val) = 8}
    let admissible : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ c : {c : Cell // c.val i = g}, (h c.val).val) = M i g)
    (∀ h ∈ admissible,
      (∑ g, (M mode g : ℝ) * Real.log (M mode g : ℝ)) -
        ∑ c : Cell, ((h c).val : ℝ) * Real.log ((h c).val : ℝ) ≤ E) →
    ((ambient.filter (fun j ↦ address j mode = x)).card : ℝ) ≤
      ((N : ℝ) + 1) ^ 45 * Real.exp E := by sorry
