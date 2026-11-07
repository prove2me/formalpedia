-- Prove2me | Theorems.Thm_ZKSheafPCP_theorem_8_3
-- name    : ZKSheafPCP.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:21.523309+00:00
-- url     : https://prove2.me/theorems/1d370f23-261e-4b6a-a385-0fb20a63a948
-- title:
--   Theorem 8.3 — $\mathcal R\cup\mathcal K$ is a $d_Y$-extendable cover of the bivariate Reed-Muller sheaf code
-- statement:
--   Let $L\subseteq\mathbb F$ be a subspace, let $d_X,d_Y\in\mathbb N$ with $d_X\ge|L_0|+d_Y$ and $d_Y\ge1$, and let $F=F_{d_X,d_Y}(L)$ be the bivariate Reed-Muller sheaf code of Definition 8.1. For all $c\in F_T$, the set of rows and columns $\mathcal R\cup\mathcal K$ is a $d_Y$-extendable cover for $F_{T=c}$. That is, it is a cover and, for each set $S'$ of at most $d_Y$ rows and columns, every locally valid assignment on $U_{S'}$ agreeing with $c$ on the curve extends to a global codeword agreeing with $c$ on the curve.
--
--   This is the structural source of zero knowledge in the construction: bounded views of the proof reveal only what the input fixes.
--
--   **Formalization Note** The first conjunct says that Definition 8.1 defines a sheaf.
--
--   Differences from the source:
--   - generalization: "Definition 8.1 ... define the sheaf of linear codes" → the conclusion also states that the local codes form a sheaf; reason: Definition 8.1 asserts this without proof, and the conjunct adds to Theorem 8.3 only; it specializes by dropping it
--   - encoding: a canonical basis of L → every basis of L, every field of characteristic 2 with 2^l elements; reason: no canonical basis is named
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Theorem 8.3, p.37; Definition 8.1, pp.36–37

import Mathlib
import Definitions.Def_ZKSheafPCP_RMParams

namespace ZKSheafPCP

open Classical

/-- Theorem 8.3, p.37 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): for a bivariate Reed-Muller sheaf code `F = F_{d_X,d_Y}(L)` (Definition 8.1) with `d_X ≥ |L₀| + d_Y`,
`d_Y ≥ 1`, and every `c ∈ F_T`, `ℛ ∪ 𝒦` is a `d_Y`-extendable cover for `F_{T=c}`. The first conjunct records that Definition
8.1 is a sheaf.

**Formalization Note** No hypothesis relates `d_Y` to `|𝒦|`. The field is any field of characteristic `2` with `2^l` elements, and
the basis of `L` is arbitrary. -/
theorem theorem_8_3 {F : Type} [Field F] [Fintype F] [CharP F 2] (R : RMParams F) (dX dY : ℕ)
    (hR : R.Valid dX) (hdX : R.L0.card + dY ≤ dX) (hdY : 1 ≤ dY) :
    (R.codes dX dY).IsSheaf R.space ∧
    ∀ c ∈ (R.codes dX dY).code R.curve,
      (R.codes dX dY).IsRelKExtendableCover R.space dY (R.space.geq R.curve) c (R.rows ∪ R.cols) := by sorry

end ZKSheafPCP
