-- Prove2me | Theorems.Thm_block_restrict_polyDegree_le
-- name    : block_restrict_polyDegree_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-08T21:26:06.466616+00:00
-- url     : https://prove2.me/theorems/f773f407-a30b-4dd2-b770-0cd4f55a2524
-- statement:
--   **Block-restriction preserves polynomial degree.**
--
--   Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean function, $x \in \{0,1\}^n$ a base point, and $B_1, B_2, \ldots, B_b \subseteq \{1, \ldots, n\}$ a family of pairwise-disjoint blocks. Define the block-restricted function $g : \{0,1\}^b \to \{0,1\}$ by
--   $$g(y) \;:=\; f\!\left( x \oplus \bigoplus_{i=1}^b y_i \cdot \mathbf{1}_{B_i} \right),$$
--   i.e. coordinate $j \in \{1, \ldots, n\}$ of the argument to $f$ is XOR-flipped from $x_j$ iff some block $B_i$ contains $j$ and the selector bit $y_i = 1$. Then
--   $$\deg(g) \;\le\; \deg(f).$$
--
--   Proof outline (NOT formalised here): take a multivariate polynomial $p$ realising $f$ of total degree $d := \deg(f)$. Build the substitution map $s : \{1, \ldots, n\} \to \mathbb{R}[Y_1, \ldots, Y_b]$ sending coordinate $j$ to:
--   - $\mathbf{1}[x_j = 1]$ (a constant polynomial) if $j \notin \bigcup_i B_i$;
--   - $Y_i$ or $1 - Y_i$ (a linear polynomial in $Y_i$, depending on $x_j$) if $j \in B_i$ for the unique $i$ given by disjointness.
--
--   Each $s(j)$ has total degree $\le 1$, so $\mathrm{bind}_1(s, p)$ has total degree $\le 1 \cdot d = d$ — which gives the desired witness for $\deg(g)$. (The lemma `bind₁_totalDegree_le` for $\mathrm{MvPolynomial}$ with linear substitutes is missing from current Mathlib.)
--
--   This is the block-substitution step in the Nisan–Szegedy proof of $\mathrm{bs}(f) \le 2 \cdot \deg(f)^2$.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313, §3 (block-substitution lemma — substituting linear polynomials into a polynomial of total degree $d$ over a Boolean cube preserves the degree-$d$ bound).

import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree
import Mathlib.Data.Finset.Basic

/-!
# Polynomial degree under block-restriction

For a Boolean function `f : {0,1}ⁿ → {0,1}` of polynomial degree `d`,
restricting attention to a *block-substitution sub-cube* — fixing some
coordinates to `x`, and grouping the remaining coordinates into pairwise-
disjoint blocks each parameterised by a single bit — yields a Boolean
function on the smaller cube `{0,1}ᵇ` whose polynomial degree is also at
most `d`.

This is the missing block-substitution lemma in the Nisan-Szegedy
proof. Its proof requires:
1. A construction of the substituted multivariate polynomial via
   `MvPolynomial.bind₁` with linear or constant inputs at each variable.
2. A proof that `bind₁` of a polynomial of total degree `≤ d` into linear
   polynomials yields a polynomial of total degree `≤ d` (this is
   `bind₁_totalDegree_le` for the special case `k = 1`, missing from
   Mathlib at present).
3. A proof that the substituted polynomial agrees with the block-restricted
   function on the cube.

Left as a platform leaf — DEFERRED. Estimated 150-250 lines.
-/

/-- The "multi-flip" of `x` selected by `y` over an indexed family of
disjoint blocks: at coordinate `j`, flips `x j` iff some block `e i`
contains `j` and `y i = true`. With `Classical.dec`, this is
`noncomputable`. -/
noncomputable def blockFlipMulti {n b : ℕ}
    (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (y : Fin b → Bool) (j : Fin n) : Bool :=
  open Classical in
  if ∃ i, j ∈ e i ∧ y i = true then !x j else x j

/-- **Block-restriction preserves polynomial-degree bound.** For Boolean
function `f`, point `x`, and pairwise-disjoint blocks `e i ⊆ Fin n`, the
function `y ↦ f (blockFlipMulti x e y)` on `{0,1}ᵇ` has polyDegree at most
that of `f`. -/

theorem block_restrict_polyDegree_le
    {n b : ℕ} (f : BoolFunc n) (x : Fin n → Bool)
    (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i j : Fin b, i ≠ j → Disjoint (e i) (e j)) :
    polyDegree (fun y : Fin b → Bool => f (blockFlipMulti x e y))
      ≤ polyDegree f := by sorry
