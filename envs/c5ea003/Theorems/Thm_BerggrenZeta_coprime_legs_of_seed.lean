-- Prove2me | Theorems.Thm_BerggrenZeta_coprime_legs_of_seed
-- name    : BerggrenZeta.coprime_legs_of_seed
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-14T01:23:08.338367+00:00
-- url     : https://prove2.me/theorems/2da68af7-7c47-4c46-ac0a-ebce34fce48e
-- title:
--   The legs of a Euclid seed are coprime: `gcd (m² - n², 2mn) = 1`.
-- statement:
--   The legs of a Euclid seed are coprime: `gcd (m² - n², 2mn) = 1`.
--
--   ```lean
--   theorem BerggrenZeta.coprime_legs_of_seed{m n : ℕ} (h1 : n < m) (h3 : Nat.Coprime m n)
--       (h4 : (m + n) % 2 = 1) : Nat.Coprime (m ^ 2 - n ^ 2) (2 * m * n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BerggrenTreeZetaCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BerggrenTreeZetaCore.lean#L351

-- Thm stub generated from Novelty/BerggrenTreeZetaCore.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# The Berggren tree of primitive Pythagorean triples: seeds, words, and the hypotenuse

This file is the combinatorial backbone for the "zeta function of the Berggren tree"
project.  It sets up the Berggren ternary tree in its *Euclid-seed* coordinates and
proves the two facts that make an analytic theory possible at all:

* the map `w ↦ seed w` from ternary words to Euclid seeds is a **bijection** onto the
  set of admissible seeds `S = {(m,n) : n < m, 0 < n, gcd(m,n) = 1, m + n odd}`
  (`seed_bijective_onto_seeds`, `seedEquiv`);
* the hypotenuse of a node is `c(w) = m² + n²` (`hyp`), so the tree zeta function is a
  Dirichlet series over `S`.

The three Berggren matrices act on the seed by
`L (m,n) = (2m - n, m)`, `M (m,n) = (2m + n, m)`, `R (m,n) = (m + 2n, n)`,
and we check (`berggren_matrix_L/M/R`) that on the triple `(m²-n², 2mn, m²+n²)` these are
exactly the classical Berggren matrices
`A₁ = !![1,-2,2; 2,-1,2; 2,-2,3]`, `A₂ = !![1,2,2; 2,1,2; 2,2,3]`,
`A₃ = !![-1,2,2; -2,1,2; -2,2,3]` (the last one is `B₃` of `Shared.BerggrenTrees.B`).

## Main results

* `seed_isSeed` — every node of the tree is an admissible Euclid seed;
* `isSeed_reachable` — **completeness** (Berggren's theorem): every admissible seed is a
  node of the tree;
* `seed_injective` — **uniqueness**: distinct words give distinct nodes;
* `seedEquiv` — the resulting equivalence `List (Fin 3) ≃ {p // IsSeed p}`;
* `node_isPPT` — every node carries a primitive Pythagorean triple;
* `hyp_le_silver_pow`, `Mspine_hyp` , `Rspine_hyp` — the growth dichotomy: the largest
  hypotenuse at depth `k` grows like the square of the silver ratio `(1+√2)² = 3+2√2`,
  while the `R`-spine grows only quadratically (`2k² + 6k + 5`).
-/

open BerggrenZeta

/-! ## Part A. Seeds, moves and the tree -/












/-! ## Part B. The seed condition is preserved by the moves -/









/-! ## Part C. Completeness: every admissible seed occurs in the tree -/







/-! ## Part D. Uniqueness: the word is determined by the node -/













/-! ## Part E. The Pythagorean triple at a node, and the Berggren matrices -/

theorem BerggrenZeta.coprime_legs_of_seed{m n : ℕ} (h1 : n < m) (h3 : Nat.Coprime m n)
    (h4 : (m + n) % 2 = 1) : Nat.Coprime (m ^ 2 - n ^ 2) (2 * m * n) := by sorry
