-- Prove2me | solution 1 for BerggrenZeta.hyp_block_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:40:33.752712+00:00
-- url     : https://prove2.me/submissions/16c9c516-7b5a-49c8-ab15-2b9892b1bc91

-- Sol generated from Novelty/BerggrenTreeHyperbolicSubtree.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeHyperbolicSubtree
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# Purely hyperbolic subtrees: the abscissa drops below `1`

The abscissa of convergence of the full Berggren tree zeta is `1`
(`Novelty.BerggrenTreeZetaAbscissa`), not the silver value `σ₀`; the reason is that two of
the three branches grow only polynomially (`Lspine_hyp`, `Rspine_hyp`).  This file isolates
the mechanism by removing the parabolic directions.

Consider the free binary subtree spanned by the two blocks

* `MM`  (`blockList true  = [1,1]`), and
* `MR`  (`blockList false = [1,2]`),

each of which contains the hyperbolic Pell move `M`.  Write `blocks bs` for the Berggren
word obtained by concatenating the blocks of a bit string `bs`.  Then:

* `blocks_injective` — distinct bit strings give distinct nodes, so the subtree really is a
  free binary tree inside the ternary Berggren tree;
* `hyp_blocks_lower` / `hyp_blocks_upper` — `5 (5/2)^d ≤ c(blocks bs) ≤ 5 (3+2√2)^{2d}` for
  a bit string of length `d`: every block is *expanding*, unlike the pure `R` direction;
* `summable_subtree` — the subtree zeta converges for `s > log 2 / log(5/2) ≈ 0.7565`;
* `not_summable_subtree` — and diverges for `0 < s < log 2 / log((3+2√2)²) ≈ 0.1963`;
* `subtree_summable_at_one` — in particular it **converges at `s = 1`**, where the full tree
  zeta diverges.

So the abscissa of the hyperbolic subtree lies in `[0.196, 0.757] ⊂ (0,1)`: the silver-type
prediction "abscissa = log(branching)/log(growth)" is qualitatively correct once the
parabolic generators are removed, and the failure of the silver abscissa for the full tree
is entirely due to them.
-/

open BerggrenZeta

open Real

/-! ## Part A. The block subtree -/




theorem blocks_cons_true (bs : List Bool) :
    blocks (true :: bs) = (1 : Fin 3) :: (1 : Fin 3) :: blocks bs := rfl

theorem blocks_cons_false (bs : List Bool) :
    blocks (false :: bs) = (1 : Fin 3) :: (2 : Fin 3) :: blocks bs := rfl



/-! ## Part B. Every block expands -/

/-- The Pell move multiplies the hypotenuse by at least `5/2`. -/
theorem hyp_M_lower (w : List (Fin 3)) :
    (5 / 2 : ℝ) * (hyp w : ℝ) ≤ (hyp ((1 : Fin 3) :: w) : ℝ) := by
  obtain ⟨h1, h2, -, -⟩ := seed_isSeed w
  have h1' : ((seed w).2 : ℝ) < ((seed w).1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < ((seed w).2 : ℝ) := by exact_mod_cast h2
  show (5 / 2 : ℝ) * (hyp w : ℝ) ≤ ((hyp ((1 : Fin 3) :: w) : ℕ) : ℝ)
  simp only [hyp, seed_cons, step, mvM]
  push_cast
  nlinarith

/-- The `R` move never decreases the hypotenuse. -/
theorem hyp_R_lower (w : List (Fin 3)) :
    (hyp w : ℝ) ≤ (hyp ((2 : Fin 3) :: w) : ℝ) := by
  obtain ⟨h1, h2, -, -⟩ := seed_isSeed w
  have h1' : ((seed w).2 : ℝ) < ((seed w).1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < ((seed w).2 : ℝ) := by exact_mod_cast h2
  show (hyp w : ℝ) ≤ ((hyp ((2 : Fin 3) :: w) : ℕ) : ℝ)
  simp only [hyp, seed_cons, step, mvR]
  push_cast
  nlinarith

theorem hyp_pos (w : List (Fin 3)) : (0 : ℝ) < (hyp w : ℝ) := by
  obtain ⟨h1, h2, -, -⟩ := seed_isSeed w
  have : 0 < hyp w := by
    have : 0 < (seed w).2 ^ 2 := by positivity
    simp only [hyp]
    omega
  exact_mod_cast this




/-! ## Part C. The subtree zeta -/







open BerggrenZeta in
theorem solution(b : Bool) (bs : List Bool) :
    (5 / 2 : ℝ) * (hyp (blocks bs) : ℝ) ≤ (hyp (blocks (b :: bs)) : ℝ) := by
  cases b with
  | true =>
    rw [blocks_cons_true]
    have h1 := hyp_M_lower (blocks bs)
    have h2 := hyp_M_lower ((1 : Fin 3) :: blocks bs)
    have hpos := hyp_pos (blocks bs)
    nlinarith
  | false =>
    rw [blocks_cons_false]
    have h1 := hyp_R_lower (blocks bs)
    have h2 := hyp_M_lower ((2 : Fin 3) :: blocks bs)
    nlinarith
