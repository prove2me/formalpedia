-- Prove2me | Theorems.Thm_mme_flatteningRank_MMObj_ab
-- name    : mme_flatteningRank_MMObj_ab
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:23:50.373002+00:00
-- url     : https://prove2.me/theorems/8af3b4db-dac9-4a48-8771-a15dda83f86b
-- statement:
--   **Mode-0 flattening rank lower bound for the matrix-multiplication tensor.** The mode-0 flattening rank of $\mathrm{MM}(a, b, c)$ is at least $ab$ whenever $c \ge 1$. Equivalently, the flattening at the singleton split $S = \{0\}$ of $\mathrm{Fin}\,3$ has rank at least $a \cdot b$. Used as part of the standard $\mathrm{BddAbove}$ analysis in $\mathrm{subrankCapacityPoly}$ bridges: cyclic permutations of this fact combine via $(abc)^2 \le D_0^N D_1^N D_2^N$ to bound $(abc)^{1/3} \le \dim(T)^N$ after taking $N$-th tensor powers.
-- source:
--   Strassen flattening; standard textbook bound on MM(a,b,c)

import Definitions.Def_mme_flattening
import Definitions.Def_mme_tensor_rank

open MME

universe u

/-- **`a*b ≤ flatteningRank σ_0 (MMObj K a b c)` for `c ≥ 1`.**

The mode-0 flattening rank of the matrix-multiplication tensor `MM(a,b,c)` is at least
`a*b` whenever `c ≥ 1`. (Proof is in `Sol_mme_flatteningRank_MMObj_ab.lean`, where the
`solution` is provided. Here we expose it as a Theorem stub so downstream proofs can
import the statement without colliding with the top-level `solution` symbol.) -/
theorem mme_flatteningRank_MMObj_ab {K : Type u} [Field K] (a b c : ℕ) (hc : 1 ≤ c) :
    a * b ≤ MME.flatteningRank (MME.diagSplit (d := 3) (by norm_num)) (MME.MMObj K a b c) := by
  sorry
