-- Prove2me | Theorems.Thm_mme_released_recursive_profile_identity
-- name    : mme_released_recursive_profile_identity
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T17:11:08.143232+00:00
-- url     : https://prove2.me/theorems/22c687f9-ada9-43f4-a0af-d48ec4f9252e
-- title:
--   The published global profile is the exact recursive seed mixture
-- statement:
--   For each owner $o$, parent shape $c$, hash mode $i$, and four-letter word $w$, let $s$ be the index of $c$ and let $t(o,s)$ be its published primitive seed term. The global integer count and its normalized frequency satisfy
--   $$N_{o,i,c,w}=\alpha_{o,s}\,C_{t(o,s)}(r_o(i),w),$$
--   $$P^{\rm global}_{o,i,c,w}=\frac{\alpha_{o,s}}D P_{t(o,s)}(r_o(i),w).$$
--   The parent profile on the right is explicitly the six-region mixture of split-weighted child products, with explicit boundary terminal profiles. This identifies the centers of the certified global windows with the data needed for the first recursive descent; it adds no rounding error.
-- source:
--   Exact-seed profile bridge for the six-region global interface in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2. Uses the already published primitive rational seed and literal supported joint counts; the recursive numerical continuation remains a separate obligation.

import Definitions.Def_mme_released_recursive_profile_mixture
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false

theorem mme_released_recursive_profile_identity (o : Fin 6) (i : Fin 3) (c : Shape) (w : Word) :
    wordCounts o i c w = alpha o (shapeEquiv.symm c) *
      parentCount (term o (shapeEquiv.symm c)) (roles o i) w ∧
    (profile o).2 i ⟨0,c⟩ w =
      ((alpha o (shapeEquiv.symm c) : ℝ) / D) *
        parentProfile (term o (shapeEquiv.symm c)) (roles o i) w := by sorry
