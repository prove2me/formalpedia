-- Prove2me | Theorems.Thm_mme_released_hashed_recipe_reference_transport
-- name    : mme_released_hashed_recipe_reference_transport
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T00:09:41.45151+00:00
-- url     : https://prove2.me/theorems/3fd55e04-bd4f-4de5-800b-082bb194c083
-- title:
--   Hashed graded recipes transport between released reference families
-- statement:
--   A graded recipe for the hashed part does not depend on which released reference is used. Any recipe built for one reference family transports to every other family, with the same input count, the same logarithmic output and the same dimension triple.
--
--   Fix a scale $K$, a level $\ell$ and a tolerance profile $\varepsilon=(\varepsilon_o)_{o\in\mathrm{Fin}\,6}$. For a family $a=(a_o)_o$ of released global references at scale $K$, each owner $o$ has $\mathrm{blocks}(K)$ blocks, and $a_o$ assigns a shape (hash cell) to each of them. A block is *hashed* when its cell has no zero coordinate. Let $N_K(a)=\mathrm{partSize}(K,a,1)=4\,p_K(a)$ be the number of fine positions of the $p_K(a)$ hashed blocks, and let $\mathcal Q_K(a,\varepsilon)$ be the hashed source predicate `QPos`. It asks that every hashed block's word has the grade of its cell in the owner's hash mode, and that for every owner $o$, every nonzero cell $c$ and every word $w$ the normalised count of hashed blocks of owner $o$, cell $c$ and word $w$ is within $\varepsilon_o$ of the released profile.
--
--   **Theorem.** Let $a$ and $a'$ be any two reference families at scale $K$, and let $R$ be a graded logarithmic joint recipe of level $\ell$ on $N_K(a')$ positions with source $\mathcal Q_K(a',\varepsilon)$. Then there is a graded logarithmic joint recipe $R'$ of level $\ell$ on $N_K(a)$ positions with source $\mathcal Q_K(a,\varepsilon)$ such that
--
--   $$
--   \mathrm{inputs}(R')=\mathrm{inputs}(R),\qquad \mathrm{logOutputs}(R')=\mathrm{logOutputs}(R),\qquad \mathrm{dims}(R')=\mathrm{dims}(R).
--   $$
--
--   **Role.** Every reference of owner $o$ realises the same prescribed cell histogram $K\cdot\mathrm{coarseCounts}_o$, so two families differ only by a permutation of blocks within each owner. The theorem says a construction of the hashed part may therefore fix one convenient reference family, for example one with sorted blocks, rather than handle an arbitrary one. Neither the rate nor the dimension bound changes.
--
--   **Formalization Note.** $R'$ is the one-part `partition` recipe whose positions are the relabelling of hashed fine positions induced by the owner-preserving, cell-preserving block bijection. `dims` is the full triple $(a,b,c)$.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); structural reduction of theorem 69b84798-206c-4f65-b1a1-2167ff28044f via the released reference definition (Def_mme_released_global_frame_data: Reference o k has exact cell counts k*coarseCounts o).

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_hashed_recipe_reference_transport (K ell : ℕ)
    (a a' : ∀ o : Fin 6, Reference o K) (eps : Fin 6 → ℝ)
    (R : LogJointRecipeG (partSize K a' 1) ell (QPos K a' eps)) :
    ∃ R' : LogJointRecipeG (partSize K a 1) ell (QPos K a eps),
      R'.inputs = R.inputs ∧ R'.logOutputs = R.logOutputs ∧ R'.dims = R.dims := by sorry
