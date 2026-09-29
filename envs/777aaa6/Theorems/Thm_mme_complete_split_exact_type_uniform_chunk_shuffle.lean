-- Prove2me | Theorems.Thm_mme_complete_split_exact_type_uniform_chunk_shuffle
-- name    : mme_complete_split_exact_type_uniform_chunk_shuffle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:33:24.844925+00:00
-- url     : https://prove2.me/theorems/e7262c1f-7b19-4d4d-b7ec-029d17c8aadc
-- title:
--   Uniform chunk shuffles on an exact complete-profile type
-- statement:
--   Fix a complete-split profile $\beta$ at level $\ell$ and a finite length $N$. Let $B$ be the set of words of $N$ complete fine-word labels that have exactly profile $\beta$; equivalently, their zero-tolerance complete-profile count constraints hold.
--
--   Permuting constituent-factor positions gives a uniform shuffle system on this exact type. More precisely, there is a family of permutations $m_e$ of $B$, indexed by $e\in S_N$, such that
--
--   $$
--   m_e(w)=w\circ e^{-1}
--   $$
--
--   and, for every source and target $s,t\in B$,
--
--   $$
--   \bigl|\{e\in S_N:m_e(s)=t\}\bigr|\,|B|=|S_N|.
--   $$
--
--   This supplies the uniform-fiber combinatorial interface for repairing holes on one exact complete-profile domain. It concerns complete-label block words, not the finer basis-coordinate words. It does not assert uniformity over a positive-tolerance union of different empirical types.
--
--   **Formalization Note.** The domain is the existing `ApproxConsistent` predicate at tolerance zero. The theorem includes empty exact domains and the unique empty word at power zero; the uniform-fiber condition quantifies over source and target blocks and is vacuous if there are none. The inverse in the action agrees with the usual left permutation action; the actual tensor shuffle should therefore use the ambient map at $e^{-1}$.
-- source:
--   Vassilevska Williams, Xu, Xu, Zhou, New Bounds for Matrix Multiplication: from Alpha to Omega, https://arxiv.org/abs/2307.07970v2, Property7.1 and proof of restated Corollary4.2, pp48–49: chunk permutations within an exact interface term have uniform fibers on its complete-profile blocks. Complete profiles are those of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 pp14–15. This is the exact finite orbit/fiber interface, not the whole hole-repair theorem. Uses Proved mme_dwz_available_block_shuffle_of_pretransitive_action, Prove2Me49de94b3-66f2-4872-b8ee-88bbc2aee3b6. The domain is deliberately zero tolerance.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_hole_cover_data
import Mathlib.Data.Fintype.Perm

open MME MME.CompleteSplit MME.DWZComponentRestriction MME.DWZSquare
open scoped Classical NNReal

set_option autoImplicit false

theorem mme_complete_split_exact_type_uniform_chunk_shuffle (ell : ℕ) (beta : Profile ell) (N : ℕ) :
    ∃ system : AvailableBlockShuffle
      {w : PowIndex (CompleteWord ell) N // ApproxConsistent id beta 0 w}
      (Equiv.Perm (Fin N)),
      ∀ e source, (system.move e source).1 = PowIndex.reindex e.symm source.1 := by sorry
