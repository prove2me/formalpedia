-- Prove2me | Theorems.Thm_mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
-- name    : mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:22:42.612907+00:00
-- url     : https://prove2.me/theorems/0d55bda9-10aa-4ded-ba78-1adf28e1ad84
-- title:
--   DWZ ownership masks are independent of fine-word representatives
-- statement:
--   Fix a finite family of component-address words, the associated three coarse grades, a profile-tag map on complete fine words, and exact componentwise profile counts. Let $f$ and $g$ be two fine-word sequences. Suppose that at every position they have the same total coarse grade and the same profile tag:
--   $$
--   \sum_r f(t,r)=\sum_r g(t,r),
--   \qquad \operatorname{tag}(f(t))=\operatorname{tag}(g(t)).
--   $$
--   Then every owner's coarse-grade predicate, every mode's exact profile predicate, Z-compatibility with each owner, and the full boundary-profile-and-unique-owner selection predicate have the same truth value on $f$ and $g$.
--
--   Consequently these selection masks are constant on fibers of the coarse-grade and profile-label map. In the fourth-power application the profile tag can be the left-square grade, so choosing a representative atomic fine word inside the same block cannot change ownership. This is a finite mask-invariance statement; it supplies neither a tensor realization nor a lower bound on surviving mass.
-- source:
--   Derived finite representative-invariance lemma for Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1, Definitions 5.3–5.5, and Section 6.1, additional zeroing-out and uniqueness filtering. https://arxiv.org/html/2210.10173v5#S6.SS1 . Not separately stated as a numbered lemma in the paper.

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data

open MME MME.CompleteSplit MME.DWZSimultaneous BigOperators

set_option autoImplicit false

theorem mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
    {C W : Type*} [DecidableEq C] [DecidableEq W] {ell N k : ℕ}
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (mu : Fin 3 → C → W → ℕ)
    (f g : FineWord ell N)
    (hgrade : ∀ t, (∑ r, (f t r).val) = ∑ r, (g t r).val)
    (htag : ∀ t, tag (f t) = tag (g t)) :
    (∀ j i, Graded component shape j i f ↔ Graded component shape j i g) ∧
    (∀ j i, Profile component tag mu j i f ↔ Profile component tag mu j i g) ∧
    (∀ j, ZCompatible component shape tag mu j f ↔
      ZCompatible component shape tag mu j g) ∧
    (∀ j i, Allowed component shape tag mu j i f ↔
      Allowed component shape tag mu j i g) := by sorry
