-- Prove2me | Theorems.Thm_mme_dwz_fine_z_owner_exists_of_unique_compatibility
-- name    : mme_dwz_fine_z_owner_exists_of_unique_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T20:06:11.704425+00:00
-- url     : https://prove2.me/theorems/3a6fcc05-7100-408f-b19d-74920bfd0fc6
-- title:
--   DWZ fine-Z zeroing: finite unique compatibility constructs the partial owner
-- statement:
--   Let the retained copies be indexed by `Fin k`, let each retained copy have a selected fine Z word, and let `compatible z j` be a decidable relation saying that fine word `z` is compatible with retained copy `j`. Assume every selected target word is compatible with its own copy and with no other copy. Also assume the explicit source-facing support implication: whenever a mixed refined address is coordinatewise nonzero, its selected fine Z word is compatible with the mixed address's X copy. Then there exists a partial owner map from fine Z words to retained copies. It returns `some j` exactly when `j` is the unique compatible copy and returns `none` exactly when there is no unique compatible copy. In particular, it owns every selected target word by its target index and owns every supported mixed fine Z word by its X index, exactly supplying the two owner premises of the refined-address direct-sum restriction bridge. This theorem formalizes only the finite unique-compatibility deletion. It assumes, rather than proves, the Claim 6.2 support-to-compatibility translation and does not formalize the separate usefulness deletion, concrete Table-2 refined grading, broken-copy realization, Hole Lemma, or Equation (25).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.1: asymmetric hashing and Additional Zeroing-Out Step 1 (printed p. 51, PDF p. 52), Claim 6.2, Definition 6.3, and Additional Zeroing-Out Step 2 (printed p. 52, PDF p. 53), followed by the broken-copy/Hole-Lemma handoff in Step 4 (printed p. 53, PDF p. 54). https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_induced_word_zeroing

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_fine_z_owner_exists_of_unique_compatibility
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (fineAddress : Fin k → Fin 3 → Fin N → Fin t)
    (compatible : (Fin N → Fin t) → Fin k → Prop)
    [DecidableRel compatible]
    (hTargetCompatible : ∀ j : Fin k,
      compatible (fineAddress j 2) j)
    (hTargetUnique : ∀ j j' : Fin k,
      compatible (fineAddress j 2) j' → j' = j)
    (hSupportedCompatible : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      compatible (fineAddress (js 2) 2) (js 0)) :
    ∃ fineZOwner : (Fin N → Fin t) → Option (Fin k),
      (∀ z,
        fineZOwner z = none ↔ ¬ ∃! j, compatible z j) ∧
      (∀ z j,
        fineZOwner z = some j ↔
          compatible z j ∧
            ∀ j', compatible z j' → j' = j) ∧
      (∀ j : Fin k,
        fineZOwner (fineAddress j 2) = some j) ∧
      (∀ js : Fin 3 → Fin k,
        (∀ r : Fin N,
          G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
        fineZOwner (fineAddress (js 2) 2) = some (js 0)) := by
  sorry
