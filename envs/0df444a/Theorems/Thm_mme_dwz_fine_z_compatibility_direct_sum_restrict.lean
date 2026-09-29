-- Prove2me | Theorems.Thm_mme_dwz_fine_z_compatibility_direct_sum_restrict
-- name    : mme_dwz_fine_z_compatibility_direct_sum_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T20:17:34.537965+00:00
-- url     : https://prove2.me/theorems/471a9fe4-beb2-40e2-9e7c-9ca2cdcace69
-- title:
--   DWZ fine-Z compatibility deletion yields a genuine refined direct sum
-- statement:
--   Let retained refined tensor copies be indexed by `Fin k`. For each copy, let `fineAddress` specify its three fine address words, and let `compatible z j` be a decidable relation saying that the fine Z word `z` is compatible with retained copy `j`. Assume: (1) each selected target Z word is compatible with its own copy; (2) no selected target Z word is compatible with another copy; (3) every coordinatewise supported mixed refined address has the same X and Y copy; and (4) the selected Z word of every such supported mixed address is compatible with its X copy. Then the direct sum of the retained refined address blocks restricts from the ambient tensor power:
--
--   $$
--   \bigoplus_{j < k} \operatorname{gradedAddressBlock}(G,\operatorname{fineAddress}_j)\;\leq\;T^{\otimes N}.
--   $$
--
--   Here `≤` denotes an actual modewise tensor restriction, not only a support-counting assertion. The theorem isolates the reusable final composition after fine-Z compatibility deletion.
--
--   **Formalization Note** The X/Y isolation and support-to-compatibility implication are explicit hypotheses. In particular, the theorem assumes rather than proves the translation of DWZ Claim 6.2 to `blockTensor ≠ 0`; it also does not formalize usefulness deletion, the concrete Table-2 grading, broken-copy realization, the Hole Lemma, or Equation (25).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.1: Step 3 and Additional Zeroing-Out Step 1 (printed p. 51, PDF p. 52), Claim 6.2, Definition 6.3, and Additional Zeroing-Out Step 2 (printed p. 52, PDF p. 53), and the broken-copy/Hole-Lemma handoff in Step 4 (printed p. 53, PDF p. 54). https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_fine_z_owner_exists_of_unique_compatibility
import Theorems.Thm_mme_dwz_fine_z_unique_owner_direct_sum_restrict

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_fine_z_compatibility_direct_sum_restrict
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
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      js 0 = js 1)
    (hSupportedCompatible : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      compatible (fineAddress (js 2) 2) (js 0)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (fineAddress j)))
      (T.kronPow N) := by
  sorry
