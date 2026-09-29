-- Prove2me | Theorems.Thm_mme_complete_split_exact_power_concatenation_restrict
-- name    : mme_complete_split_exact_power_concatenation_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:27:41.952497+00:00
-- url     : https://prove2.me/theorems/f7817ab2-d19a-4b7e-ad68-fd457796fec1
-- title:
--   Exact complete-profile powers concatenate
-- statement:
--   Let $T$ be a tensor over a field $K$ with chosen bases $b_i$ of its three modes, let each basis index carry a complete word label $\mathrm{label}_i$ of level $\ell$, and let $\beta$ assign to each mode a probability profile on complete words. For a length $N$, the **exact complete-profile power**
--
--   $$T^{[\beta]}_N \;=\; \big(T^{\otimes N}\big)\big[\,\mathrm{ApproxConsistent}(\mathrm{label}_i, \beta_i, 0)\,\big]$$
--
--   is the simultaneous three-mode projection of $T^{\otimes N}$ onto those basis words whose letter counts are exactly $N\beta_i(\sigma)$ in every mode $i$ and for every complete word $\sigma$ (tolerance $\varepsilon = 0$).
--
--   Then for all $m, n$,
--
--   $$T^{[\beta]}_m \otimes T^{[\beta]}_n \;\trianglelefteq\; T^{[\beta]}_{m+n} .$$
--
--   The reason is that the exactness constraint is additive: concatenating a word of length $m$ whose counts are $m\beta$ with a word of length $n$ whose counts are $n\beta$ gives a word of length $m+n$ whose counts are $(m+n)\beta$. So the block-diagonal splitting of $T^{\otimes(m+n)}$ into $T^{\otimes m} \otimes T^{\otimes n}$ carries the allowed subspace of the product into the allowed subspace of the whole.
--
--   This is the complete-profile analogue of the accepted prescribed-Z concatenation, and it is the step that lets an exact-power value be transported from one length to its multiples, which a finite family of exact-profile children needs before it can be combined at a common length. Note that the reverse inclusion is false: a word can have the right global counts without being exact on each block.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_mode_word_basis

open MME MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_exact_power_concatenation_restrict
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (m n : ℕ) :
    TensorObj.Restrict
      (TensorObj.kron (restrictedPower T b label beta 0 m)
        (restrictedPower T b label beta 0 n))
      (restrictedPower T b label beta 0 (m + n)) := by sorry
