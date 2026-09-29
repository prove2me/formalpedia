-- Prove2me | Theorems.Thm_mme_complete_split_exact_power_six_finite_witness_power
-- name    : mme_complete_split_exact_power_six_finite_witness_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:29:56.748976+00:00
-- url     : https://prove2.me/theorems/aebcf0ab-b30b-40dc-a211-dc48fe7f57b9
-- title:
--   Exact complete-profile witnesses repeat to multiples of their length
-- statement:
--   Let $T^{[\beta]}_N$ denote the exact complete-profile power of a tensor $T$: the simultaneous three-mode projection of $T^{\otimes N}$ onto the basis words whose letter counts are exactly $N\beta_i(\sigma)$ in every mode.
--
--   Suppose that at length $N$ there is a finite witness for the six-symmetrized $\tau$-value at base $v$ — that is, natural numbers $k$ and triples $(a_j, b_j, c_j)$ such that
--
--   $$\bigoplus_{j<k} \langle a_j, b_j, c_j\rangle \;\trianglelefteq\; \mathrm{six}\big(T^{[\beta]}_N\big), \qquad v^{6N} \;\le\; \sum_{j<k} (a_j b_j c_j)^{\tau}.$$
--
--   Then for every $r$ there is such a witness at length $N r$, with the same base $v$:
--
--   $$\bigoplus \langle A, B, C\rangle \;\trianglelefteq\; \mathrm{six}\big(T^{[\beta]}_{Nr}\big), \qquad v^{6Nr} \;\le\; \sum (A B C)^{\tau}.$$
--
--   The proof takes the $r$-fold Kronecker power of the given witness: the matrix families multiply, the $\tau$-weights multiply as well, and the $r$-fold Kronecker power of the exact power restricts from the exact power at length $Nr$, because exactness is additive under concatenation. Six-symmetrization commutes with Kronecker powers up to isomorphism and is monotone under restriction, so the extraction transports.
--
--   This is the complete-profile analogue of the accepted prescribed-Z witness-power statement. It is what lets several exact-profile children, each with witnesses only along its own cofinal set of lengths, be brought to one common length.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.CompleteSplit MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_exact_power_six_finite_witness_power
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (N r : ℕ) (tau v : ℝ)
    (h : SixFiniteWitness TensorObj.Restrict
      (restrictedPower T b label beta 0 N) N tau v) :
    SixFiniteWitness TensorObj.Restrict
      (restrictedPower T b label beta 0 (N * r)) (N * r) tau v := by sorry
