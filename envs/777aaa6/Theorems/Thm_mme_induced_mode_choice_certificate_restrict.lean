-- Prove2me | Theorems.Thm_mme_induced_mode_choice_certificate_restrict
-- name    : mme_induced_mode_choice_certificate_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T18:48:41.664835+00:00
-- url     : https://prove2.me/theorems/423e7ee4-b640-4cb2-955f-7497b600440b
-- title:
--   An induced finite mode-choice certificate yields a tensor restriction
-- statement:
--   Let $S$ and $T$ be order-three tensors over a field, and suppose a finite mode-choice certificate from $S$ to $T$ is given. Thus each mode has finitely many linear maps, all triples of choices outside a specified retained set annihilate $S$, and the sum of the retained images is exactly $T$. Then
--
--   $$T \preceq S,$$
--
--   where $\preceq$ denotes tensor restriction by one linear map in each mode. The restricting map in a mode is the sum of that mode's finite family of maps. Multilinearity expands the tensor product of these sums over all mode choices; off-support terms vanish and the retained terms sum to the target.
--
--   This theorem is a reusable algebraic kernel for induced block zeroing. In applications, all combinatorial and fine-coordinate content remains visible in the certificate hypotheses.
-- source:
--   Elementary multilinearity of tensor products; the induced variable-zeroing application follows the block-zeroing step in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 271, https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_induced_mode_choice_certificate
import Definitions.Def_mme_tensor_quotient

open MME PiTensorProduct BigOperators

universe u

theorem mme_induced_mode_choice_certificate_restrict
    {K : Type u} [Field K]
    {source target : TensorObj K 3}
    (cert : InducedModeChoiceCertificate source target) :
    TensorObj.Restrict target source := by sorry
