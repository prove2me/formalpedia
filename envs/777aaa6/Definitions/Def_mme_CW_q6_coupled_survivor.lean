-- Prove2me | Definitions.Def_mme_CW_q6_coupled_survivor
-- name    : mme_CW_q6_coupled_survivor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T05:25:57.148934+00:00
-- url     : https://prove2.me/theorems/fb142da6-af25-4fde-8009-a4fe76bd3989
-- title:
--   A symmetrized fine-structure survivor in the coupled $q=6$ extraction
-- statement:
--   For nonnegative integer type counts $L$ and $G$, define one symmetrized survivor of the coupled $q=6$ hashing construction by
--
--   $$
--   S_{L,G}=\operatorname{cyc}(\langle6,1,6\rangle)^{\otimes 2G}\otimes\operatorname{cyc}(\langle1,6,1\rangle)^{\otimes 2L}.
--   $$
--
--   The first factor records the $2G$ high-volume positions and the second records the $2L$ low-volume positions in the fine structure on CW90 journal p. 271. Separating this survivor object from its later restriction to a square matrix-multiplication tensor cleanly separates Salem--Spencer hashing from algebraic tensor assembly.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled-constituent proof on journal p. 271 (PDF p. 21), especially the fine-structure volume `(q^2)^(2G) q^(2L) = q^(4G+2L)`; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value

/-! One symmetrized survivor on CW90 journal p. 271 contains `2*G` copies of the high constituent and `2*L` copies of the low constituent. -/

universe u

namespace MME

noncomputable def coupledQ6Survivor
    (K : Type u) [Field K] (L G : ℕ) : TensorObj K 3 :=
  TensorObj.kron
    ((cyclicSymmetrization (MMObj K 6 1 6)).kronPow (2 * G))
    ((cyclicSymmetrization (MMObj K 1 6 1)).kronPow (2 * L))

end MME


