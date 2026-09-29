-- Prove2me | Theorems.Thm_mme_basisAllAllowedSubtensor_restrict_of_coefficient_imp
-- name    : mme_basisAllAllowedSubtensor_restrict_of_coefficient_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T15:17:03.622671+00:00
-- url     : https://prove2.me/theorems/aa34a0fc-62d8-4e88-bc83-8886908b5c78
-- title:
--   Coordinate projection enlargement from coefficient support
-- statement:
--   Let $K$ be a field and let $T\in V_0\otimes_K V_1\otimes_K V_2$ be a tensor on finite-dimensional spaces. Choose finite bases $b_i:I_i\to V_i$, and let $P_i,Q_i$ be arbitrary predicates on their basis indices. For a predicate family $R$, write $T[R]$ for the actual tensor obtained by projecting each mode onto the span of those $b_i(x_i)$ with $R_i(x_i)$.
--
--   Write $a(x_0,x_1,x_2)$ for the coefficient of $T$ in the product basis. Suppose
--   $$
--   a(x_0,x_1,x_2)\ne0
--   \ \text{ and }\
--   \bigwedge_{i=0}^2 Q_i(x_i)
--   \quad\Longrightarrow\quad
--   \bigwedge_{i=0}^2 P_i(x_i).
--   $$
--   Then
--   $$
--   T[Q]\preceq T[P],
--   $$
--   where $\preceq$ denotes restriction by modewise linear maps.
--
--   The result does not require either predicate family to contain the other. It permits restoring directions excluded by a coordinate filter when those directions contribute no nonzero coefficient to the desired projection. No equality of mode-space dimensions, or modewise linear isomorphism, is asserted. Empty index sets and zero tensors are allowed.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS1, Section 6.1, Claim 6.2 and the description of the ideal tensor immediately following Additional Zeroing-Out Step 2. Finite coordinate-map normalization lemma extracted from that argument; not a separately numbered theorem in the paper.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_tensor_rank
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME Module PiTensorProduct BigOperators

universe u

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_basisAllAllowedSubtensor_restrict_of_coefficient_imp
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} [∀ i, Fintype (ι i)]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (P Q : (i : Fin 3) → ι i → Prop)
    (hsupport : ∀ x : (i : Fin 3) → ι i,
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, Q i (x i)) → ∀ i, P i (x i)) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor b Q)
      (T.basisAllAllowedSubtensor b P) := by sorry
