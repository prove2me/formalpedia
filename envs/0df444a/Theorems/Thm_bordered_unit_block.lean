-- Prove2me | Theorems.Thm_bordered_unit_block
-- name    : bordered_unit_block
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:42:37.426272+00:00
-- url     : https://prove2.me/theorems/435c05a3-92f5-483f-8a79-5b97111ebac9
-- title:
--   Bordered form of a symmetric 4×4 matrix with identity lower-right block
-- statement:
--   Let $H$ be a real symmetric $4\times 4$ matrix whose lower-right $2\times 2$ block is the identity, and let $g \in \mathbb R^4$. Write $P$ for the $2\times 2$ block $(H_{i,j+2})_{i,j\in\{0,1\}}$, and put
--   $$L = H_{zz} - P P^{\mathsf T}, \qquad u = (g_2, g_3), \qquad v = (g_0, g_1) - P u,$$
--   where $H_{zz}$ is the upper-left $2\times 2$ block. Then
--   $$g^{\mathsf T} \operatorname{adj}(H)\, g \;=\; |u|^2 \det L \;+\; v^{\mathsf T} \operatorname{adj}(L)\, v .$$
--
--   This holds because $H = J^{\mathsf T} \operatorname{diag}(L, I) J$ for the unimodular shear $J = \begin{pmatrix} I & 0 \\ P^{\mathsf T} & I \end{pmatrix}$, and $g = J^{\mathsf T}(v, u)$. It reduces a $4\times 4$ bordered form (the curvature of a level set) to $2\times 2$ data. This is the block-diagonal structure of the Hessian of a Hamiltonian $\tfrac12|w + b(z)|^2 - \tfrac12 F(z)$, used for fiber elimination in Grisa's companion paper (Zenodo 21376299, §5).
--
--   **Formalization note.** The statement writes $L$, $u$, $v$ out in the entries of $H$; the hypotheses are $H^{\mathsf T} = H$, $H_{22} = H_{33} = 1$ and $H_{23} = 0$.
-- source:
--   Elementary linear algebra (block shear J^T diag(L, I) J); cf. Grisa, companion paper, Zenodo 21376299 (2026), §5 (block-diagonal Hessian).

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-- (a) Bordered form of a symmetric `4 × 4` matrix with identity lower-right block. -/
theorem bordered_unit_block (H : Matrix (Fin 4) (Fin 4) ℝ) (g : Fin 4 → ℝ)
    (hS : H.transpose = H) (h22 : H 2 2 = 1) (h33 : H 3 3 = 1) (h23 : H 2 3 = 0) :
    g ⬝ᵥ H.adjugate.mulVec g =
      (g 2 ^ 2 + g 3 ^ 2) *
          ((H 0 0 - H 0 2 ^ 2 - H 0 3 ^ 2) * (H 1 1 - H 1 2 ^ 2 - H 1 3 ^ 2)
            - (H 0 1 - H 0 2 * H 1 2 - H 0 3 * H 1 3) ^ 2) +
        ((H 1 1 - H 1 2 ^ 2 - H 1 3 ^ 2) * (g 0 - H 0 2 * g 2 - H 0 3 * g 3) ^ 2
          - 2 * (H 0 1 - H 0 2 * H 1 2 - H 0 3 * H 1 3) *
              (g 0 - H 0 2 * g 2 - H 0 3 * g 3) * (g 1 - H 1 2 * g 2 - H 1 3 * g 3)
          + (H 0 0 - H 0 2 ^ 2 - H 0 3 ^ 2) * (g 1 - H 1 2 * g 2 - H 1 3 * g 3) ^ 2) := by sorry
