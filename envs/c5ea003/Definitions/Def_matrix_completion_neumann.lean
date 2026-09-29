-- Prove2me | Definitions.Def_matrix_completion_neumann
-- name    : matrix_completion_neumann
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T22:56:07.63902+00:00
-- url     : https://prove2.me/theorems/1eaa7ca3-8f98-4136-ac22-a17c92cab09e
-- statement:
--   This definition module provides Neumann-series certificate terms, their linear and quadratic index partitions, and the coefficient/contribution events used in Sections 4 through 6.
--
--   $$
--   Y=\sum_{k\ge 0}p^{-1}P_\Omega
--   \left(P_T-p^{-1}P_TP_\Omega P_T\right)^k(UV^\top).
--   $$
--
--   Module overview: Neumann-series interface for the least-squares dual certificate. Section 4.3 writes the inverse of $P_{T} P_\Omega P_{T}$ as a Neumann series in $H = P_{T} - p^{-1} P_{T} P_\Omega P_{T}$. The definitions here expose the concrete iterates and the normal-space certificate terms appearing in (4.13).
--
--   Documented declarations:
--   1. The Neumann error operator $H = P_{T} - p^{-1} P_{T} P_\Omega P_{T}$.
--   2. The iterate $H^k(E)$, where $E$ is the sign matrix.
--   3. The $k$th normal-space certificate term $p^{-1} P_{T^\perp} P_\Omega P_{T} H^k(E)$.
--   4. Centered Bernoulli indicator $\xi_{ij} = \delta_{ij} - p$.
--   5. Coordinate kernel $\langle P_{T}(e_{i} e_{j}^\top), e_{a} e_{b}^\top\rangle$.
--   6. Sum of all matrix entries, used to express scalar centered sampling fluctuations in coefficient estimates.
--   7. Diagonal tangent-kernel multiplier $X_{ab} ↦ X_{ab}\,\langle P_{T}(e_{ab}), e_{ab}\rangle$, the operator estimated in Lemma 6.4.
--   8. Off-diagonal tangent response $X ↦ \sum_{\omega' \ne \omega} X_{\omega'} \langle P_{T}(e_{\omega'}), e_\omega\rangle e_\omega$. This is the common response map behind the decoupled off-diagonal first-order term and the $\omega_{1} \ne \omega_{2} = \omega_{3}$ centered quadratic coefficient matrix.
--
--   Role in the mission. Key declarations include neumannErrorOperator, neumannIterate, neumannCertificateTerm, centeredIndicator, tangentCoordinateKernel, matrixEntrySum, tangentDiagonalMultiplier, offDiagonalTangentResponse, linearNeumannDiagonalBaseMatrix, quadraticNeumannAllEqualBaseMatrix, linearNeumannDiagonalContribution, linearNeumannDiagonalCenteredContribution, linearNeumannDiagonalMeanContribution, linearNeumannOffDiagonalContribution, linearNeumannOffDiagonalCoefficientMatrix, linearNeumannOffDiagonalDecoupledContribution, LinearNeumannOffDiagonalCoefficientBound, LinearNeumannFirstOrderContributionBounds, among others. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

/-!
Neumann-series interface for the least-squares dual certificate.

Section 4.3 writes the inverse of `P_T P_Omega P_T` as a Neumann series in
`H = P_T - p^{-1} P_T P_Omega P_T`.  The definitions here expose the concrete
iterates and the normal-space certificate terms appearing in (4.13).
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- The Neumann error operator `H = P_T - p^{-1} P_T P_Omega P_T`. -/
noncomputable def neumannErrorOperator {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : Real)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  tangentProjection S X -
    (p⁻¹) • tangentProjection S
      (samplingProjection Omega (tangentProjection S X))

/-- The iterate `H^k(E)`, where `E` is the sign matrix. -/
noncomputable def neumannIterate {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : Real)
    (k : Nat) : RealMatrix n1 n2 :=
  ((neumannErrorOperator Omega S p)^[k]) (signMatrix S)

/-- The `k`th normal-space certificate term
`p^{-1} P_{T^\perp} P_Omega P_T H^k(E)`. -/
noncomputable def neumannCertificateTerm {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) (k : Nat) : RealMatrix n1 n2 :=
  (p⁻¹) • normalProjection S
    (samplingProjection Omega (tangentProjection S (neumannIterate Omega S p k)))

/-- Centered Bernoulli indicator `ξ_ij = δ_ij - p`. -/
noncomputable def centeredIndicator {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (i : Fin n1) (j : Fin n2) : Real :=
  if (i, j) ∈ Omega then 1 - p else -p

/-- Coordinate kernel `⟪P_T(e_i e_j^T), e_a e_b^T⟫`. -/
noncomputable def tangentCoordinateKernel {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r)
    (i : Fin n1) (j : Fin n2) (a : Fin n1) (b : Fin n2) : Real :=
  matrixInner (tangentProjection S (coordinateMatrix i j)) (coordinateMatrix a b)

/-- Sum of all matrix entries, used to express scalar centered sampling
fluctuations in coefficient estimates. -/
noncomputable def matrixEntrySum {n1 n2 : Nat} (X : RealMatrix n1 n2) : Real :=
  ∑ w : Fin n1 × Fin n2, X w.1 w.2

/-- Diagonal tangent-kernel multiplier
`X_ab ↦ X_ab * ⟪P_T(e_ab), e_ab⟫`, the operator estimated in Lemma 6.4. -/
noncomputable def tangentDiagonalMultiplier {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j => X i j * tangentCoordinateKernel S i j i j

/-- Off-diagonal tangent response
`X ↦ ∑_{ω' ≠ ω} X_{ω'} ⟪P_T(e_{ω'}), e_ω⟫ e_ω`.
This is the common response map behind the decoupled off-diagonal first-order
term and the `ω₁ ≠ ω₂ = ω₃` centered quadratic coefficient matrix. -/
noncomputable def offDiagonalTangentResponse {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j =>
    ∑ w : Fin n1 × Fin n2,
      if w = (i, j) then 0 else
        X w.1 w.2 * tangentCoordinateKernel S w.1 w.2 i j

/-- Fixed matrix `H_ab = E_ab * ⟪P_T(e_ab), e_ab⟫` used in the centered
diagonal term of Lemma 4.5, equation (6.9). -/
noncomputable def linearNeumannDiagonalBaseMatrix {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) : RealMatrix n1 n2 :=
  tangentDiagonalMultiplier S (signMatrix S)

/-- Fixed matrix `E_ω P_{ωω}^2 F_ω` used in the all-equal quadratic term
of Lemma 4.6, equation (6.21). -/
noncomputable def quadraticNeumannAllEqualBaseMatrix {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) : RealMatrix n1 n2 :=
  tangentDiagonalMultiplier S (linearNeumannDiagonalBaseMatrix S)

/-- Diagonal contribution in the proof of Lemma 4.5, corresponding to
`(a,b) = (a',b')` in (6.8). -/
noncomputable def linearNeumannDiagonalContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w : Fin n1 × Fin n2,
      ((centeredIndicator Omega p w.1 w.2) ^ 2 *
        signMatrix S w.1 w.2 *
          tangentCoordinateKernel S w.1 w.2 w.1 w.2) •
        coordinateMatrix w.1 w.2

/-- Centered random part of the diagonal first Neumann contribution after
expanding `ξ_ab^2 = (1 - 2p)ξ_ab + p(1-p)` in (6.9). -/
noncomputable def linearNeumannDiagonalCenteredContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w : Fin n1 × Fin n2,
      (((1 - 2 * p) * centeredIndicator Omega p w.1 w.2) *
        signMatrix S w.1 w.2 *
          tangentCoordinateKernel S w.1 w.2 w.1 w.2) •
        coordinateMatrix w.1 w.2

/-- Deterministic mean part of the diagonal first Neumann contribution after
expanding `ξ_ab^2 = (1 - 2p)ξ_ab + p(1-p)` in (6.9). -/
noncomputable def linearNeumannDiagonalMeanContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (p : Real) :
    RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w : Fin n1 × Fin n2,
      ((p * (1 - p)) *
        signMatrix S w.1 w.2 *
          tangentCoordinateKernel S w.1 w.2 w.1 w.2) •
        coordinateMatrix w.1 w.2

/-- Off-diagonal contribution in the proof of Lemma 4.5, corresponding to
`(a,b) ≠ (a',b')` in (6.8). -/
noncomputable def linearNeumannOffDiagonalContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          (centeredIndicator Omega p w1.1 w1.2 *
            centeredIndicator Omega p w2.1 w2.2 *
              signMatrix S w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Conditional coefficient matrix `Q(E)` from (6.14) for the decoupled
off-diagonal first Neumann term.  The entry indexed by `w1` sums the second
independent centered sample over all `w2 ≠ w1`. -/
noncomputable def linearNeumannOffDiagonalCoefficientMatrix {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega2 : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ *
      ∑ w2 : Fin n1 × Fin n2,
        if w2 = (i, j) then 0 else
          centeredIndicator Omega2 p w2.1 w2.2 *
            signMatrix S w2.1 w2.2 *
              tangentCoordinateKernel S w2.1 w2.2 i j

/-- Decoupled off-diagonal first Neumann contribution: two independent
Bernoulli observation sets supply the two centered factors in (6.13). -/
noncomputable def linearNeumannOffDiagonalDecoupledContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2}
    (Omega1 Omega2 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          (centeredIndicator Omega1 p w1.1 w1.2 *
            centeredIndicator Omega2 p w2.1 w2.2 *
              signMatrix S w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Uniform entrywise bound for the conditional coefficient matrix `Q(E)` in
the decoupled off-diagonal first Neumann term. -/
def LinearNeumannOffDiagonalCoefficientBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega2 : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p bound : Real) : Prop :=
  entrySupNorm (linearNeumannOffDiagonalCoefficientMatrix Omega2 S p) ≤ bound

/-- Bounds for the diagonal and off-diagonal first-order Neumann contributions. -/
def LinearNeumannFirstOrderContributionBounds {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p diagBound offDiagBound : Real) : Prop :=
  spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤ diagBound ∧
    spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤ offDiagBound

/-- Quadratic Neumann contribution with `ω₁ = ω₂ = ω₃` in (6.20). -/
noncomputable def quadraticNeumannAllEqualContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w : Fin n1 × Fin n2,
      ((centeredIndicator Omega p w.1 w.2) ^ 3 *
        signMatrix S w.1 w.2 *
          tangentCoordinateKernel S w.1 w.2 w.1 w.2 *
            tangentCoordinateKernel S w.1 w.2 w.1 w.2) •
        coordinateMatrix w.1 w.2

/-- Centered random part of the all-equal quadratic contribution after using
`ξ^3 = (1 - 3p + 3p^2)ξ + p(1 - 3p + 2p^2)`. -/
noncomputable def quadraticNeumannAllEqualCenteredContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w : Fin n1 × Fin n2,
      (((1 - 3 * p + 3 * p ^ 2) *
        centeredIndicator Omega p w.1 w.2) *
          signMatrix S w.1 w.2 *
            tangentCoordinateKernel S w.1 w.2 w.1 w.2 *
              tangentCoordinateKernel S w.1 w.2 w.1 w.2) •
        coordinateMatrix w.1 w.2

/-- Deterministic mean part of the all-equal quadratic contribution after
using `ξ^3 = (1 - 3p + 3p^2)ξ + p(1 - 3p + 2p^2)`. -/
noncomputable def quadraticNeumannAllEqualMeanContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (p : Real) :
    RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w : Fin n1 × Fin n2,
      ((1 - 3 * p + 2 * p ^ 2) *
        signMatrix S w.1 w.2 *
          tangentCoordinateKernel S w.1 w.2 w.1 w.2 *
            tangentCoordinateKernel S w.1 w.2 w.1 w.2) •
        coordinateMatrix w.1 w.2

/-- Quadratic Neumann contribution with `ω₁ ≠ ω₂ = ω₃` in (6.20). -/
noncomputable def quadraticNeumannFirstIndexDistinctContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          (centeredIndicator Omega p w1.1 w1.2 *
            (centeredIndicator Omega p w2.1 w2.2) ^ 2 *
              signMatrix S w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
                  tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Centered random part of the `ω₁ ≠ ω₂ = ω₃` quadratic contribution after
expanding `ξ_{ω₂}^2 = (1 - 2p)ξ_{ω₂} + p(1-p)`. -/
noncomputable def quadraticNeumannFirstIndexDistinctCenteredContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          ((1 - 2 * p) *
            centeredIndicator Omega p w1.1 w1.2 *
              centeredIndicator Omega p w2.1 w2.2 *
                signMatrix S w2.1 w2.2 *
                  tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
                    tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Conditional coefficient matrix for the two-copy decoupled centered part of
the `ω₁ ≠ ω₂ = ω₃` quadratic contribution.  The inner independent sample
acts on the diagonal-weighted sign matrix from Lemma 6.7. -/
noncomputable def quadraticFirstIndexDistinctCenteredCoefficientMatrix
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega2 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ *
      ∑ w2 : Fin n1 × Fin n2,
        if w2 = (i, j) then 0 else
          centeredIndicator Omega2 p w2.1 w2.2 *
            signMatrix S w2.1 w2.2 *
              tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 i j

/-- Two-copy decoupled model for the centered part of the
`ω₁ ≠ ω₂ = ω₃` quadratic contribution. -/
noncomputable def quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega1 Omega2 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          ((1 - 2 * p) *
            centeredIndicator Omega1 p w1.1 w1.2 *
              centeredIndicator Omega2 p w2.1 w2.2 *
                signMatrix S w2.1 w2.2 *
                  tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
                    tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Uniform entrywise bound for the conditional coefficient matrix in the
two-copy decoupled centered `ω₁ ≠ ω₂ = ω₃` quadratic term. -/
def QuadraticFirstIndexDistinctCenteredCoefficientBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega2 : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p bound : Real) : Prop :=
  entrySupNorm (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S p) ≤
    bound

/-- Mean part of the `ω₁ ≠ ω₂ = ω₃` quadratic contribution after expanding
`ξ_{ω₂}^2 = (1 - 2p)ξ_{ω₂} + p(1-p)`. -/
noncomputable def quadraticNeumannFirstIndexDistinctMeanContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          ((1 - p) *
            centeredIndicator Omega p w1.1 w1.2 *
              signMatrix S w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
                  tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Deterministic coefficient matrix `H_{ω₁}` for the mean part of the
`ω₁ ≠ ω₂ = ω₃` quadratic term in the proof of Lemma 4.6. -/
noncomputable def quadraticFirstIndexDistinctMeanCoefficientMatrix
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ *
      ∑ w2 : Fin n1 × Fin n2,
        if w2 = (i, j) then 0 else
          signMatrix S w2.1 w2.2 *
            tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
              tangentCoordinateKernel S w2.1 w2.2 i j

/-- Quadratic Neumann contribution with `ω₁ = ω₃ ≠ ω₂` in (6.20). -/
noncomputable def quadraticNeumannMiddleIndexDistinctContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          ((centeredIndicator Omega p w1.1 w1.2) ^ 2 *
            centeredIndicator Omega p w2.1 w2.2 *
              signMatrix S w1.1 w1.2 *
                tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
                  tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Centered random part of the `ω₁ = ω₃ ≠ ω₂` quadratic contribution after
expanding `ξ_{ω₁}^2 = (1 - 2p)ξ_{ω₁} + p(1-p)`. -/
noncomputable def quadraticNeumannMiddleIndexDistinctCenteredContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          ((1 - 2 * p) *
            centeredIndicator Omega p w1.1 w1.2 *
              centeredIndicator Omega p w2.1 w2.2 *
                signMatrix S w1.1 w1.2 *
                tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
                    tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Conditional coefficient matrix for the two-copy decoupled centered part of
the `ω₁ = ω₃ ≠ ω₂` quadratic contribution.  The outer entry `ω₁` carries the
sign matrix and the inner independent sample sums the `ω₂` factor. -/
noncomputable def quadraticMiddleIndexDistinctCenteredCoefficientMatrix
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega2 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ *
      ∑ w2 : Fin n1 × Fin n2,
        if w2 = (i, j) then 0 else
          centeredIndicator Omega2 p w2.1 w2.2 *
            signMatrix S i j *
              tangentCoordinateKernel S i j w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 i j

/-- Fixed kernel-square base matrix for the Bernstein estimate of the
conditional coefficient in the `ω₁ = ω₃ ≠ ω₂` centered quadratic term.  The
outer sign factor is kept outside this base matrix, matching the paper's
separation of `E_ω` from the scalar `H_ω`. -/
noncomputable def quadraticMiddleIndexDistinctKernelSquareBaseMatrix
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (w1 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  fun i j =>
    if (i, j) = w1 then 0 else
      tangentCoordinateKernel S w1.1 w1.2 i j *
        tangentCoordinateKernel S i j w1.1 w1.2

/-- Two-copy decoupled model for the centered part of the
`ω₁ = ω₃ ≠ ω₂` quadratic contribution. -/
noncomputable def quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega1 Omega2 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          ((1 - 2 * p) *
            centeredIndicator Omega1 p w1.1 w1.2 *
              centeredIndicator Omega2 p w2.1 w2.2 *
                signMatrix S w1.1 w1.2 *
                  tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
                    tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Uniform entrywise bound for the conditional coefficient matrix in the
two-copy decoupled centered `ω₁ = ω₃ ≠ ω₂` quadratic term. -/
def QuadraticMiddleIndexDistinctCenteredCoefficientBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega2 : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p bound : Real) : Prop :=
  entrySupNorm (quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p) ≤
    bound

/-- Mean part of the `ω₁ = ω₃ ≠ ω₂` quadratic contribution after expanding
`ξ_{ω₁}^2 = (1 - 2p)ξ_{ω₁} + p(1-p)`. -/
noncomputable def quadraticNeumannMiddleIndexDistinctMeanContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        if w1 = w2 then 0 else
          ((1 - p) *
            centeredIndicator Omega p w2.1 w2.2 *
              signMatrix S w1.1 w1.2 *
                tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
                  tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Random coefficient `H_{ω₁}` for the mean part of the
`ω₁ = ω₃ ≠ ω₂` quadratic contribution after the `ξ_{ω₁}²` expansion. -/
noncomputable def quadraticMiddleIndexDistinctMeanCoefficient
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) (w1 : Fin n1 × Fin n2) : Real :=
  p⁻¹ *
    ∑ w2 : Fin n1 × Fin n2,
      if w2 = w1 then 0 else
        centeredIndicator Omega p w2.1 w2.2 *
          tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
            tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2

/-- Uniform sup-norm bound for the random coefficients in the mean part of the
`ω₁ = ω₃ ≠ ω₂` quadratic contribution. -/
def QuadraticMiddleIndexDistinctMeanCoefficientBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p bound : Real) : Prop :=
  ∀ w1 : Fin n1 × Fin n2,
    |quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1| ≤ bound

/-- Quadratic Neumann contribution with `ω₁ = ω₂ ≠ ω₃` in (6.20). -/
noncomputable def quadraticNeumannLastIndexDistinctContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w3 : Fin n1 × Fin n2,
        if w1 = w3 then 0 else
          ((centeredIndicator Omega p w1.1 w1.2) ^ 2 *
            centeredIndicator Omega p w3.1 w3.2 *
              signMatrix S w3.1 w3.2 *
                tangentCoordinateKernel S w3.1 w3.2 w1.1 w1.2 *
                  tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Centered random part of the `ω₁ = ω₂ ≠ ω₃` quadratic contribution after
expanding `ξ_{ω₁}^2 = (1 - 2p)ξ_{ω₁} + p(1-p)`. -/
noncomputable def quadraticNeumannLastIndexDistinctCenteredContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w3 : Fin n1 × Fin n2,
        if w1 = w3 then 0 else
          ((1 - 2 * p) *
            centeredIndicator Omega p w1.1 w1.2 *
              centeredIndicator Omega p w3.1 w3.2 *
                signMatrix S w3.1 w3.2 *
                  tangentCoordinateKernel S w3.1 w3.2 w1.1 w1.2 *
                    tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Conditional coefficient matrix for the two-copy decoupled centered part of
the `ω₁ = ω₂ ≠ ω₃` quadratic contribution.  It is the off-diagonal response
operator applied to the centered sampling fluctuation of the sign matrix. -/
noncomputable def quadraticLastIndexDistinctCenteredCoefficientMatrix
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega3 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ *
      ∑ w3 : Fin n1 × Fin n2,
        if w3 = (i, j) then 0 else
          centeredIndicator Omega3 p w3.1 w3.2 *
            signMatrix S w3.1 w3.2 *
              tangentCoordinateKernel S w3.1 w3.2 i j *
                tangentCoordinateKernel S i j i j

/-- Two-copy decoupled model for the centered part of the
`ω₁ = ω₂ ≠ ω₃` quadratic contribution. -/
noncomputable def quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega1 Omega3 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w3 : Fin n1 × Fin n2,
        if w1 = w3 then 0 else
          ((1 - 2 * p) *
            centeredIndicator Omega1 p w1.1 w1.2 *
              centeredIndicator Omega3 p w3.1 w3.2 *
                signMatrix S w3.1 w3.2 *
                  tangentCoordinateKernel S w3.1 w3.2 w1.1 w1.2 *
                    tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Uniform entrywise bound for the conditional coefficient matrix in the
two-copy decoupled centered `ω₁ = ω₂ ≠ ω₃` quadratic term. -/
def QuadraticLastIndexDistinctCenteredCoefficientBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega3 : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p bound : Real) : Prop :=
  entrySupNorm (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S p) ≤
    bound

/-- Mean part of the `ω₁ = ω₂ ≠ ω₃` quadratic contribution after expanding
`ξ_{ω₁}^2 = (1 - 2p)ξ_{ω₁} + p(1-p)`. -/
noncomputable def quadraticNeumannLastIndexDistinctMeanContribution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 2 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w3 : Fin n1 × Fin n2,
        if w1 = w3 then 0 else
          ((1 - p) *
            centeredIndicator Omega p w3.1 w3.2 *
              signMatrix S w3.1 w3.2 *
                tangentCoordinateKernel S w3.1 w3.2 w1.1 w1.2 *
                  tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2

/-- Off-diagonal response operator for the mean part of the
`ω₁ = ω₂ ≠ ω₃` quadratic contribution.  Applied to
`p^{-1}(P_Ω - pI)(p^{-1}E)`, this is exactly the fourth term in (6.20) after
the `ξ_{ω₁}²` expansion, with the diagonal `ω₁ = ω₃` terms removed. -/
noncomputable def quadraticLastIndexDistinctOffDiagonalResponse
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  ∑ w1 : Fin n1 × Fin n2,
    ∑ w3 : Fin n1 × Fin n2,
      if w1 = w3 then 0 else
        (X w3.1 w3.2 *
          tangentCoordinateKernel S w3.1 w3.2 w1.1 w1.2 *
            tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2) •
          coordinateMatrix w1.1 w1.2

/-- Quadratic Neumann contribution with `ω₁`, `ω₂`, and `ω₃` pairwise
distinct in (6.20). -/
noncomputable def quadraticNeumannAllDistinctContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        ∑ w3 : Fin n1 × Fin n2,
          if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then 0 else
            (centeredIndicator Omega p w1.1 w1.2 *
              centeredIndicator Omega p w2.1 w2.2 *
                centeredIndicator Omega p w3.1 w3.2 *
                  signMatrix S w3.1 w3.2 *
                    tangentCoordinateKernel S w3.1 w3.2 w2.1 w2.2 *
                      tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
              coordinateMatrix w1.1 w1.2

/-- Decoupled model for the all-distinct quadratic contribution: three
independent Bernoulli observation sets provide the three centered factors.
This is the object controlled after applying the triple decoupling inequality. -/
noncomputable def quadraticNeumannAllDistinctDecoupledContribution {n1 n2 r : Nat}
    {M : RealMatrix n1 n2}
    (Omega1 Omega2 Omega3 : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : RealMatrix n1 n2 :=
  (p⁻¹) ^ 3 •
    ∑ w1 : Fin n1 × Fin n2,
      ∑ w2 : Fin n1 × Fin n2,
        ∑ w3 : Fin n1 × Fin n2,
          if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then 0 else
            (centeredIndicator Omega1 p w1.1 w1.2 *
              centeredIndicator Omega2 p w2.1 w2.2 *
                centeredIndicator Omega3 p w3.1 w3.2 *
                  signMatrix S w3.1 w3.2 *
                    tangentCoordinateKernel S w3.1 w3.2 w2.1 w2.2 *
                      tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
              coordinateMatrix w1.1 w1.2

/-- Inner scalar coefficient `G_{ω₂}` in the triple-decoupled all-distinct
quadratic term, with the excluded outer index `ω₁` kept explicit. -/
noncomputable def quadraticAllDistinctInnerCoefficient {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega3 : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) (w1 w2 : Fin n1 × Fin n2) : Real :=
  p⁻¹ *
    ∑ w3 : Fin n1 × Fin n2,
      if w3 = w1 ∨ w3 = w2 then 0 else
        centeredIndicator Omega3 p w3.1 w3.2 *
          signMatrix S w3.1 w3.2 *
            tangentCoordinateKernel S w3.1 w3.2 w2.1 w2.2

/-- Deterministic base matrix whose scalar centered sampling fluctuation is the
inner `G_{ω₂}` coefficient in the triple-decoupled all-distinct term. -/
noncomputable def quadraticAllDistinctInnerBaseMatrix {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r)
    (w1 w2 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  fun i j =>
    if (i, j) = w1 ∨ (i, j) = w2 then 0 else
      signMatrix S i j * tangentCoordinateKernel S i j w2.1 w2.2

/-- Middle scalar coefficient `H_{ω₁}` in the triple-decoupled all-distinct
quadratic term after summing the `ω₂` layer. -/
noncomputable def quadraticAllDistinctMiddleCoefficient {n1 n2 r : Nat}
    {M : RealMatrix n1 n2}
    (Omega2 Omega3 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) (w1 : Fin n1 × Fin n2) : Real :=
  p⁻¹ *
    ∑ w2 : Fin n1 × Fin n2,
      if w2 = w1 then 0 else
        centeredIndicator Omega2 p w2.1 w2.2 *
          quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2 *
            tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2

/-- Conditional base matrix whose scalar centered sampling fluctuation over the
second independent sample is the middle coefficient `H_{ω₁}` in the
triple-decoupled all-distinct quadratic term. -/
noncomputable def quadraticAllDistinctMiddleBaseMatrix {n1 n2 r : Nat}
    {M : RealMatrix n1 n2}
    (Omega3 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) (w1 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  fun i j =>
    if (i, j) = w1 then 0 else
      quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j) *
        tangentCoordinateKernel S i j w1.1 w1.2

/-- Uniform sup-norm bound for the inner `G_{ω₂}` coefficients in the
triple-decoupled all-distinct quadratic term. -/
def QuadraticAllDistinctInnerCoefficientBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega3 : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p bound : Real) : Prop :=
  ∀ w1 w2 : Fin n1 × Fin n2,
    |quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2| ≤ bound

/-- Uniform sup-norm bound for the middle `H_{ω₁}` coefficients in the
triple-decoupled all-distinct quadratic term. -/
def QuadraticAllDistinctMiddleCoefficientBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2}
    (Omega2 Omega3 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p bound : Real) : Prop :=
  ∀ w1 : Fin n1 × Fin n2,
    |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤ bound

/-- Outer coefficient matrix in the triple-decoupled all-distinct quadratic
term.  Applying the centered sampling fluctuation in the first independent
sample to this matrix recovers the decoupled contribution. -/
noncomputable def quadraticAllDistinctOuterCoefficientMatrix {n1 n2 r : Nat}
    {M : RealMatrix n1 n2}
    (Omega2 Omega3 : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : Real) : RealMatrix n1 n2 :=
  fun i j => quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p (i, j)

/-- Product Bernoulli probability for a three-set event in the decoupled model. -/
noncomputable def bernoulliTripleEventProb {n1 n2 : Nat} (p : Real)
    (Event :
      Finset (Fin n1 × Fin n2) →
      Finset (Fin n1 × Fin n2) →
      Finset (Fin n1 × Fin n2) → Prop) : Real :=
  ∑ Omega1 : Finset (Fin n1 × Fin n2),
    ∑ Omega2 : Finset (Fin n1 × Fin n2),
      ∑ Omega3 : Finset (Fin n1 × Fin n2),
        bernoulliObservationWeight p Omega1 *
          bernoulliObservationWeight p Omega2 *
            bernoulliObservationWeight p Omega3 *
              if Event Omega1 Omega2 Omega3 then 1 else 0

/-- Product Bernoulli probability for a two-set event in a decoupled model. -/
noncomputable def bernoulliPairEventProb {n1 n2 : Nat} (p : Real)
    (Event :
      Finset (Fin n1 × Fin n2) →
      Finset (Fin n1 × Fin n2) → Prop) : Real :=
  ∑ Omega1 : Finset (Fin n1 × Fin n2),
    ∑ Omega2 : Finset (Fin n1 × Fin n2),
      bernoulliObservationWeight p Omega1 *
        bernoulliObservationWeight p Omega2 *
          if Event Omega1 Omega2 then 1 else 0

/-- Spectral-norm bound for one Neumann certificate term. -/
def NeumannCertificateTermSpectralBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) (k : Nat) (bound : Real) : Prop :=
  spectralNorm (neumannCertificateTerm Omega S p k) ≤ bound

/-- Uniform spectral-norm bound for every finite partial sum of the Neumann
certificate tail starting at `k0`. -/
def NeumannCertificateTailSpectralBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) (k0 : Nat) (bound : Real) : Prop :=
  ∀ K : Nat, k0 ≤ K →
    spectralNorm
        (Finset.sum (Finset.Icc k0 K)
          (fun k => neumannCertificateTerm Omega S p k)) ≤ bound

/-- Frobenius contraction bound for the Neumann error operator on the tangent
space.  This is the deterministic form of the Theorem 4.1 input used in the
geometric-series proof of Lemma 4.8. -/
def NeumannErrorOperatorFrobeniusContraction {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p rho : Real) : Prop :=
  ∀ X : RealMatrix n1 n2,
    tangentProjection S X = X →
      frobeniusNorm (neumannErrorOperator Omega S p X) ≤
        rho * frobeniusNorm X

/-- Frobenius bound for applying the sampling projection to tangent-space
matrices, matching the Corollary 4.3 step in Lemma 4.8. -/
def SampledTangentOperatorFrobeniusBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (bound : Real) : Prop :=
  ∀ X : RealMatrix n1 n2,
    tangentProjection S X = X →
      frobeniusNorm (samplingProjection Omega X) ≤ bound * frobeniusNorm X

/-- Frobenius control of a finite Neumann-iterate tail before the sampling
operator and normal projection are applied. -/
def NeumannIterateTailFrobeniusBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) (k0 : Nat) (bound : Real) : Prop :=
  ∀ K : Nat, k0 ≤ K →
    frobeniusNorm
        (Finset.sum (Finset.Icc k0 K)
          (fun k => neumannIterate Omega S p k)) ≤ bound

/-- The explicit Lemma 4.8 remainder bound with `k0 = 3`, before it is
absorbed into the fixed `1/2` threshold used by the certificate proof. -/
noncomputable def neumannRemainderFormulaBound
    (Ctail β μ0 : Real) (n r m : Nat) : Real :=
  Ctail * Real.sqrt (((n : Real) ^ 2 * (r : Real)) / (m : Real)) *
    Real.rpow
      ((μ0 * (n : Real) * (r : Real) * (β * Real.log (n : Real))) /
        (m : Real))
      ((3 : Real) / 2)

end MatrixCompletion


