-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_ideal_identity
-- name    : ZamirInversion581.Mult.ideal_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:20.2356+00:00
-- url     : https://prove2.me/theorems/a2516d8c-eb6b-4e2e-a251-ce3b01f856da
-- title:
--   §2.1 ideal-execution identity — complementary Schur complements recover $BC$
-- statement:
--   Let $B,C,R,A,A'$ be $n\times n$ matrices over a field $F$, and let $S=A-BRC$, $S'=A'-B(I-R)C$. Assume $R$, $I-R$, $S$, $S'$ are invertible (the event $E$). Let
--
--   $$
--   M=\begin{pmatrix}A&B\\C&R^{-1}\end{pmatrix},\qquad M'=\begin{pmatrix}A'&B\\C&(I-R)^{-1}\end{pmatrix},
--   $$
--
--   and let $H,H'$ be the upper-left $n\times n$ blocks of $M^{-1},M'^{-1}$. Then $H=S^{-1}$, $H'=S'^{-1}$, and
--
--   $$
--   A+A'-H^{-1}-H'^{-1}=BC.
--   $$
--
--   So six inversions and matrix additions, with no multiplication performed by the procedure itself, compute the product $BC$. The identity is the algebraic core of the reduction from high-success inversion.
--
--   Differences from the source:
--   - generalization: a finite field F_q and n ≥ 3 → any field F and any n; reason: the identity is algebraic and uses neither assumption; it specializes to the source's case
--   - encoding: "whenever the six oracle calls are correct, Q = ..." → H, H′ are the true blocks and the conclusion concerns them; reason: correct calls return exactly these matrices, so this is the page's Q in the ideal execution
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.7, §2.1 ideal-execution identity display; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Inverter
import Definitions.Def_ZamirInversion581_Mult_SchurExecution

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- §2.1 ideal-execution identity, p.7. Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf
SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917. On the event `E`, the upper
left blocks `H`, `H′` of `M⁻¹`, `M′⁻¹` are `S⁻¹`, `(S′)⁻¹`, and `A + A′ − H⁻¹ − (H′)⁻¹ = BC`. The block
matrices themselves are used, so the Schur complement formula is derived, not assumed. -/
theorem ideal_identity {F : Type*} [Field F] {n : ℕ} (B C R A A' : Matrix (Fin n) (Fin n) F)
    (hE : EventE B C R A A') :
    upperLeft (idealM B C R A)⁻¹ = (schurS B C R A)⁻¹ ∧
    upperLeft (idealM' B C R A')⁻¹ = (schurS' B C R A')⁻¹ ∧
    A + A' - (upperLeft (idealM B C R A)⁻¹)⁻¹ - (upperLeft (idealM' B C R A')⁻¹)⁻¹ = B * C := by sorry

end ZamirInversion581.Mult
