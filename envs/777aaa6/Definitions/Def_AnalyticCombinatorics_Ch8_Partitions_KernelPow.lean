-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelPow
-- name    : AnalyticCombinatorics_Ch8_Partitions_KernelPow
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T13:51:59.055203+00:00
-- url     : https://prove2.me/theorems/c2cbabd1-5613-42df-82cb-1c8ef57b97b4
-- title:
--   Kernel Pow
-- statement:
--   For real-valued matrices P,Q on natural indices, KComp P Q n k sums P n j·Q j k over j<n. KPow 0 P is the identity matrix, and KPow (L+1) P = KComp P (KPow L P). These are powers of the strictly lower-triangular truncation of P; all composition sums are finite.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/KernelPow.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Fact B via Doeblin (File B): kernel composition and powers

Composition `KComp P Q n k = ∑_{j<n} P n j · Q j k` and the `L`-fold power `KPow L P` of a predecessor
kernel.  Proves nonnegativity and (strict) predecessor-support preservation by induction on `L` — the
algebraic foundation for the finite-time Doeblin overlap and the `P^L`-harmonic identity for `hitVal`.
The identity kernel `KPow 0 = δ(k=n)` forces the *strict* support `n < k → · = 0`.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Kernel composition over predecessors: `(KComp P Q) n k = ∑_{j < n} P n j · Q j k`. -/
def KComp (P Q : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun n k => ∑ j ∈ Finset.range n, P n j * Q j k

/-- `L`-fold kernel power; `KPow 0` is the identity kernel `δ(k=n)`. -/
def KPow : ℕ → (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | 0, _ => fun n k => if k = n then 1 else 0
  | L + 1, P => KComp P (KPow L P)

end AnalyticCombinatorics.Ch8.Partitions.Erdos


