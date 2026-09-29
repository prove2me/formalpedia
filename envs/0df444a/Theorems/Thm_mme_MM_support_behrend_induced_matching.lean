-- Prove2me | Theorems.Thm_mme_MM_support_behrend_induced_matching
-- name    : mme_MM_support_behrend_induced_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:29:21.592827+00:00
-- url     : https://prove2.me/theorems/b4897f87-1318-4ba0-86b0-298e9fc3d944
-- title:
--   An explicit Behrend induced matching in matrix-multiplication support
-- statement:
--   For every positive integer \(H\), there is a finite set \(E\subseteq[H]^3\) such that each of the three pair-address maps
--   \[
--   (i,j,k)\longmapsto(i,j),\qquad
--   (i,j,k)\longmapsto(j,k),\qquad
--   (i,j,k)\longmapsto(k,i)
--   \]
--   is injective on \(E\).  Moreover, if an \(X\)-pair from one member, a \(Y\)-pair from a second member, and a \(Z\)-pair from a third member fit together as a matrix-multiplication support triple, then all three members are equal.  Thus \(E\) is an induced matching in the support hypergraph of \(\langle H,H,H\rangle\).  Quantitatively,
--   \[
--   H^2\exp\!\left(-100\sqrt{\log(H+1)}\right)\le |E|.
--   \]
--
--   The deliberately loose constant \(100\) permits a uniform all-\(H>0\) statement while retaining the \(H^{2-o(1)}\) rate supplied by an explicit Behrend three-term-progression-free set.
-- source:
--   The Salem--Spencer/Behrend induced-matching construction used in the C-tensor method of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990). The explicit finite density input is Prove2Me theorem mme_behrend_explicit_threeAP_free, cb45e6ba-b86a-4119-a08e-f162c8fbc86b.

import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open Real

theorem mme_MM_support_behrend_induced_matching
    (H : ℕ) (hH : 0 < H) :
    ∃ E : Finset (Fin H × Fin H × Fin H),
      Function.Injective
        (fun e : E => (e.1.1, e.1.2.1)) ∧
      Function.Injective
        (fun e : E => (e.1.2.1, e.1.2.2)) ∧
      Function.Injective
        (fun e : E => (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E,
        x.1.2.1 = y.1.2.1 →
        y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 →
        x = y ∧ y = z) ∧
      ((H : ℝ) ^ 2) *
          Real.exp (-100 *
            Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        (E.card : ℝ) := by sorry
