-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_lemma_4_17
-- name    : ZeroFreeRRG.Hardcore.potts_lemma_4_17
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:04:42.528365+00:00
-- url     : https://prove2.me/theorems/bdc56d0f-6ad0-483f-9649-d1c0f5729335
-- title:
--   Potts part of the variational strictness lemma
-- statement:
--   Fix $d\ge3$ and $q\ge2$. For the antiferromagnetic Potts model at $0<\beta<1$, interior variational replica symmetry implies both strict uniqueness of the Bethe maximizer (Condition 1) and strict Kesten–Stigum stability (Condition 2). Variational replica symmetry is preserved when $\beta$ increases in $[0,1)$. This is the complete Potts part of Lemma 4.17, including monotonicity from the coloring endpoint.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Lemma 4.17, printed pp. 29–31.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore
theorem potts_lemma_4_17 (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ β : ℝ, 0 < β → β < 1 → InteriorVariationalRS (.potts q) d β →
        Condition1 (.potts q) d β ∧ Condition2 (.potts q) d β) ∧
    (∀ β' β : ℝ, 0 ≤ β' → β' < β → β < 1 →
        VariationalRS (.potts q) d β' → VariationalRS (.potts q) d β) := by sorry
end ZeroFreeRRG.Hardcore
