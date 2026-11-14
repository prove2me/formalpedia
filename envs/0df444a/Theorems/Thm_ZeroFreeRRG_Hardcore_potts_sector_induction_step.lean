-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_sector_induction_step
-- name    : ZeroFreeRRG.Hardcore.potts_sector_induction_step
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:53:22.382389+00:00
-- url     : https://prove2.me/theorems/14fae1cf-620d-445f-9979-2bc7fb084f58
-- title:
--   A sector-based induction step for restricted Potts sums
-- statement:
--   Fix a nonempty color set and a partial vertex coloring. If the weighted Potts sums obtained by assigning each color to one additional vertex are nonzero and their normalized phases all lie within distance $1/2$ of one unit complex number, then the original restricted partition sum is nonzero.
-- source:
--   Auxiliary induction step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_sector_induction_step {V : Type} [Fintype V] (q : ℕ) (hq : 1 ≤ q) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (S : Finset V) (τ : V → Fin q) (v : V) (hv : v ∉ S) (u : ℂ) (hu : ‖u‖ = 1)
    (hn : ∀ c : Fin q, pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) ≠ 0)
    (hclose : ∀ c : Fin q, ‖u - (pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c)) /
      (‖pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c)‖ : ℂ)‖ ≤ 1/2) :
    pottsWeightedPartial q G W hW S τ ≠ 0 := by sorry
