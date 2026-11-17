-- Prove2me | Theorems.Thm_XiPairingPublished_upper_zero_translation
-- name    : XiPairingPublished.upper_zero_translation
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T11:18:49.58621+00:00
-- url     : https://prove2.me/theorems/3999cd88-d9b9-47f6-ba67-eb329a3ed931
-- title:
--   Real translation preserves upper zero occurrences and multiplicities
-- statement:
--   Let f be a complex function and c a real number. Translating the argument by c gives a bijection between upper-half-plane zeros counted by their analytic orders, preserving multiplicity labels and sending a zero z to z+c. Fibres with analytic order zero are empty.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno; shifted_index.lean. Standard analytic-order translation lemma from Mathlib. No novelty claim.

import Mathlib
namespace XiPairingPublished
end XiPairingPublished

theorem XiPairingPublished.upper_zero_translation (f : ℂ → ℂ) (c : ℝ) :
    let U := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt (fun w => f (w+(c : ℂ))) z.val)
    let Z := (z : {z : ℂ // f z = 0 ∧ 0 < z.im}) × Fin (analyticOrderNatAt f z.val)
    ∃ e : U ≃ Z, ∀ p, (e p).1.val = p.1.val+c ∧ (e p).2.val = p.2.val := by sorry
