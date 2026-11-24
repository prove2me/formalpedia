-- Prove2me | Theorems.Thm_erdos_1219
-- name    : erdos_1219
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:54:17.318575+00:00
-- url     : https://prove2.me/theorems/0dc4d6fa-82c9-49c1-901f-5c7d3b754eb0
-- title:
--   erdos 1219: erdos 1219
-- statement:
--   **Erdős problem #1219.**  Let `(n_k)` be an increasing sequence of natural numbers such that
--   `2 ^ ℵ_{n_k}` is strictly increasing and `2 ^ ℵ_{n_0} > ℵ_ω`.  Then
--   `Σ_k 2 ^ ℵ_{n_k} → (ℵ_ω)²₂`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Solution.lean#L22-L26
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Solution.lean#L22-L26

import Definitions.Def_Erdos1219_Main
import Definitions.Def_Erdos1219_Solution
import Theorems.Thm_Erdos1219_erdos_1219

set_option autoImplicit false
open Cardinal Ordinal
universe u

theorem erdos_1219 (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    Erdos1219.PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω) := by sorry
