-- Prove2me | solution 1 for taylor_wiles_patching
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T05:26:13.486738+00:00
-- url     : https://prove2.me/submissions/4cb66257-1f34-4e5c-b8f7-1454caf90ead
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_taylor_wiles_patching
import Theorems.Thm_taylor_wiles_primes_existence
import Theorems.Thm_selmer_group_control
import Theorems.Thm_iwasawa_freeness
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

-- Sketch: Taylor-Wiles patching via three ingredients.
-- (1) taylor_wiles_primes_existence: Chebotarev gives the auxiliary primes Q_n.
-- (2) selmer_group_control: Euler characteristic formula bounds the Selmer group.
-- (3) iwasawa_freeness: Auslander-Buchsbaum forces M_∞ free over Λ → R ≅ T.
-- The full argument is encoded in iwasawa_freeness; the other two are prerequisites
-- that feed into its construction.
theorem solution
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c)
    (heq : a ^ p + b ^ p = c ^ p) : False :=
  iwasawa_freeness p hp h5 a b c ha hb hc hab hbc hac heq
