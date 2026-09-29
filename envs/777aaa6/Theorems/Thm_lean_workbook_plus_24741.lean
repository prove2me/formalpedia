-- Prove2me | Theorems.Thm_lean_workbook_plus_24741
-- name    : lean_workbook_plus_24741
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b9f5045b-4fbc-4256-9314-881b9f2bb713
-- statement:
--   Perhaps a more clear explanation: \nBy Euler's totient theorem, \n $ a^{\phi(n)}\equiv 1\pmod n$ \nif $ \text{gcd}(a,n)=1$ , where $ \phi(n)=n\prod_{p|n}\left(1-\frac{1}{p}\right),$ where $ p$ is prime. \n\n $ \phi(9)=9\cdot\frac{2}{3}=6,$ and $ 2$ is coprime to $ 9$ , so $ 2^{6}\equiv 1\pmod 9.$ However, we want values of, say, $ x$ , such that $ 2^{x}\equiv -1\equiv 8\pmod 9$ . $ 8$ is a power of $ 2$ , $ 2^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24741 :
  IsLeast {x : ℕ | 2^x ≡ 8 [MOD 9]} 3   :=  by sorry
