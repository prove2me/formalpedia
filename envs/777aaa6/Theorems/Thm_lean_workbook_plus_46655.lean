-- Prove2me | Theorems.Thm_lean_workbook_plus_46655
-- name    : lean_workbook_plus_46655
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/84824204-7246-4505-9568-29c3eae020b1
-- statement:
--   Rest of the solutionBy Euler's Totient Theorem, we know that $2^{\phi(625)}\equiv 2^{500}\equiv 1\mod{625}$ . So, $2^{27653}\equiv 2^{153}\mod{625}$ . We can bash the rest of this out. $$2^{153}=2^{128}\cdot 2^{16}\cdot 2^8\cdot 2^1\equiv 206\cdot 536\cdot 256\cdot 2\equiv 492\mod{625}$$ So, $2^{27853}-1\equiv 491\mod{625}$ . Now we can use CRT. Let $N=625a+491$ for some integer $a$ . $$625a+491\equiv 15\mod{16}$$ $$\implies a\equiv 4\mod{16}$$ Let $a=16b+4$ for some integer $b$ . We have $$N=625a+491=625(16b+4)+491=10000b+2991$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46655 :
  (2^27653 - 1) % 625 = 491   :=  by sorry
