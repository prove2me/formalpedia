-- Prove2me | Theorems.Thm_lean_workbook_plus_44491
-- name    : lean_workbook_plus_44491
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/430a7051-caae-4473-8565-e2078595bf60
-- statement:
--   Here is a simple solution: Call the legs of the spider $a,b,c,d,e,f,g,h$ . Then, consider all arrangements of $aabbccddeeffgghh$ . In every arrangement, the first letter in a pair represents a sock and the second letter in a pair represents a shoe. Thus, there is a one-to-one correspondence with the number of ways to wear socks and shoes and the number of arrangements of $aabbccddeeffgghh$ . This is easy, just $\frac{16!}{(2!)^8}$ because there are $16$ letters and $8$ pairs of $2$ identical letters.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44491 :
  16! / (2!^8) = 5765760   :=  by sorry
