-- Prove2me | Theorems.Thm_Couret_Certificate_state_row_8
-- name    : Couret.Certificate.state_row_8
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:24:07.214673+00:00
-- url     : https://prove2.me/theorems/e48f1c07-1542-4ff1-ab60-4b48bb170e73
-- title:
--   Automaton certificate state row 8
-- statement:
--   For the fixed table state $i=8$ in the 147-state, eight-letter automaton, every raw next-state index is below 147 and its raw quotient class is below 101. The stored encoding locates back to $i$ and is empty exactly when $i=0$. Every letter step is semantically valid; the stored reachability word reaches $i$ from zero and is nonempty if $i\ne0$. The stored output equals both the encoded output-mask count and the semantic presence count. Finally the quotient map $q$ respects transitions and output:
--
--   $$q(\delta(i,g))=\bar\delta(q(i),g),\qquad O(i)=\bar O(q(i))\qquad(g\text{ any of the eight letters}).$$
--
--   This records the full state-row certificate, including bounds, semantics, reachability and quotient compatibility.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/StateCheck01.lean, lines 8–8; source file SHA-256 401113f4b26f2f24037156a3dc068ae0619cd59129dca2c7063c48adf382e11c; theorem Couret.Certificate.state_row_8

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem state_row_8 : StateFacts 8 := by sorry







end Certificate
end Couret
